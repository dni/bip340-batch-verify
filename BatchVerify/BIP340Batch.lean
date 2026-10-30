import BatchVerify.BIP340Props
import BatchVerify.Secp256k1
import VCVio.OracleComp.QueryTracking.CachingOracle
import VCVio.OracleComp.EvalDist.Measure
import VCVio.EvalDist.ProbabilityBounds
import VCVio.ProgramLogic.Unary.HoareTriple

/-!
# BIP340 batch verification with hash-derived coefficients

BIP340 batch verification checks `Σ aᵢ·(sᵢ·G - Rᵢ - eᵢ·Pᵢ) = 0` with `a₁ = 1`
and random coefficients `a₂, …, aᵤ`. `batchVerify_sound_bits` shows that one
uniformly random `b`-bit coefficient catches an invalid batch except with
probability `2^-b`. In practice the coefficients are not independent random
values: they are derived deterministically from the batch, and the attacker
chooses the batch. Here they come from a random oracle.

We model two derivations, both as a random oracle with `b`-bit answers:

* **whole-batch derivation**, as in the BIP340 text: coefficient `aᵢ` (for
  `i ≥ 2`) is the hash of the whole batch together with `i`;
* **incremental derivation**, as in libsecp256k1's batch verification API:
  `aᵢ` is the hash of the first `i` entries of the batch, so it is known as
  soon as those entries are, and the attacker may choose the later entries
  after seeing it.

`batchGame`: the attacker, with access to the random oracle, outputs a batch;
the verifier derives the coefficients from the same oracle.
`batch_indexed_sound` and `batch_incremental_sound`: if the attacker makes at
most `q` oracle queries, then the batch passes while containing an invalid
signature with probability at most `(q + 1)/2^b`, however large the batch.
This holds for every choice of the challenge hash. The `secp256k1_…` versions
take `b = 128`.

The proofs charge each win to a random oracle answer, through the bound
`wp_badVal_le` on the expected value of a bad event plus a potential. The
attacker's queries cost `1/2^b` each. The verifier's queries cost `1/2^b`
together, since only one of its answers can complete the batch it checks.

For whole-batch derivation one fresh answer can complete at most one batch,
which gives the bound directly. The incremental case needs more care.

For incremental derivation, let `j` be the last invalid entry of the winning
batch. Then the prefix `t` of the first `j` entries already passes, and its
equation `Σ aᵢ·defectᵢ = 0` involves only coefficients of prefixes of `t`.
Whichever of those (with a nonzero defect) is answered last must hit the one
value that solves the equation. One fresh answer can complete many prefixes
`t` at once (all cached extensions of the queried prefix), so a single query
can have several bad values. Each such `t` was already cached, though, and is
completed only once. The potential counts the cached prefixes that are not
complete yet. While the verifier checks a batch, the bad event ignores the
proper prefixes of that `t` (its `target`): a coefficient may be `0`, so such
a prefix can pass without the batch passing.
-/

open OracleSpec OracleComp OracleComp.ProgramLogic
open scoped ENNReal OracleSpec.PrimitiveQuery

namespace BatchVerify.BIP340Batch

/-! ## A bad-event bound for random oracles -/

section BadEvent

variable {ι Y : Type} [DecidableEq ι] [Fintype Y] [UniformAnswerMeasure (ι →ₒ Y)]

open scoped Classical in
/-- The score of a cache: `1` if it is bad, and otherwise its potential as a
probability, `Φ/|Y|` capped at `1`. -/
noncomputable def badVal (Bad : (ι →ₒ Y).QueryCache → Prop) (Φ : (ι →ₒ Y).QueryCache → ℝ≥0∞)
    (c : (ι →ₒ Y).QueryCache) : ℝ≥0∞ :=
  if Bad c then 1 else min 1 (Φ c * (Fintype.card Y : ℝ≥0∞)⁻¹)

omit [DecidableEq ι] [UniformAnswerMeasure (ι →ₒ Y)] in
theorem badVal_le_one (Bad : (ι →ₒ Y).QueryCache → Prop) (Φ : (ι →ₒ Y).QueryCache → ℝ≥0∞)
    (c : (ι →ₒ Y).QueryCache) : badVal Bad Φ c ≤ 1 := by
  unfold badVal
  split_ifs
  · exact le_rfl
  · exact min_le_left _ _

omit [DecidableEq ι] [UniformAnswerMeasure (ι →ₒ Y)] in
theorem propInd_le_badVal (Bad : (ι →ₒ Y).QueryCache → Prop) (Φ : (ι →ₒ Y).QueryCache → ℝ≥0∞)
    (c : (ι →ₒ Y).QueryCache) : propInd (Bad c) ≤ badVal Bad Φ c := by
  unfold badVal propInd
  split_ifs <;> simp

/-- **Bad-event bound with a potential**, in expectation: run `oa` against a
lazily sampled random oracle and score the final cache with `badVal Bad Φ`.
Suppose that whenever the cache `c` is good and a query `t` allowed by `P` is
fresh, the answer makes the cache bad with probability at most `k/|Y|`, and the
potential afterwards is at most `Ψ`, where `k + Ψ ≤ w + Φ c`. If `oa` only makes
queries allowed by `P`, each costing `w` from a budget of `q`, then the
expected score grows by at most `q/|Y|`.

With `Φ = 0` and `w = k = 1` this is the usual "each fresh answer is bad with
probability `1/|Y|`". The potential lets one query be charged for several bad
values (`k > 1`) when earlier queries prepaid for them, and with `w = 0` a
phase of queries is paid for by the potential alone. Bounding the expected
score rather than the probability of a bad cache lets the potential left by
one phase start the next. -/
theorem wp_badVal_le (Bad : (ι →ₒ Y).QueryCache → Prop) (Φ : (ι →ₒ Y).QueryCache → ℝ≥0∞)
    (P : ι → Prop) (w : ℕ)
    (hstep : ∀ c t, P t → ¬ Bad c → c t = none → ∃ k Ψ : ℝ≥0∞,
      Pr{let u ← (liftM ((ι →ₒ Y).query t) : OracleComp (ι →ₒ Y) Y)}[Bad (c.cacheQuery t u)] ≤
        k * (Fintype.card Y : ℝ≥0∞)⁻¹ ∧
      (∀ u, Φ (c.cacheQuery t u) ≤ Ψ) ∧ k + Ψ ≤ w + Φ c)
    {α : Type} (oa : OracleComp (ι →ₒ Y) α) (q : ℕ)
    (hq : IsQueryBound oa q (fun t b => P t ∧ w ≤ b) (fun _ b => b - w))
    (c₀ : (ι →ₒ Y).QueryCache) :
    wp ((simulateQ (ι →ₒ Y).cachingOracle oa).run c₀) (fun z => badVal Bad Φ z.2) ≤
      q * (Fintype.card Y : ℝ≥0∞)⁻¹ + badVal Bad Φ c₀ := by
  induction oa using OracleComp.inductionOn generalizing q c₀ with
  | pure x =>
    rw [simulateQ_pure, StateT.run_pure, wp_pure]
    exact le_add_self
  | query_bind t mx ih =>
    rw [isQueryBound_query_bind_iff] at hq
    obtain ⟨⟨hP, hw⟩, hrest⟩ := hq
    rw [simulateQ_bind, cachingOracle.simulateQ_query, StateT.run_bind]
    cases hc : c₀ t with
    | some v =>
      rw [cachingOracle.run_some hc, pure_bind]
      refine (ih v (q - w) (hrest v) c₀).trans ?_
      gcongr
      exact_mod_cast Nat.sub_le q w
    | none =>
      rw [cachingOracle.run_none hc, bind_map_left, wp_bind]
      have hcard : ((q - w : ℕ) : ℝ≥0∞) + w = q := by exact_mod_cast Nat.sub_add_cancel hw
      refine (wp_le_const_add_of_support _ fun u _ => ih u (q - w) (hrest u) _).trans ?_
      -- one fresh answer
      have hone : wp (liftM ((ι →ₒ Y).query t) : OracleComp (ι →ₒ Y) Y)
          (fun u => badVal Bad Φ (c₀.cacheQuery t u)) ≤
            w * (Fintype.card Y : ℝ≥0∞)⁻¹ + badVal Bad Φ c₀ := by
        by_cases hb : Bad c₀
        · refine (wp_le_const_of_support _ fun u _ => badVal_le_one Bad Φ _).trans ?_
          rw [show badVal Bad Φ c₀ = 1 by simp [badVal, hb]]
          exact le_add_self
        obtain ⟨k, Ψ, hk, hΨ, hkΨ⟩ := hstep c₀ t hP hb hc
        have hle1 : wp (liftM ((ι →ₒ Y).query t) : OracleComp (ι →ₒ Y) Y)
            (fun u => badVal Bad Φ (c₀.cacheQuery t u)) ≤ 1 :=
          wp_le_const_of_support _ fun u _ => badVal_le_one Bad Φ _
        have hleΦ : wp (liftM ((ι →ₒ Y).query t) : OracleComp (ι →ₒ Y) Y)
            (fun u => badVal Bad Φ (c₀.cacheQuery t u)) ≤
              (w + Φ c₀) * (Fintype.card Y : ℝ≥0∞)⁻¹ := by
          calc _ ≤ wp (liftM ((ι →ₒ Y).query t) : OracleComp (ι →ₒ Y) Y)
                (fun u => propInd (Bad (c₀.cacheQuery t u)) +
                  Ψ * (Fintype.card Y : ℝ≥0∞)⁻¹) := by
                refine wp_mono _ fun u => ?_
                unfold badVal propInd
                split_ifs
                · exact le_add_right le_rfl
                · calc _ ≤ Φ (c₀.cacheQuery t u) * (Fintype.card Y : ℝ≥0∞)⁻¹ := min_le_right _ _
                    _ ≤ Ψ * (Fintype.card Y : ℝ≥0∞)⁻¹ := by gcongr; exact hΨ u
                    _ ≤ _ := le_add_self
            _ = Pr{let u ← (liftM ((ι →ₒ Y).query t) : OracleComp (ι →ₒ Y) Y)}[
                  Bad (c₀.cacheQuery t u)] + Ψ * (Fintype.card Y : ℝ≥0∞)⁻¹ := by
                rw [wp_add, prEvent_eq_wp_propInd]
                exact congrArg _ (wp_const _ _)
            _ ≤ k * (Fintype.card Y : ℝ≥0∞)⁻¹ + Ψ * (Fintype.card Y : ℝ≥0∞)⁻¹ := by gcongr
            _ ≤ _ := by rw [← add_mul]; gcongr
        rw [show badVal Bad Φ c₀ = min 1 (Φ c₀ * (Fintype.card Y : ℝ≥0∞)⁻¹) by
          simp [badVal, hb]]
        rcases le_total 1 (Φ c₀ * (Fintype.card Y : ℝ≥0∞)⁻¹) with h | h
        · rw [min_eq_left h]
          exact hle1.trans le_add_self
        · rw [min_eq_right h, ← add_mul]
          exact hleΦ
      calc _ ≤ ((q - w : ℕ) : ℝ≥0∞) * (Fintype.card Y : ℝ≥0∞)⁻¹ +
            (w * (Fintype.card Y : ℝ≥0∞)⁻¹ + badVal Bad Φ c₀) := by gcongr
        _ = _ := by rw [← add_assoc, ← add_mul, hcard]

omit [DecidableEq ι] [Fintype Y] [UniformAnswerMeasure (ι →ₒ Y)] in
/-- A total query bound charges `1` per query, with every query allowed. -/
theorem isQueryBound_of_total {α : Type} {oa : OracleComp (ι →ₒ Y) α} {q : ℕ}
    (h : IsTotalQueryBound oa q) :
    IsQueryBound oa q (fun _ b => True ∧ 1 ≤ b) (fun _ b => b - 1) :=
  (isQueryBound_congr (fun _ _ => ⟨fun h => ⟨trivial, h⟩, fun h => h.2⟩) fun _ _ => rfl).mp h

omit [DecidableEq ι] [Fintype Y] [UniformAnswerMeasure (ι →ₒ Y)] in
/-- Queries allowed by `P` can be charged `0` each. -/
theorem isQueryBound_of_allQueries {α : Type} {oa : OracleComp (ι →ₒ Y) α} {P : ι → Prop}
    (h : AllQueriesSatisfy oa P) :
    IsQueryBound oa 0 (fun t b => P t ∧ 0 ≤ b) (fun _ b => b - 0) := by
  induction oa using OracleComp.inductionOn with
  | pure _ => trivial
  | query_bind t mx ih =>
    rw [allQueriesSatisfy_query_bind_iff] at h
    rw [isQueryBound_query_bind_iff]
    exact ⟨⟨h.1, le_rfl⟩, fun u => ih u (h.2 u)⟩

end BadEvent

/-! ## Batches -/

open Curve BIP340 BIP340.Entry

deriving instance DecidableEq for BatchVerify.BIP340.Entry

section Batch

variable {n : ℕ} [Fact n.Prime] {E X M : Type} [AddCommGroup E] [DecidableEq E] [DecidableEq X]
  (C : Curve n E X) (challenge : X → X → M → ZMod n)

/-- Coefficients only matter at invalid signatures: changing the others keeps a
passing batch passing. -/
theorem batchVerify_congr (hord : PrimeOrder n E) {u : ℕ} (ent : Fin u → Entry n X M)
    {a a' : Fin u → ZMod n} (h : ∀ i, valid C challenge (ent i) = false → a i = a' i)
    (hv : batchVerify C challenge ent a = true) : batchVerify C challenge ent a' = true := by
  rw [batchVerify_iff C challenge hord] at hv ⊢
  refine ⟨hv.1, ?_⟩
  rw [← hv.2]
  refine Finset.sum_congr rfl fun i _ => ?_
  cases hi : valid C challenge (ent i)
  · rw [h i hi]
  · rw [((valid_iff C challenge _).mp hi).2.2, nsmul_zero, nsmul_zero]

/-- If every signature after position `j` is valid, a passing batch still
passes when cut after position `j`. -/
theorem batchVerify_take (hord : PrimeOrder n E) (L : List (Entry n X M)) {j : ℕ}
    (hj : j < L.length) (hafter : ∀ i : Fin L.length, j < i → valid C challenge (L.get i) = true)
    (a : ℕ → ZMod n) (hv : batchVerify C challenge L.get (fun i => a i) = true) :
    batchVerify C challenge (L.take (j + 1)).get (fun i => a i) = true := by
  have hlen : (L.take (j + 1)).length = j + 1 := by simp; omega
  rw [batchVerify_iff C challenge hord] at hv ⊢
  obtain ⟨hlift, hsum⟩ := hv
  refine ⟨fun i => ?_, ?_⟩
  · have hi : (i : ℕ) < L.length := by have := i.2; omega
    simpa [List.getElem_take] using hlift ⟨i, hi⟩
  · let f : ℕ → E := fun i =>
      if h : i < L.length then (a i).val • defect C challenge L[i] else 0
    have hL : ∀ i : Fin L.length, (a i).val • defect C challenge (L.get i) = f i :=
      fun i => by simp [f, i.2]
    have hT : ∀ i : Fin (L.take (j + 1)).length,
        (a i).val • defect C challenge ((L.take (j + 1)).get i) = f i := fun i => by
      have hi : (i : ℕ) < L.length := by have := i.2; omega
      simp [f, hi, List.getElem_take]
    rw [Finset.sum_congr rfl fun i _ => hL i, Fin.sum_univ_eq_sum_range f] at hsum
    rw [Finset.sum_congr rfl fun i _ => hT i, Fin.sum_univ_eq_sum_range f, hlen, ← hsum]
    refine Finset.sum_subset (Finset.range_subset_range.mpr (by omega)) fun i hi hi' => ?_
    simp only [Finset.mem_range] at hi hi'
    have hv := ((valid_iff C challenge _).mp (hafter ⟨i, hi⟩ (by change j < i; omega))).2.2
    simp only [List.get_eq_getElem] at hv
    simp [f, hi, hv]

/-- Batch verification of `L` with coefficients `as`. -/
def verifyList (L : List (Entry n X M)) (as : List (ZMod n)) : Bool :=
  batchVerify C challenge L.get (fun i => as.getD i 0)

/-- The attacker wins if its batch passes although it contains an invalid signature. -/
def Wins (z : List (Entry n X M) × List (ZMod n)) : Prop :=
  verifyList C challenge z.1 z.2 = true ∧
    ∃ i : Fin z.1.length, valid C challenge (z.1.get i) = false

end Batch

/-! ## Deriving the coefficients from a random oracle -/

section Derivation

variable {n : ℕ} {X M : Type} {K : Type} [DecidableEq K] (b : ℕ)
  (key : List (Entry n X M) → ℕ → K)

/-- A random oracle with `b`-bit answers on inputs of type `K`. -/
abbrev KeySpec (K : Type) (b : ℕ) := K →ₒ Fin (2 ^ b)

/-- The verifier's coefficient for position `i` (from `0`) of batch `L`: `1`
for the first signature (BIP340's `a₁ = 1`), otherwise the hash of `key L i`. -/
def coeffQuery (L : List (Entry n X M)) (i : ℕ) : OracleComp (KeySpec K b) (ZMod n) :=
  if i = 0 then pure 1
  else (fun h : Fin (2 ^ b) => ((h : ℕ) : ZMod n)) <$>
    (liftM ((KeySpec K b).query (key L i)) : OracleComp (KeySpec K b) (Fin (2 ^ b)))

/-- The batch verification game: the attacker `adv` outputs a batch, then the
verifier derives its coefficients from the same random oracle. -/
def batchGame (adv : OracleComp (KeySpec K b) (List (Entry n X M))) :
    OracleComp (KeySpec K b) (List (Entry n X M) × List (ZMod n)) := do
  let L ← adv
  let as ← (List.range L.length).mapM (coeffQuery b key L)
  return (L, as)

theorem coeffQuery_spec (L : List (Entry n X M)) (i : ℕ) (c : (KeySpec K b).QueryCache)
    (z : ZMod n × (KeySpec K b).QueryCache)
    (hz : z ∈ support ((simulateQ (KeySpec K b).cachingOracle (coeffQuery b key L i)).run c)) :
    (i = 0 → z.1 = 1) ∧
      (i ≠ 0 → ∃ h : Fin (2 ^ b), z.2 (key L i) = some h ∧ z.1 = ((h : ℕ) : ZMod n)) := by
  unfold coeffQuery at hz
  split_ifs at hz with hi
  · simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
    subst hz
    exact ⟨fun _ => rfl, fun h => absurd hi h⟩
  · rw [simulateQ_map, cachingOracle.simulateQ_query, StateT.run_map, support_map] at hz
    obtain ⟨⟨h, c'⟩, hmem, rfl⟩ := hz
    exact ⟨fun h0 => absurd h0 hi, fun _ => ⟨h, cachingOracle_query_caches _ _ _ _ hmem, rfl⟩⟩

theorem coeffs_spec (L : List (Entry n X M)) (is : List ℕ) (c : (KeySpec K b).QueryCache)
    (z : List (ZMod n) × (KeySpec K b).QueryCache)
    (hz : z ∈ support
      ((simulateQ (KeySpec K b).cachingOracle (is.mapM (coeffQuery b key L))).run c)) :
    ∀ k (hk : k < is.length), (is[k] = 0 → z.1.getD k 0 = 1) ∧
      (is[k] ≠ 0 → ∃ h : Fin (2 ^ b),
        z.2 (key L is[k]) = some h ∧ z.1.getD k 0 = ((h : ℕ) : ZMod n)) := by
  induction is generalizing c z with
  | nil => intro k hk; simp at hk
  | cons i is ih =>
    rw [List.mapM_cons, simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hz
    obtain ⟨⟨a, c₁⟩, h₁, hz⟩ := hz
    rw [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hz
    obtain ⟨⟨as, c₂⟩, h₂, hz⟩ := hz
    simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
    subst hz
    intro k hk
    cases k with
    | zero =>
      obtain ⟨hz0, hnz⟩ := coeffQuery_spec b key L i c _ h₁
      refine ⟨fun h => by simpa using hz0 h, fun h => ?_⟩
      obtain ⟨v, hv, ha⟩ := hnz (by simpa using h)
      have hle := simulateQ_cachingOracle_cache_le _ c₁ _ h₂
      exact ⟨v, by simpa using hle hv, by simpa using ha⟩
    | succ k =>
      simpa using ih c₁ (as, c₂) h₂ k (by simpa using hk)

/-- **What the verifier leaves in the cache**: coefficient `0` is `1`, and every
other coefficient `k` is the cached hash of `key L k`. -/
theorem game_spec (adv : OracleComp (KeySpec K b) (List (Entry n X M)))
    (L : List (Entry n X M)) (as : List (ZMod n)) (c : (KeySpec K b).QueryCache)
    (hz : ((L, as), c) ∈
      support ((simulateQ (KeySpec K b).cachingOracle (batchGame b key adv)).run ∅)) :
    (∀ k < L.length, k = 0 → as.getD k 0 = 1) ∧
      (∀ k < L.length, k ≠ 0 → ∃ h : Fin (2 ^ b),
        c (key L k) = some h ∧ as.getD k 0 = ((h : ℕ) : ZMod n)) := by
  unfold batchGame at hz
  rw [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hz
  obtain ⟨⟨L', c₁⟩, -, hz⟩ := hz
  rw [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hz
  obtain ⟨⟨as', c₂⟩, h₂, hz⟩ := hz
  simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff,
    Prod.mk.injEq] at hz
  obtain ⟨⟨rfl, rfl⟩, rfl⟩ := hz
  have hco := coeffs_spec b key L (List.range L.length) c₁ (as, c) h₂
  refine ⟨fun k hk h0 => by simpa using (hco k (by simpa using hk)).1 (by simpa using h0),
    fun k hk h0 => ?_⟩
  obtain ⟨h, hc, ha⟩ := (hco k (by simpa using hk)).2 (by simpa using h0)
  rw [List.getElem_range] at hc
  exact ⟨h, hc, by simpa using ha⟩

omit [DecidableEq K] in
/-- The verifier only queries keys of the batch it checks. -/
theorem coeffs_allQueries (L : List (Entry n X M)) (is : List ℕ) :
    AllQueriesSatisfy (is.mapM (coeffQuery b key L)) (fun t => ∃ i, t = key L i) := by
  induction is with
  | nil => exact allQueriesSatisfy_pure _ _
  | cons i is ih =>
    rw [List.mapM_cons]
    refine allQueriesSatisfy_bind ?_ fun _ =>
      allQueriesSatisfy_bind ih fun _ => allQueriesSatisfy_pure _ _
    unfold coeffQuery
    split_ifs
    · exact allQueriesSatisfy_pure _ _
    · rw [allQueriesSatisfy_def, isQueryBound_map_iff, isQueryBound_query_iff]
      exact ⟨i, rfl⟩

end Derivation

/-! ## Incremental derivation -/

section Incremental

variable {n : ℕ} [Fact n.Prime] {E X M : Type} [AddCommGroup E] [DecidableEq E] [DecidableEq X]
  [DecidableEq M] (C : Curve n E X) (challenge : X → X → M → ZMod n) (b : ℕ)

/-- Incremental derivation hashes the first `i + 1` entries. -/
def prefixKey (L : List (Entry n X M)) (i : ℕ) : List (Entry n X M) := L.take (i + 1)

/-- The random oracle of incremental derivation: a batch prefix ↦ a `b`-bit value. -/
abbrev PrefixSpec (n : ℕ) (X M : Type) (b : ℕ) := KeySpec (List (Entry n X M)) b

/-! ### Bookkeeping on the random oracle's cache -/

/-- The prefixes stored in cache `c`. -/
def cached (c : (PrefixSpec n X M b).QueryCache) (x : List (Entry n X M)) : Prop := c x ≠ none

/-- Batch `t` has length at least two and its last signature is invalid. -/
def Rel (t : List (Entry n X M)) : Prop :=
  ∃ h : 1 < t.length, valid C challenge (t.get ⟨t.length - 1, by omega⟩) = false

/-- Every prefix of `t` that determines the coefficient of an invalid
signature (other than the first) lies in `S`. -/
def Covers (S : List (Entry n X M) → Prop) (t : List (Entry n X M)) : Prop :=
  ∀ i : Fin t.length, (i : ℕ) ≠ 0 → valid C challenge (t.get i) = false → S (t.take (i + 1))

/-- The coefficients of batch `t` as recorded in cache `c`. -/
def cacheCoeff (c : (PrefixSpec n X M b).QueryCache) (t : List (Entry n X M))
    (i : Fin t.length) : ZMod n :=
  if (i : ℕ) = 0 then 1 else ((c (t.take (i + 1))).map fun h => ((h : ℕ) : ZMod n)).getD 0

/-- Batch `t` counts for the bad event: its last signature is invalid and `Ex`
does not exclude it. -/
def Counts (Ex : List (Entry n X M) → Prop) (t : List (Entry n X M)) : Prop :=
  Rel C challenge t ∧ ¬ Ex t

/-- The bad event: some batch that counts has all its relevant coefficients
in the cache, and passes with them. -/
def Bad (Ex : List (Entry n X M) → Prop) (c : (PrefixSpec n X M b).QueryCache) : Prop :=
  ∃ t, Counts C challenge Ex t ∧ Covers C challenge (cached b c) t ∧
    batchVerify C challenge t.get (cacheCoeff b c t) = true

/-- Batches in `S`, not in `Ex`, that are not covered by `S` yet. -/
def IncOf (Ex : List (Entry n X M) → Prop) (S : List (Entry n X M) → Prop) :
    Set (List (Entry n X M)) :=
  {t | Counts C challenge Ex t ∧ S t ∧ ¬ Covers C challenge S t}

/-- The potential: how many cached batches outside `Ex` still wait for a coefficient. -/
noncomputable def Φ (Ex : List (Entry n X M) → Prop) (c : (PrefixSpec n X M b).QueryCache) :
    ℝ≥0∞ :=
  ((IncOf C challenge Ex (cached b c)).encard : ℝ≥0∞)

omit [DecidableEq M] in
theorem bad_empty (Ex : List (Entry n X M) → Prop) : ¬ Bad C challenge b Ex ∅ := by
  rintro ⟨t, ⟨⟨h1, hlast⟩, -⟩, hcov, -⟩
  exact hcov ⟨t.length - 1, by omega⟩ (by change t.length - 1 ≠ 0; omega) hlast
    (by rw [Nat.sub_add_cancel (by omega), List.take_of_length_le le_rfl]; rfl)

omit [DecidableEq M] in
theorem Φ_empty (Ex : List (Entry n X M) → Prop) : Φ C challenge b Ex ∅ = 0 := by
  have : IncOf C challenge Ex (cached b (∅ : (PrefixSpec n X M b).QueryCache)) = ∅ :=
    Set.eq_empty_iff_forall_notMem.mpr fun t ht => ht.2.1 rfl
  simp [Φ, this]

omit [DecidableEq M] in
theorem covers_mono {S S' : List (Entry n X M) → Prop} (h : ∀ x, S x → S' x)
    {t : List (Entry n X M)} (ht : Covers C challenge S t) : Covers C challenge S' t :=
  fun i hi hv => h _ (ht i hi hv)

omit [Fact n.Prime] in
theorem cached_cacheQuery (c : (PrefixSpec n X M b).QueryCache) (p : List (Entry n X M))
    (u : Fin (2 ^ b)) : cached b (c.cacheQuery p u) = fun x => cached b c x ∨ x = p := by
  funext x
  by_cases hx : x = p
  · subst hx
    simp [cached]
  · simp [cached, hx]


/-- **One fresh answer**: if the cache is good and the prefix `p` is fresh,
the answer for `p` makes the cache bad with probability at most `k/2^b`, where
`k` is the number of batches the answer completes, and the potential drops by
`k - 1`. It drops by `k` unless `p` itself counts for the bad event. -/
theorem bad_step [UniformAnswerMeasure (PrefixSpec n X M b)] (hord : PrimeOrder n E)
    (hb : 2 ^ b ≤ n) (Ex : List (Entry n X M) → Prop)
    (c : (PrefixSpec n X M b).QueryCache) (p : List (Entry n X M))
    (hbad : ¬ Bad C challenge b Ex c) (hp : c p = none) :
    ∃ k Ψ : ℝ≥0∞,
      Pr{let u ← (liftM ((PrefixSpec n X M b).query p) :
          OracleComp (PrefixSpec n X M b) (Fin (2 ^ b)))}[
        Bad C challenge b Ex (c.cacheQuery p u)] ≤
          k * (Fintype.card (Fin (2 ^ b)) : ℝ≥0∞)⁻¹ ∧
      (∀ u, Φ C challenge b Ex (c.cacheQuery p u) ≤ Ψ) ∧
        k + Ψ ≤ (({p} ∩ {t | Counts C challenge Ex t} : Set (List (Entry n X M))).encard : ℝ≥0∞) +
          Φ C challenge b Ex c := by
  classical
  let S : List (Entry n X M) → Prop := fun x => cached b c x ∨ x = p
  have hS : ∀ u, cached b (c.cacheQuery p u) = S := cached_cacheQuery b c p
  -- the batches that the answer for `p` completes
  let NC : Set (List (Entry n X M)) :=
    {t | Counts C challenge Ex t ∧ Covers C challenge S t ∧ ¬ Covers C challenge (cached b c) t}
  refine ⟨(NC.encard : ℝ≥0∞), ((IncOf C challenge Ex S).encard : ℝ≥0∞), ?_, ?_, ?_⟩
  · by_cases hfin : NC.Finite
    swap
    · rw [Set.Infinite.encard_eq hfin, ENat.toENNReal_top, ENNReal.top_mul]
      · exact le_top
      · exact ENNReal.inv_ne_zero.mpr (ENNReal.natCast_ne_top _)
    rw [hfin.encard_eq_coe_toFinset_card, ENat.toENNReal_coe]
    refine (prEvent_mono_of_support _ _
      (fun u => ∃ t ∈ hfin.toFinset,
        batchVerify C challenge t.get (cacheCoeff b (c.cacheQuery p u) t) = true)
      fun u _ hu => ?_).trans (prEvent_exists_finset_le_card_mul _ _ _ fun t ht => ?_)
    · obtain ⟨t, hrel, hcov, hbv⟩ := hu
      rw [hS u] at hcov
      refine ⟨t, hfin.mem_toFinset.mpr ⟨hrel, hcov, fun hcov' => hbad ⟨t, hrel, hcov', ?_⟩⟩, hbv⟩
      refine batchVerify_congr C challenge hord t.get (fun i hi => ?_) hbv
      unfold cacheCoeff
      split_ifs with hi0
      · rfl
      · have hne : t.take (i + 1) ≠ p := fun h => hcov' i hi0 hi (h ▸ hp)
        rw [QueryCache.cacheQuery_of_ne _ _ hne]
    · obtain ⟨hrel, hcov, hncov⟩ := hfin.mem_toFinset.mp ht
      obtain ⟨i₀, hi₀, hinv, hnone⟩ : ∃ i₀ : Fin t.length, (i₀ : ℕ) ≠ 0 ∧
          valid C challenge (t.get i₀) = false ∧ ¬ cached b c (t.take (i₀ + 1)) := by
        by_contra! h
        exact hncov fun i hi hv => h i hi hv
      have hp₀ : t.take (i₀ + 1) = p := (hcov i₀ hi₀ hinv).resolve_left hnone
      rw [prEvent_liftM_query_eq_card_div]
      have hcard : (Finset.univ.filter fun u : Fin (2 ^ b) =>
          batchVerify C challenge t.get (cacheCoeff b (c.cacheQuery p u) t) = true).card ≤ 1 := by
        refine Finset.card_le_one.mpr fun u hu u' hu' => ?_
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hu hu'
        have h := batchVerify_sound C challenge hord t.get hinv (fun i hi => by
          unfold cacheCoeff
          split_ifs with hi0
          · rfl
          · have hne : t.take (i + 1) ≠ p := by
              rw [← hp₀]
              intro h
              apply hi
              have := congrArg List.length h
              simp only [List.length_take] at this
              have := i.2
              have := i₀.2
              ext
              omega
            rw [QueryCache.cacheQuery_of_ne _ _ hne, QueryCache.cacheQuery_of_ne _ _ hne]) hu hu'
        subst hp₀
        simp only [cacheCoeff, hi₀, ↓reduceIte, QueryCache.cacheQuery_self] at h
        have h' : ((u : ℕ) : ZMod n) = ((u' : ℕ) : ZMod n) := by simpa using h
        rw [ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt (u.2.trans_le hb),
          Nat.mod_eq_of_lt (u'.2.trans_le hb)] at h'
        exact Fin.ext h'
      calc ((Finset.univ.filter fun u : Fin (2 ^ b) =>
            batchVerify C challenge t.get (cacheCoeff b (c.cacheQuery p u) t) = true).card :
              ℝ≥0∞) / (Fintype.card (Fin (2 ^ b)) : ℝ≥0∞)
          ≤ 1 / (Fintype.card (Fin (2 ^ b)) : ℝ≥0∞) := by gcongr; exact_mod_cast hcard
        _ = _ := one_div _
  · intro u
    rw [Φ, hS u]
  · have hdisj : Disjoint NC (IncOf C challenge Ex S) :=
      Set.disjoint_left.mpr fun t h1 h2 => h2.2.2 h1.2.1
    have hsub : NC ∪ IncOf C challenge Ex S ⊆
        IncOf C challenge Ex (cached b c) ∪ ({p} ∩ {t | Counts C challenge Ex t}) := by
      rintro t (⟨hrel, hcov, hncov⟩ | ⟨hrel, hSt, hncov⟩)
      · by_cases htp : t = p
        · exact Or.inr ⟨htp, hrel⟩
        · refine Or.inl ⟨hrel, ?_, hncov⟩
          obtain ⟨h1, hlast⟩ := hrel.1
          have := hcov ⟨t.length - 1, by omega⟩ (by change t.length - 1 ≠ 0; omega) hlast
          rw [show t.length - 1 + 1 = t.length by omega, List.take_of_length_le le_rfl] at this
          exact this.resolve_right htp
      · by_cases htp : t = p
        · exact Or.inr ⟨htp, hrel⟩
        · exact Or.inl ⟨hrel, hSt.resolve_right htp,
            fun hcov => hncov (covers_mono C challenge (fun x hx => Or.inl hx) hcov)⟩
    calc (NC.encard : ℝ≥0∞) + ((IncOf C challenge Ex S).encard : ℝ≥0∞)
        = ((NC ∪ IncOf C challenge Ex S).encard : ℝ≥0∞) := by
          rw [Set.encard_union_eq hdisj, ENat.toENNReal_add]
      _ ≤ ((IncOf C challenge Ex (cached b c) ∪
            ({p} ∩ {t | Counts C challenge Ex t})).encard : ℝ≥0∞) :=
          ENat.toENNReal_le.mpr (Set.encard_le_encard hsub)
      _ ≤ ((IncOf C challenge Ex (cached b c)).encard +
            ({p} ∩ {t | Counts C challenge Ex t} : Set (List (Entry n X M))).encard : ℕ∞) :=
          ENat.toENNReal_le.mpr (Set.encard_union_le _ _)
      _ = _ := by rw [ENat.toENNReal_add, add_comm, Φ]

/-- `k` is the length of a prefix of `L` that ends with an invalid signature. -/
def EndsInvalid (L : List (Entry n X M)) (k : ℕ) : Prop :=
  ∃ h : 0 < k ∧ k ≤ L.length,
    valid C challenge (L.get ⟨k - 1, by have := h.1; have := h.2; omega⟩) = false

instance (L : List (Entry n X M)) : DecidablePred (EndsInvalid C challenge L) :=
  fun _ => by unfold EndsInvalid; infer_instance

/-- The length of the longest prefix of `L` that ends with an invalid signature
(`0` if all are valid). -/
def lastInvalid (L : List (Entry n X M)) : ℕ :=
  Nat.findGreatest (EndsInvalid C challenge L) L.length

/-- The prefix of `L` up to its last invalid signature: the batch that the
verifier's coefficients can complete. -/
def target (L : List (Entry n X M)) : List (Entry n X M) := L.take (lastInvalid C challenge L)

/-- The proper prefixes of `T`. -/
def ExT (T t : List (Entry n X M)) : Prop := t.length < T.length ∧ t <+: T

omit [DecidableEq M] in
/-- Every prefix of `L` is the target, a proper prefix of it, or ends with a
valid signature. -/
theorem take_target_or (L : List (Entry n X M)) (k : ℕ) (hk : k ≤ L.length) :
    L.take k = target C challenge L ∨ ExT (target C challenge L) (L.take k) ∨
      ¬ Rel C challenge (L.take k) := by
  have hmL : lastInvalid C challenge L ≤ L.length := Nat.findGreatest_le _
  rcases lt_trichotomy k (lastInvalid C challenge L) with h | h | h
  · refine Or.inr (Or.inl ⟨?_, List.take_prefix_take_left h.le⟩)
    simp only [target, List.length_take]
    omega
  · exact Or.inl (by rw [target, h])
  · refine Or.inr (Or.inr fun ⟨h1, hlast⟩ => Nat.findGreatest_is_greatest h hk ?_)
    have hlen : (L.take k).length = k := by simp [hk]
    refine ⟨⟨by omega, hk⟩, ?_⟩
    simpa [List.getElem_take, hlen] using hlast

open scoped Classical in
/-- The potential of the target: `1` until its own coefficient is cached. -/
noncomputable def tgtPot (T : List (Entry n X M)) (c : (PrefixSpec n X M b).QueryCache) :
    ℝ≥0∞ :=
  if c T = none then 1 else 0

/-- **One fresh answer in the verifier's phase**: if the queried prefix is the
target, a proper prefix of it, or ends with a valid signature, then the bad
event (ignoring proper prefixes of the target) costs no extra `1`. -/
theorem final_step [UniformAnswerMeasure (PrefixSpec n X M b)] (hord : PrimeOrder n E)
    (hb : 2 ^ b ≤ n) (T : List (Entry n X M)) (c : (PrefixSpec n X M b).QueryCache)
    (p : List (Entry n X M)) (hP : p = T ∨ ExT T p ∨ ¬ Rel C challenge p)
    (hbad : ¬ Bad C challenge b (ExT T) c) (hp : c p = none) :
    ∃ k Ψ : ℝ≥0∞,
      Pr{let u ← (liftM ((PrefixSpec n X M b).query p) :
          OracleComp (PrefixSpec n X M b) (Fin (2 ^ b)))}[
        Bad C challenge b (ExT T) (c.cacheQuery p u)] ≤
          k * (Fintype.card (Fin (2 ^ b)) : ℝ≥0∞)⁻¹ ∧
      (∀ u, Φ C challenge b (ExT T) (c.cacheQuery p u) + tgtPot b T (c.cacheQuery p u) ≤ Ψ) ∧
        k + Ψ ≤ ((0 : ℕ) : ℝ≥0∞) + (Φ C challenge b (ExT T) c + tgtPot b T c) := by
  obtain ⟨k, Ψ, h1, h2, h3⟩ := bad_step C challenge b hord hb (ExT T) c p hbad hp
  rw [Nat.cast_zero, zero_add]
  by_cases hpT : p = T
  · subst hpT
    refine ⟨k, Ψ, h1, fun u => ?_, ?_⟩
    · rw [show tgtPot b p (c.cacheQuery p u) = 0 by simp [tgtPot], add_zero]
      exact h2 u
    · calc k + Ψ ≤ _ := h3
        _ ≤ 1 + Φ C challenge b (ExT p) c := by
          gcongr
          calc _ ≤ (({p} : Set (List (Entry n X M))).encard : ℝ≥0∞) :=
                ENat.toENNReal_le.mpr (Set.encard_le_encard Set.inter_subset_left)
            _ = 1 := by simp
        _ = _ := by rw [show tgtPot b p c = 1 by simp [tgtPot, hp], add_comm]
  · have hzero : ({p} ∩ {t | Counts C challenge (ExT T) t} : Set (List (Entry n X M))) = ∅ := by
      refine Set.eq_empty_iff_forall_notMem.mpr fun t ⟨htp, hrel⟩ => ?_
      rw [Set.mem_singleton_iff] at htp
      subst htp
      rcases hP with h | h | h
      · exact hpT h
      · exact hrel.2 h
      · exact h hrel.1
    rw [hzero, Set.encard_empty, ENat.toENNReal_zero, zero_add] at h3
    have hne : T ≠ p := fun h => hpT h.symm
    refine ⟨k, Ψ + tgtPot b T c, h1, fun u => add_le_add (h2 u) ?_, ?_⟩
    · rw [tgtPot, tgtPot, QueryCache.cacheQuery_of_ne _ _ hne]
    · rw [← add_assoc]
      exact add_le_add h3 le_rfl

/-- **A win leaves a bad cache**: the target of the winning batch has a cached
coefficient for each invalid signature and passes with them. -/
theorem wins_bad (hord : PrimeOrder n E)
    (adv : OracleComp (PrefixSpec n X M b) (List (Entry n X M)))
    (z : (List (Entry n X M) × List (ZMod n)) × (PrefixSpec n X M b).QueryCache)
    (hz : z ∈ support
      ((simulateQ (PrefixSpec n X M b).cachingOracle (batchGame b prefixKey adv)).run ∅))
    (hw : Wins C challenge z.1) :
    Bad C challenge b (ExT (target C challenge z.1.1)) z.2 := by
  have : Fact (1 < n) := ⟨(Fact.out : n.Prime).one_lt⟩
  obtain ⟨⟨L, as⟩, c₂⟩ := z
  change Bad C challenge b (ExT (target C challenge L)) c₂
  obtain ⟨h1, h2'⟩ := game_spec b prefixKey adv L as c₂ hz
  have h2 : ∀ k < L.length, k ≠ 0 → ∃ h : Fin (2 ^ b),
      c₂ (L.take (k + 1)) = some h ∧ as.getD k 0 = ((h : ℕ) : ZMod n) := h2'
  obtain ⟨hv, i, hi⟩ := hw
  simp only at hv i hi
  -- the last invalid signature
  have hPi : EndsInvalid C challenge L (i + 1) := ⟨⟨by omega, i.2⟩, by simpa using hi⟩
  have hli : lastInvalid C challenge L = Nat.findGreatest (EndsInvalid C challenge L) L.length :=
    rfl
  have hm1 : (i : ℕ) + 1 ≤ Nat.findGreatest (EndsInvalid C challenge L) L.length :=
    Nat.le_findGreatest i.2 hPi
  obtain ⟨⟨hm0, hmL⟩, hjv⟩ := Nat.findGreatest_spec (P := EndsInvalid C challenge L) i.2 hPi
  obtain ⟨j, hjm⟩ : ∃ j : Fin L.length, (j : ℕ) + 1 = lastInvalid C challenge L :=
    ⟨⟨Nat.findGreatest (EndsInvalid C challenge L) L.length - 1, by omega⟩, by simp only; omega⟩
  have hj : valid C challenge (L.get j) = false := by
    have : j = ⟨Nat.findGreatest (EndsInvalid C challenge L) L.length - 1, by omega⟩ :=
      Fin.ext (by simp only; omega)
    rw [this]
    exact hjv
  have hafter : ∀ i : Fin L.length, j < i → valid C challenge (L.get i) = true := by
    intro i hji
    by_contra hvi
    rw [Fin.lt_def] at hji
    exact Nat.findGreatest_is_greatest (P := EndsInvalid C challenge L) (k := i + 1) (by omega)
      i.2 ⟨⟨by omega, i.2⟩, by simpa using hvi⟩
  have hj0 : (j : ℕ) ≠ 0 := by
    intro hj0
    have hsingle := batchVerify_sound_single C challenge hord L.get hj
      (fun i hi => hafter i (by
        rw [Fin.lt_def, hj0]
        exact Nat.pos_of_ne_zero fun h => hi (Fin.ext (h.trans hj0.symm))))
      (a := fun i => as.getD i 0) (by rw [h1 j j.2 hj0]; exact one_ne_zero)
    unfold verifyList at hv
    rw [hv] at hsingle
    cases hsingle
  have hlen : (L.take (j + 1)).length = j + 1 := by simp
  refine ⟨L.take (j + 1), ⟨⟨by omega, ?_⟩, fun h => ?_⟩, fun i hi0 hinv => ?_, ?_⟩
  · simpa [List.getElem_take, hlen] using hj
  · have := h.1
    simp only [target, List.length_take] at this
    omega
  · have hi : (i : ℕ) < L.length := by have := i.2; omega
    obtain ⟨h, hc, -⟩ := h2 i hi hi0
    rw [List.take_take, min_eq_left (by have := i.2; omega)]
    simp [cached, hc]
  · have := batchVerify_take C challenge hord L j.2 hafter (fun k => as.getD k 0) hv
    refine batchVerify_congr C challenge hord _ (fun i _ => ?_) this
    have hi : (i : ℕ) < L.length := by have := i.2; omega
    unfold cacheCoeff
    split_ifs with hi0
    · exact h1 i hi hi0
    · obtain ⟨h, hc, ha⟩ := h2 i hi hi0
      rw [List.take_take, min_eq_left (by have := i.2; omega), hc]
      simpa using ha

omit [DecidableEq M] in
/-- The verifier's phase starts from the attacker's cache at most `1/2^b` worse. -/
theorem badVal_phase (L : List (Entry n X M)) (c : (PrefixSpec n X M b).QueryCache) :
    badVal (Bad C challenge b (ExT (target C challenge L)))
      (fun c => Φ C challenge b (ExT (target C challenge L)) c +
        tgtPot b (target C challenge L) c) c ≤
    (Fintype.card (Fin (2 ^ b)) : ℝ≥0∞)⁻¹ +
      badVal (Bad C challenge b (fun _ => False)) (Φ C challenge b (fun _ => False)) c := by
  by_cases h₁ : Bad C challenge b (fun _ => False) c
  · rw [show badVal (Bad C challenge b (fun _ => False)) _ c = 1 by simp [badVal, h₁]]
    exact (badVal_le_one _ _ _).trans le_add_self
  have h₂ : ¬ Bad C challenge b (ExT (target C challenge L)) c :=
    fun ⟨t, hrel, hcov, hbv⟩ => h₁ ⟨t, ⟨hrel.1, not_false⟩, hcov, hbv⟩
  have hΦ : Φ C challenge b (ExT (target C challenge L)) c ≤
      Φ C challenge b (fun _ => False) c :=
    ENat.toENNReal_le.mpr (Set.encard_le_encard fun t ht => ⟨⟨ht.1.1, not_false⟩, ht.2⟩)
  have htg : tgtPot b (target C challenge L) c ≤ 1 := by
    unfold tgtPot
    split_ifs <;> simp
  simp only [badVal, h₁, h₂, ↓reduceIte]
  rcases le_total 1 (Φ C challenge b (fun _ => False) c *
      (Fintype.card (Fin (2 ^ b)) : ℝ≥0∞)⁻¹) with h | h
  · rw [min_eq_left h]
    exact (min_le_left _ _).trans le_add_self
  · rw [min_eq_right h]
    calc _ ≤ (Φ C challenge b (ExT (target C challenge L)) c +
            tgtPot b (target C challenge L) c) * (Fintype.card (Fin (2 ^ b)) : ℝ≥0∞)⁻¹ :=
          min_le_right _ _
      _ ≤ (Φ C challenge b (fun _ => False) c + 1) * (Fintype.card (Fin (2 ^ b)) : ℝ≥0∞)⁻¹ := by
          gcongr
      _ = _ := by rw [add_mul, one_mul, add_comm]

/-- **BIP340 batch verification is sound with incrementally hash-derived
coefficients**, in the random oracle model: the coefficient of signature `i`
(for `i ≥ 2`) is a `b`-bit hash of the first `i` entries, with `2^b ≤ n`. An
attacker that makes at most `q` oracle queries gets a batch containing an
invalid signature accepted with probability at most `(q + 1)/2^b`, however
large the batch. This holds for every challenge hash. -/
theorem batch_incremental_sound [UniformAnswerMeasure (PrefixSpec n X M b)]
    (hord : PrimeOrder n E) (hb : 2 ^ b ≤ n)
    (adv : OracleComp (PrefixSpec n X M b) (List (Entry n X M))) (q : ℕ)
    (hq : IsTotalQueryBound adv q) :
    Pr{let z ← (simulateQ (PrefixSpec n X M b).cachingOracle
      (batchGame b prefixKey adv)).run ∅}[Wins C challenge z.1] ≤
        ((q + 1 : ℕ) : ℝ≥0∞) / (2 ^ b : ℕ) := by
  rw [prEvent_eq_wp_propInd]
  refine (wp_mono_of_support _ (post' := fun z =>
      badVal (Bad C challenge b (ExT (target C challenge z.1.1)))
        (fun c => Φ C challenge b (ExT (target C challenge z.1.1)) c +
          tgtPot b (target C challenge z.1.1) c) z.2) fun z hz =>
    (propInd_mono (wins_bad C challenge b hord adv z hz)).trans
      (propInd_le_badVal _ _ _)).trans ?_
  unfold batchGame
  rw [simulateQ_bind, StateT.run_bind, wp_bind]
  calc _ ≤ wp ((simulateQ (PrefixSpec n X M b).cachingOracle adv).run ∅)
        (fun x => (Fintype.card (Fin (2 ^ b)) : ℝ≥0∞)⁻¹ +
          badVal (Bad C challenge b (fun _ => False))
            (Φ C challenge b (fun _ => False)) x.2) := by
        refine wp_mono _ fun x => ?_
        obtain ⟨L, c₁⟩ := x
        rw [simulateQ_bind, StateT.run_bind, wp_bind]
        simp only [simulateQ_pure, StateT.run_pure, wp_pure]
        refine (wp_badVal_le _ _ (fun t => t = target C challenge L ∨
            ExT (target C challenge L) t ∨ ¬ Rel C challenge t) 0
          (fun c t ht h₁ h₂ => final_step C challenge b hord hb _ c t ht h₁ h₂) _ 0
          (isQueryBound_of_allQueries ((coeffs_allQueries b prefixKey L _).mono
            fun t ⟨i, hi⟩ => by
              rw [hi, prefixKey, List.take_eq_take_min]
              exact take_target_or C challenge L _ (min_le_right _ _))) c₁).trans ?_
        rw [Nat.cast_zero, zero_mul, zero_add]
        exact badVal_phase C challenge b L c₁
    _ = (Fintype.card (Fin (2 ^ b)) : ℝ≥0∞)⁻¹ +
          wp ((simulateQ (PrefixSpec n X M b).cachingOracle adv).run ∅)
            (fun x => badVal (Bad C challenge b (fun _ => False))
              (Φ C challenge b (fun _ => False)) x.2) := by
        rw [wp_add]
        exact congrArg (· + _) (wp_const _ _)
    _ ≤ (Fintype.card (Fin (2 ^ b)) : ℝ≥0∞)⁻¹ +
          (q * (Fintype.card (Fin (2 ^ b)) : ℝ≥0∞)⁻¹ +
            badVal (Bad C challenge b (fun _ => False))
              (Φ C challenge b (fun _ => False)) ∅) := by
        gcongr
        exact wp_badVal_le (Bad C challenge b (fun _ => False))
          (Φ C challenge b (fun _ => False)) (fun _ => True) 1
          (fun c t _ h₁ h₂ => by
            obtain ⟨k, Ψ, hk, hΨ, hkΨ⟩ :=
              bad_step C challenge b hord hb (fun _ => False) c t h₁ h₂
            refine ⟨k, Ψ, hk, hΨ, hkΨ.trans ?_⟩
            rw [Nat.cast_one]
            gcongr
            calc _ ≤ (({t} : Set (List (Entry n X M))).encard : ℝ≥0∞) :=
                  ENat.toENNReal_le.mpr (Set.encard_le_encard Set.inter_subset_left)
              _ = 1 := by simp)
          adv q (isQueryBound_of_total hq) ∅
    _ = _ := by
        rw [show badVal (Bad C challenge b (fun _ => False))
            (Φ C challenge b (fun _ => False)) ∅ = 0 by
          simp [badVal, bad_empty, Φ_empty]]
        rw [Fintype.card_fin, div_eq_mul_inv]
        push_cast
        ring

end Incremental

/-! ## Derivation from the whole batch

BIP340 itself derives the coefficients from a seed that hashes the whole
batch, expanded with a CSPRNG. We idealize this as a random oracle on
`(batch, index)`. Each coefficient now depends on every entry, so one fresh
answer completes at most one batch and no potential is needed. -/

section Indexed

variable {n : ℕ} [Fact n.Prime] {E X M : Type} [AddCommGroup E] [DecidableEq E] [DecidableEq X]
  [DecidableEq M] (C : Curve n E X) (challenge : X → X → M → ZMod n) (b : ℕ)

/-- Coefficient `i` hashes the whole batch together with `i`. -/
def indexKey (L : List (Entry n X M)) (i : ℕ) : List (Entry n X M) × ℕ := (L, i)

/-- The random oracle of whole-batch derivation: `(batch, index)` ↦ a `b`-bit value. -/
abbrev IndexSpec (n : ℕ) (X M : Type) (b : ℕ) := KeySpec (List (Entry n X M) × ℕ) b

namespace Indexed

/-- The coefficients of batch `L` as recorded in cache `c`. -/
def cacheCoeff (c : (IndexSpec n X M b).QueryCache) (L : List (Entry n X M))
    (i : Fin L.length) : ZMod n :=
  if (i : ℕ) = 0 then 1 else ((c (L, i)).map fun h => ((h : ℕ) : ZMod n)).getD 0

/-- The bad event: some batch with an invalid signature has the coefficients
of all its invalid signatures in the cache, and passes with them. -/
def Bad (c : (IndexSpec n X M b).QueryCache) : Prop :=
  ∃ L : List (Entry n X M), (∃ j : Fin L.length, valid C challenge (L.get j) = false) ∧
    (∀ i : Fin L.length, (i : ℕ) ≠ 0 → valid C challenge (L.get i) = false →
      c (L, i) ≠ none) ∧
    batchVerify C challenge L.get (cacheCoeff b c L) = true

omit [DecidableEq M] in
theorem bad_empty (hord : PrimeOrder n E) : ¬ Bad C challenge b ∅ := by
  have : Fact (1 < n) := ⟨(Fact.out : n.Prime).one_lt⟩
  rintro ⟨L, ⟨j, hj⟩, hcov, hbv⟩
  -- every invalid signature sits at position `0`
  have h0 : ∀ i : Fin L.length, valid C challenge (L.get i) = false → (i : ℕ) = 0 :=
    fun i hi => by_contra fun h => hcov i h hi rfl
  have hsingle := batchVerify_sound_single C challenge hord L.get hj
    (fun i hi => by
      by_contra hv
      exact hi (Fin.ext ((h0 i (by simpa using hv)).trans (h0 j hj).symm)))
    (a := cacheCoeff b ∅ L) (by simp [cacheCoeff, h0 j hj])
  rw [hbv] at hsingle
  cases hsingle

/-- **One fresh answer**: the answer for `(L, k)` can only complete batch `L`,
and at most one value of it makes `L` pass. -/
theorem bad_step [UniformAnswerMeasure (IndexSpec n X M b)] (hord : PrimeOrder n E)
    (hb : 2 ^ b ≤ n) (c : (IndexSpec n X M b).QueryCache) (p : List (Entry n X M) × ℕ)
    (hbad : ¬ Bad C challenge b c) (hp : c p = none) :
    ∃ k Ψ : ℝ≥0∞,
      Pr{let u ← (liftM ((IndexSpec n X M b).query p) :
          OracleComp (IndexSpec n X M b) (Fin (2 ^ b)))}[
        Bad C challenge b (c.cacheQuery p u)] ≤ k * (Fintype.card (Fin (2 ^ b)) : ℝ≥0∞)⁻¹ ∧
      (∀ u, (fun _ => (0 : ℝ≥0∞)) (c.cacheQuery p u) ≤ Ψ) ∧
        k + Ψ ≤ 1 + (fun _ => (0 : ℝ≥0∞)) c := by
  classical
  refine ⟨1, 0, ?_, fun _ => le_rfl, by simp⟩
  obtain ⟨L₀, k₀⟩ := p
  -- a bad answer makes `L₀` pass, and position `k₀` holds an invalid signature
  have hcand : ∀ u, Bad C challenge b (c.cacheQuery (L₀, k₀) u) →
      ∃ hk : k₀ < L₀.length, k₀ ≠ 0 ∧ valid C challenge (L₀.get ⟨k₀, hk⟩) = false ∧
        batchVerify C challenge L₀.get (cacheCoeff b (c.cacheQuery (L₀, k₀) u) L₀) = true := by
    rintro u ⟨L, hinv, hcov, hbv⟩
    by_cases hcovc : ∀ i : Fin L.length, (i : ℕ) ≠ 0 → valid C challenge (L.get i) = false →
        c (L, i) ≠ none
    · refine absurd ⟨L, hinv, hcovc, batchVerify_congr C challenge hord L.get (fun i hi => ?_)
        hbv⟩ hbad
      unfold cacheCoeff
      split_ifs with hi0
      · rfl
      · have hne : ((L, (i : ℕ)) : List (Entry n X M) × ℕ) ≠ (L₀, k₀) :=
          fun h => hcovc i hi0 hi (h ▸ hp)
        rw [QueryCache.cacheQuery_of_ne _ _ hne]
    · push Not at hcovc
      obtain ⟨i₀, hi₀, hv₀, hnone⟩ := hcovc
      have heq : ((L, (i₀ : ℕ)) : List (Entry n X M) × ℕ) = (L₀, k₀) := by
        by_contra hne
        exact hcov i₀ hi₀ hv₀ (by rwa [QueryCache.cacheQuery_of_ne _ _ hne])
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj heq
      exact ⟨i₀.2, hi₀, hv₀, hbv⟩
  by_cases hk : ∃ hk : k₀ < L₀.length, k₀ ≠ 0 ∧ valid C challenge (L₀.get ⟨k₀, hk⟩) = false
  swap
  · refine le_of_eq_of_le (prEvent_eq_zero_of_forall_mem_support _ _ fun u _ hu => ?_) bot_le
    obtain ⟨hk', hk0, hv, -⟩ := hcand u hu
    exact hk ⟨hk', hk0, hv⟩
  obtain ⟨hk, hk0, hv⟩ := hk
  refine (prEvent_mono_of_support _ _
    (fun u => batchVerify C challenge L₀.get (cacheCoeff b (c.cacheQuery (L₀, k₀) u) L₀) = true)
    fun u _ hu => (hcand u hu).2.2.2).trans ?_
  rw [prEvent_liftM_query_eq_card_div, one_mul]
  have hcard : (Finset.univ.filter fun u : Fin (2 ^ b) =>
      batchVerify C challenge L₀.get (cacheCoeff b (c.cacheQuery (L₀, k₀) u) L₀) = true).card ≤ 1 :=
      by
    refine Finset.card_le_one.mpr fun u hu u' hu' => ?_
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hu hu'
    have h := batchVerify_sound C challenge hord L₀.get (j := ⟨k₀, hk⟩) hv (fun i hi => by
      unfold cacheCoeff
      split_ifs with hi0
      · rfl
      · have hne : ((L₀, (i : ℕ)) : List (Entry n X M) × ℕ) ≠ (L₀, k₀) :=
          fun h => hi (Fin.ext (Prod.mk.inj h).2)
        rw [QueryCache.cacheQuery_of_ne _ _ hne, QueryCache.cacheQuery_of_ne _ _ hne]) hu hu'
    simp only [cacheCoeff, hk0, ↓reduceIte, QueryCache.cacheQuery_self] at h
    have h' : ((u : ℕ) : ZMod n) = ((u' : ℕ) : ZMod n) := by simpa using h
    rw [ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt (u.2.trans_le hb),
      Nat.mod_eq_of_lt (u'.2.trans_le hb)] at h'
    exact Fin.ext h'
  calc ((Finset.univ.filter fun u : Fin (2 ^ b) =>
        batchVerify C challenge L₀.get (cacheCoeff b (c.cacheQuery (L₀, k₀) u) L₀) = true).card :
          ℝ≥0∞) / (Fintype.card (Fin (2 ^ b)) : ℝ≥0∞)
      ≤ 1 / (Fintype.card (Fin (2 ^ b)) : ℝ≥0∞) := by gcongr; exact_mod_cast hcard
    _ = _ := one_div _

/-- **A win leaves a bad cache**: the verifier cached the coefficient of every
signature of the winning batch. -/
theorem wins_bad (hord : PrimeOrder n E)
    (adv : OracleComp (IndexSpec n X M b) (List (Entry n X M)))
    (z : (List (Entry n X M) × List (ZMod n)) × (IndexSpec n X M b).QueryCache)
    (hz : z ∈ support
      ((simulateQ (IndexSpec n X M b).cachingOracle (batchGame b indexKey adv)).run ∅))
    (hw : Wins C challenge z.1) : Bad C challenge b z.2 := by
  obtain ⟨⟨L, as⟩, c⟩ := z
  change Bad C challenge b c
  obtain ⟨h1, h2'⟩ := game_spec b indexKey adv L as c hz
  have h2 : ∀ k < L.length, k ≠ 0 → ∃ h : Fin (2 ^ b),
      c (L, k) = some h ∧ as.getD k 0 = ((h : ℕ) : ZMod n) := h2'
  obtain ⟨hv, i, hi⟩ := hw
  refine ⟨L, ⟨i, hi⟩, fun i hi0 _ => ?_, ?_⟩
  · obtain ⟨h, hc, -⟩ := h2 i i.2 hi0
    simp [hc]
  · refine batchVerify_congr C challenge hord _ (fun i _ => ?_) hv
    unfold cacheCoeff
    split_ifs with hi0
    · exact h1 i i.2 hi0
    · obtain ⟨h, hc, ha⟩ := h2 i i.2 hi0
      rw [hc]
      simpa using ha


/-- The invalid signatures of `L`, other than the first, whose coefficient is
not cached yet. -/
def Pending (c : (IndexSpec n X M b).QueryCache) (L : List (Entry n X M)) : Set (Fin L.length) :=
  {i | (i : ℕ) ≠ 0 ∧ valid C challenge (L.get i) = false ∧ c (L, i) = none}

open scoped Classical in
/-- The potential of the verifier's phase: `1` while batch `L` still waits for
a coefficient. -/
noncomputable def pendingPot (L : List (Entry n X M)) (c : (IndexSpec n X M b).QueryCache) :
    ℝ≥0∞ :=
  if (Pending C challenge b c L).Nonempty then 1 else 0

omit [DecidableEq M] in
theorem pendingPot_le_one (L : List (Entry n X M)) (c : (IndexSpec n X M b).QueryCache) :
    pendingPot C challenge b L c ≤ 1 := by
  unfold pendingPot
  split_ifs <;> simp

theorem mem_pending_cacheQuery (c : (IndexSpec n X M b).QueryCache) (L : List (Entry n X M))
    (k₀ : ℕ) (u : Fin (2 ^ b)) (i : Fin L.length) :
    i ∈ Pending C challenge b (c.cacheQuery (L, k₀) u) L ↔
      i ∈ Pending C challenge b c L ∧ (i : ℕ) ≠ k₀ := by
  simp only [Pending, Set.mem_ofPred_eq]
  by_cases hi : (i : ℕ) = k₀
  · subst hi
    simp [QueryCache.cacheQuery_self]
  · have hne : ((L, (i : ℕ)) : List (Entry n X M) × ℕ) ≠ (L, k₀) :=
      fun h => hi (Prod.mk.inj h).2
    rw [QueryCache.cacheQuery_of_ne _ _ hne]
    simp [hi]

/-- If the answer for `(L₀, k₀)` makes a good cache bad, then `k₀` is an
invalid position of `L₀` and the answer completes `L₀`. -/
theorem bad_cacheQuery (hord : PrimeOrder n E) (c : (IndexSpec n X M b).QueryCache)
    (L₀ : List (Entry n X M)) (k₀ : ℕ) (u : Fin (2 ^ b)) (hbad : ¬ Bad C challenge b c)
    (hp : c (L₀, k₀) = none) (hu : Bad C challenge b (c.cacheQuery (L₀, k₀) u)) :
    ∃ hk : k₀ < L₀.length, k₀ ≠ 0 ∧ valid C challenge (L₀.get ⟨k₀, hk⟩) = false ∧
      ∀ i : Fin L₀.length, (i : ℕ) ≠ 0 → valid C challenge (L₀.get i) = false →
        c.cacheQuery (L₀, k₀) u (L₀, i) ≠ none := by
  obtain ⟨L, hinv, hcov, hbv⟩ := hu
  by_cases hcovc : ∀ i : Fin L.length, (i : ℕ) ≠ 0 → valid C challenge (L.get i) = false →
      c (L, i) ≠ none
  · refine absurd ⟨L, hinv, hcovc, batchVerify_congr C challenge hord L.get (fun i hi => ?_)
      hbv⟩ hbad
    unfold cacheCoeff
    split_ifs with hi0
    · rfl
    · have hne : ((L, (i : ℕ)) : List (Entry n X M) × ℕ) ≠ (L₀, k₀) :=
        fun h => hcovc i hi0 hi (h ▸ hp)
      rw [QueryCache.cacheQuery_of_ne _ _ hne]
  · push Not at hcovc
    obtain ⟨i₀, hi₀, hv₀, hnone⟩ := hcovc
    have heq : ((L, (i₀ : ℕ)) : List (Entry n X M) × ℕ) = (L₀, k₀) := by
      by_contra hne
      exact hcov i₀ hi₀ hv₀ (by rwa [QueryCache.cacheQuery_of_ne _ _ hne])
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj heq
    exact ⟨i₀.2, hi₀, hv₀, hcov⟩

/-- **One fresh answer in the verifier's phase**: answering a coefficient of
batch `L` makes the cache bad only if it is the last pending one, and then
with probability at most `1/2^b`. -/
theorem final_step [UniformAnswerMeasure (IndexSpec n X M b)] (hord : PrimeOrder n E)
    (hb : 2 ^ b ≤ n) (L : List (Entry n X M)) (c : (IndexSpec n X M b).QueryCache)
    (t : List (Entry n X M) × ℕ) (ht : t.1 = L) (hbad : ¬ Bad C challenge b c)
    (hp : c t = none) :
    ∃ k Ψ : ℝ≥0∞,
      Pr{let u ← (liftM ((IndexSpec n X M b).query t) :
          OracleComp (IndexSpec n X M b) (Fin (2 ^ b)))}[
        Bad C challenge b (c.cacheQuery t u)] ≤ k * (Fintype.card (Fin (2 ^ b)) : ℝ≥0∞)⁻¹ ∧
      (∀ u, pendingPot C challenge b L (c.cacheQuery t u) ≤ Ψ) ∧
        k + Ψ ≤ ((0 : ℕ) : ℝ≥0∞) + pendingPot C challenge b L c := by
  obtain ⟨L₀, k₀⟩ := t
  change L₀ = L at ht
  subst ht
  rw [Nat.cast_zero, zero_add]
  have hpr0 : ∀ u, Bad C challenge b (c.cacheQuery (L₀, k₀) u) →
      (∃ i ∈ Pending C challenge b c L₀, (i : ℕ) = k₀) ∧
        ∀ i ∈ Pending C challenge b c L₀, (i : ℕ) = k₀ := by
    intro u hu
    obtain ⟨hk, hk0, hv, hcov⟩ := bad_cacheQuery C challenge b hord c L₀ k₀ u hbad hp hu
    refine ⟨⟨⟨k₀, hk⟩, ⟨hk0, hv, hp⟩, rfl⟩, fun i hi => ?_⟩
    by_contra hne
    exact hcov i hi.1 hi.2.1
      ((mem_pending_cacheQuery C challenge b c L₀ k₀ u i).mpr ⟨hi, hne⟩).2.2
  by_cases hall : (∃ i ∈ Pending C challenge b c L₀, (i : ℕ) = k₀) ∧
      ∀ i ∈ Pending C challenge b c L₀, (i : ℕ) = k₀
  · -- the answer settles the last pending coefficient
    obtain ⟨k', Ψ', hk', -, hkΨ'⟩ := bad_step C challenge b hord hb c (L₀, k₀) hbad hp
    have hk1 : k' ≤ 1 := le_self_add.trans (by simpa using hkΨ')
    refine ⟨1, 0, hk'.trans (by gcongr), fun u => ?_, ?_⟩
    · have : ¬ (Pending C challenge b (c.cacheQuery (L₀, k₀) u) L₀).Nonempty := by
        rintro ⟨i, hi⟩
        rw [mem_pending_cacheQuery] at hi
        exact hi.2 (hall.2 i hi.1)
      simp [pendingPot, this]
    · obtain ⟨⟨i, hi, -⟩, -⟩ := hall
      simp [pendingPot, show (Pending C challenge b c L₀).Nonempty from ⟨i, hi⟩]
  · refine ⟨0, pendingPot C challenge b L₀ c, ?_, fun u => ?_, by rw [zero_add]⟩
    · rw [zero_mul]
      exact le_of_eq (prEvent_eq_zero_of_forall_mem_support _ _ fun u _ hu => hall (hpr0 u hu))
    · unfold pendingPot
      split_ifs with h1 h2
      · exact le_rfl
      · obtain ⟨i, hi⟩ := h1
        rw [mem_pending_cacheQuery] at hi
        exact absurd ⟨i, hi.1⟩ h2
      · exact bot_le
      · exact le_rfl

end Indexed

/-- **BIP340 batch verification is sound with coefficients derived from the
whole batch**, in the random oracle model: the coefficient of signature `i`
(for `i ≥ 2`) is a `b`-bit hash of the batch and `i`, with `2^b ≤ n`. An
attacker that makes at most `q` oracle queries gets a batch containing an
invalid signature accepted with probability at most `(q + 1)/2^b`, however
large the batch. This holds for every challenge hash. -/
theorem batch_indexed_sound [UniformAnswerMeasure (IndexSpec n X M b)]
    (hord : PrimeOrder n E) (hb : 2 ^ b ≤ n)
    (adv : OracleComp (IndexSpec n X M b) (List (Entry n X M))) (q : ℕ)
    (hq : IsTotalQueryBound adv q) :
    Pr{let z ← (simulateQ (IndexSpec n X M b).cachingOracle
      (batchGame b indexKey adv)).run ∅}[Wins C challenge z.1] ≤
        ((q + 1 : ℕ) : ℝ≥0∞) / (2 ^ b : ℕ) := by
  rw [prEvent_eq_wp_propInd]
  refine (wp_mono_of_support _ (post' := fun z => badVal (Indexed.Bad C challenge b)
      (Indexed.pendingPot C challenge b z.1.1) z.2) fun z hz =>
    (propInd_mono (Indexed.wins_bad C challenge b hord adv z hz)).trans
      (propInd_le_badVal _ _ _)).trans ?_
  unfold batchGame
  rw [simulateQ_bind, StateT.run_bind, wp_bind]
  calc _ ≤ wp ((simulateQ (IndexSpec n X M b).cachingOracle adv).run ∅)
        (fun x => (Fintype.card (Fin (2 ^ b)) : ℝ≥0∞)⁻¹ +
          badVal (Indexed.Bad C challenge b) (fun _ => 0) x.2) := by
        refine wp_mono _ fun x => ?_
        obtain ⟨L, c₁⟩ := x
        rw [simulateQ_bind, StateT.run_bind, wp_bind]
        simp only [simulateQ_pure, StateT.run_pure, wp_pure]
        refine (wp_badVal_le (Indexed.Bad C challenge b) (Indexed.pendingPot C challenge b L)
          (fun t => t.1 = L) 0
          (fun c t ht h₁ h₂ => Indexed.final_step C challenge b hord hb L c t ht h₁ h₂) _ 0
          (isQueryBound_of_allQueries ((coeffs_allQueries b indexKey L _).mono
            fun t ⟨i, hi⟩ => by rw [hi]; rfl)) c₁).trans ?_
        rw [Nat.cast_zero, zero_mul, zero_add]
        unfold badVal
        split_ifs
        · exact le_add_self
        · refine (min_le_right _ _).trans ?_
          rw [zero_mul, min_eq_right zero_le_one, add_zero]
          calc _ ≤ 1 * (Fintype.card (Fin (2 ^ b)) : ℝ≥0∞)⁻¹ := by
                gcongr
                exact Indexed.pendingPot_le_one C challenge b L c₁
            _ = _ := one_mul _
    _ = (Fintype.card (Fin (2 ^ b)) : ℝ≥0∞)⁻¹ +
          wp ((simulateQ (IndexSpec n X M b).cachingOracle adv).run ∅)
            (fun x => badVal (Indexed.Bad C challenge b) (fun _ => 0) x.2) := by
        rw [wp_add]
        exact congrArg (· + _) (wp_const _ _)
    _ ≤ (Fintype.card (Fin (2 ^ b)) : ℝ≥0∞)⁻¹ +
          (q * (Fintype.card (Fin (2 ^ b)) : ℝ≥0∞)⁻¹ +
            badVal (Indexed.Bad C challenge b) (fun _ => 0) ∅) := by
        gcongr
        exact wp_badVal_le (Indexed.Bad C challenge b) (fun _ => 0) (fun _ => True) 1
          (fun c t _ h₁ h₂ => by
            obtain ⟨k, Ψ, h⟩ := Indexed.bad_step C challenge b hord hb c t h₁ h₂
            exact ⟨k, Ψ, h.1, h.2.1, by simpa using h.2.2⟩)
          adv q (isQueryBound_of_total hq) ∅
    _ = _ := by
        rw [show badVal (Indexed.Bad C challenge b) (fun _ => 0) ∅ = 0 by
          simp [badVal, Indexed.bad_empty C challenge b hord]]
        rw [Fintype.card_fin, div_eq_mul_inv]
        push_cast
        ring

end Indexed

/-! ## The `q` term is necessary: grinding

The bounds `(q + 1)/2^b` cannot drop their `q`: an attacker who simply tries
batches wins with probability `1 - (1 - 2^-b)^q`, which is about `q/2^b` while
`q ≪ 2^b`. From one valid signature `(pk, m, r, s)`, the batch
`[(pk, m, r, s - δ), (pk, m, r, s + δ)]` has defects `-δ·G` and `δ·G`, so it
passes exactly when its second coefficient is `1`. The attacker hashes these
batches for `δ = 1, …, q` and outputs the first whose coefficient is `1`.

For a two-signature batch both derivations hash the whole batch, so the same
attacker works against each: `batch_grind` is stated for any derivation whose
second coefficient tells the candidates apart. -/

section Grinding

variable {n : ℕ} [Fact n.Prime] {E X M : Type} [AddCommGroup E] [DecidableEq E] [DecidableEq X]
  (C : Curve n E X) (challenge : X → X → M → ZMod n) (b : ℕ)
  {K : Type} [DecidableEq K] (key : List (Entry n X M) → ℕ → K)

namespace Grind

/-- Signature `v` with `s` shifted by `d`. -/
def tweak (v : Entry n X M) (d : ZMod n) : Entry n X M := { v with s := v.s + d }

/-- The `δ`-th candidate batch: two shifted copies of `v`. -/
def cand (v : Entry n X M) (δ : ℕ) : List (Entry n X M) :=
  [tweak v (-(δ : ZMod n)), tweak v δ]

/-- The grinding attacker with `k` hash queries left. -/
def grind (v : Entry n X M) (ht : 1 < 2 ^ b) :
    ℕ → OracleComp (KeySpec K b) (List (Entry n X M))
  | 0 => pure (cand v 1)
  | k + 1 => do
    let h ← (liftM ((KeySpec K b).query (key (cand v (k + 1)) 1)) :
      OracleComp (KeySpec K b) (Fin (2 ^ b)))
    if h = ⟨1, ht⟩ then pure (cand v (k + 1)) else grind v ht k

/-- The attacker found a candidate whose coefficient is `1`. -/
def Found (v : Entry n X M) (ht : 1 < 2 ^ b)
    (z : List (Entry n X M) × (KeySpec K b).QueryCache) : Prop :=
  ∃ δ, 0 < δ ∧ δ < n ∧ z.1 = cand v δ ∧ z.2 (key (cand v δ) 1) = some ⟨1, ht⟩

theorem tweak_defect {v : Entry n X M} (hv : valid C challenge v = true) (d : ZMod n) :
    defect C challenge (tweak v d) = C.mulG d := by
  have h0 := ((valid_iff C challenge v).mp hv).2.2
  have : defect C challenge (tweak v d) = defect C challenge v + C.mulG d := by
    simp only [defect, tweak, R, P, e, map_add]
    abel
  rw [this, h0, zero_add]

theorem tweak_invalid {v : Entry n X M} (hv : valid C challenge v = true) {d : ZMod n}
    (hd : d ≠ 0) : valid C challenge (tweak v d) = false := by
  cases h : valid C challenge (tweak v d)
  · rfl
  · have := ((valid_iff C challenge _).mp h).2.2
    rw [tweak_defect C challenge hv] at this
    exact absurd (C.mulG_eq_zero.mp this) hd

/-- A candidate batch passes when both its coefficients are `1`. -/
theorem cand_pass (hord : PrimeOrder n E) {v : Entry n X M} (hv : valid C challenge v = true)
    (d : ZMod n) (ent : Fin 2 → Entry n X M) (h0 : ent 0 = tweak v (-d))
    (h1 : ent 1 = tweak v d) (a : Fin 2 → ZMod n) (ha0 : a 0 = 1) (ha1 : a 1 = 1) :
    batchVerify C challenge ent a = true := by
  have : Fact (1 < n) := ⟨(Fact.out : n.Prime).one_lt⟩
  have hlift := (valid_iff C challenge v).mp hv
  rw [batchVerify_iff C challenge hord]
  refine ⟨Fin.forall_fin_two.mpr ⟨?_, ?_⟩, ?_⟩
  · rw [h0]; exact ⟨hlift.1, hlift.2.1⟩
  · rw [h1]; exact ⟨hlift.1, hlift.2.1⟩
  · rw [Fin.sum_univ_two, h0, h1, ha0, ha1, tweak_defect C challenge hv,
      tweak_defect C challenge hv, ZMod.val_one, one_smul, one_smul, map_neg, neg_add_cancel]

omit [DecidableEq X] in
theorem cand_inj (v : Entry n X M) {δ δ' : ℕ} (hδ : δ < n) (hδ' : δ' < n)
    (h : cand v δ = cand v δ') : δ = δ' := by
  have h2 := congrArg (fun L : List (Entry n X M) => (L.getD 1 v).s) h
  simp only [cand, tweak, List.getD_cons_succ, List.getD_cons_zero, add_right_inj] at h2
  rwa [ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt hδ, Nat.mod_eq_of_lt hδ'] at h2

omit [DecidableEq X] [DecidableEq K] in
theorem grind_bound (v : Entry n X M) (ht : 1 < 2 ^ b) (k : ℕ) :
    IsTotalQueryBound (grind b key v ht k) k := by
  induction k with
  | zero => trivial
  | succ k ih =>
    rw [grind, isTotalQueryBound_query_bind_iff]
    refine ⟨Nat.succ_pos k, fun u => ?_⟩
    split_ifs
    · trivial
    · exact ih

omit [DecidableEq X] [DecidableEq K] in
theorem grind_length (v : Entry n X M) (ht : 1 < 2 ^ b) (k : ℕ) :
    ∀ L ∈ support (grind b key v ht k), L.length = 2 := by
  induction k with
  | zero => intro L hL; simp only [grind, support_pure, Set.mem_singleton_iff] at hL; subst hL; rfl
  | succ k ih =>
    intro L hL
    rw [grind, mem_support_bind_iff] at hL
    obtain ⟨u, -, hL⟩ := hL
    split_ifs at hL
    · simp only [support_pure, Set.mem_singleton_iff] at hL; subst hL; rfl
    · exact ih L hL

omit [DecidableEq X] in
/-- **The attacker misses with probability at most `(1 - 2^-b)^k`**, as long
as none of its `k` candidates has been hashed yet. -/
theorem grind_miss [UniformAnswerMeasure (KeySpec K b)] (v : Entry n X M)
    (hkey : ∀ δ δ', key (cand v δ) 1 = key (cand v δ') 1 → cand v δ = cand v δ')
    (ht : 1 < 2 ^ b) (k : ℕ) (hk : k < n) (c : (KeySpec K b).QueryCache)
    (hc : ∀ δ, 0 < δ → δ ≤ k → c (key (cand v δ) 1) = none) :
    Pr{let z ← (simulateQ (KeySpec K b).cachingOracle (grind b key v ht k)).run c}[
      ¬ Found b key v ht z] ≤ (((2 ^ b - 1 : ℕ) : ℝ≥0∞) / (2 ^ b : ℕ)) ^ k := by
  induction k generalizing c with
  | zero => rw [pow_zero]; exact prEvent_le_one _
  | succ k ih =>
    rw [grind, simulateQ_bind, cachingOracle.simulateQ_query, StateT.run_bind,
      cachingOracle.run_none (hc (k + 1) (Nat.succ_pos k) le_rfl), bind_map_left,
      prEvent_bind_eq_sum_fintype]
    have hq : ∀ u : Fin (2 ^ b), Pr{let x ← (liftM ((KeySpec K b).query
        (key (cand v (k + 1)) 1)) : OracleComp (KeySpec K b) (Fin (2 ^ b)))}[x = u] =
          ((2 ^ b : ℕ) : ℝ≥0∞)⁻¹ := fun u => by
      refine (prEvent_liftM_query_eq_card_div (spec := KeySpec K b) _ (· = u)).trans ?_
      simp [Finset.filter_eq', one_div]
    set B := (((2 ^ b - 1 : ℕ) : ℝ≥0∞) / (2 ^ b : ℕ)) with hB
    let tgt : Fin (2 ^ b) := ⟨1, ht⟩
    calc _ ≤ ∑ u : Fin (2 ^ b), (if u = tgt then 0 else ((2 ^ b : ℕ) : ℝ≥0∞)⁻¹ * B ^ k) := by
          refine Finset.sum_le_sum fun u _ => ?_
          rw [hq u]
          by_cases hu : u = tgt
          · subst hu
            simp only [tgt, ↓reduceIte, simulateQ_pure, StateT.run_pure]
            refine le_of_eq (mul_eq_zero_of_right _
              (prEvent_eq_zero_of_forall_mem_support _ _ fun z hz hnf => hnf ?_))
            rw [support_pure, Set.mem_singleton_iff] at hz
            subst hz
            exact ⟨k + 1, Nat.succ_pos k, hk, rfl, QueryCache.cacheQuery_self _ _ _⟩
          · simp only [tgt] at hu
            simp only [tgt, hu, ↓reduceIte]
            gcongr
            refine ih (by omega) _ fun δ hδ hδk => ?_
            have hne : key (cand v δ) 1 ≠ key (cand v (k + 1)) 1 := fun h => by
              have := cand_inj v (δ := δ) (δ' := k + 1) (by omega) hk (hkey _ _ h)
              omega
            rw [QueryCache.cacheQuery_of_ne _ _ hne]
            exact hc δ hδ (by omega)
      _ = ((2 ^ b - 1 : ℕ) : ℝ≥0∞) * (((2 ^ b : ℕ) : ℝ≥0∞)⁻¹ * B ^ k) := by
          rw [← Finset.add_sum_erase _ _ (Finset.mem_univ tgt),
            ite_eq_left_of_eq_true _ _ (eq_true rfl), zero_add, Finset.sum_congr rfl fun u hu =>
              ite_eq_right_of_eq_false _ _ (eq_false (Finset.ne_of_mem_erase hu)),
            Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
            Fintype.card_fin, nsmul_eq_mul]
      _ = B ^ (k + 1) := by
          rw [pow_succ]
          simp only [hB, div_eq_mul_inv]
          ring

end Grind

open Grind in
/-- **Grinding, for any derivation** that hashes a two-signature batch into
its second coefficient without collisions between candidates: the attacker
`grind`, which makes `q` hash queries and outputs batches of two signatures,
wins with probability at least `1 - (1 - 2^-b)^q`. -/
theorem batch_grind [UniformAnswerMeasure (KeySpec K b)]
    (hord : PrimeOrder n E) (ht : 1 < 2 ^ b) {v : Entry n X M}
    (hv : valid C challenge v = true)
    (hkey : ∀ δ δ', key (cand v δ) 1 = key (cand v δ') 1 → cand v δ = cand v δ')
    (q : ℕ) (hq : q < n) :
    1 - (((2 ^ b - 1 : ℕ) : ℝ≥0∞) / (2 ^ b : ℕ)) ^ q ≤
      Pr{let z ← (simulateQ (KeySpec K b).cachingOracle
        (batchGame b key (grind b key v ht q))).run ∅}[Wins C challenge z.1] := by
  have hmiss := grind_miss b key v hkey ht q hq ∅ fun _ _ _ => rfl
  have hfound : 1 - (((2 ^ b - 1 : ℕ) : ℝ≥0∞) / (2 ^ b : ℕ)) ^ q ≤
      Pr{let z ← (simulateQ (KeySpec K b).cachingOracle (grind b key v ht q)).run ∅}[
        Found b key v ht z] :=
    calc _ ≤ 1 - Pr{let z ← (simulateQ (KeySpec K b).cachingOracle
          (grind b key v ht q)).run ∅}[¬ Found b key v ht z] := tsub_le_tsub_left hmiss 1
      _ = _ := by
        rw [prEvent_not_eq_one_sub, ENNReal.sub_sub_cancel ENNReal.one_ne_top (prEvent_le_one _)]
  unfold batchGame
  rw [simulateQ_bind, StateT.run_bind]
  refine le_trans hfound ?_
  rw [← mul_one (Pr{let z ← (simulateQ (KeySpec K b).cachingOracle
    (grind b key v ht q)).run ∅}[Found b key v ht z])]
  refine mul_le_prEvent_bind_of_forall _ _ (Found b key v ht) _ le_rfl
    fun x hx => (prEvent_eq_one_of_forall_mem_support _ _ fun z hz => ?_).ge
  obtain ⟨L, c⟩ := x
  obtain ⟨δ, hδ, hδn, rfl, hcδ⟩ := hx
  rw [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hz
  obtain ⟨⟨as, c₂⟩, h₂, hz⟩ := hz
  simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
  subst hz
  have hco := coeffs_spec b key (cand v δ) _ c (as, c₂) h₂
  have hle := simulateQ_cachingOracle_cache_le _ c _ h₂
  have ha0 : as.getD 0 0 = 1 := by simpa using (hco 0 (by simp [cand])).1 (by simp)
  have ha1 : as.getD 1 0 = 1 := by
    obtain ⟨h, hc, ha⟩ := (hco 1 (by simp [cand])).2 (by simp [cand])
    have hc' : c₂ (key (cand v δ) 1) = some h := by
      rw [List.getElem_range] at hc
      exact hc
    rw [hle hcδ, Option.some.injEq] at hc'
    simpa [← hc'] using ha
  have hδ0 : (δ : ZMod n) ≠ 0 := fun h => by
    have := congrArg ZMod.val h
    rw [ZMod.val_natCast, ZMod.val_zero, Nat.mod_eq_of_lt hδn] at this
    omega
  refine ⟨cand_pass C challenge hord hv δ (cand v δ).get rfl rfl _ (by simpa using ha0)
    (by simpa using ha1), ⟨1, by simp [cand]⟩, tweak_invalid C challenge hv hδ0⟩

variable [DecidableEq M]

open Grind in
/-- **Grinding matches the bound, whole-batch derivation**: from any valid
signature `v`, the attacker `grind`, which makes `q` hash queries and outputs
batches of two signatures, gets a batch containing an invalid signature
accepted with probability at least `1 - (1 - 2^-b)^q`. Compare
`batch_indexed_sound`'s upper bound `(q + 1)/2^b`. -/
theorem batch_indexed_grind [UniformAnswerMeasure (IndexSpec n X M b)]
    (hord : PrimeOrder n E) (ht : 1 < 2 ^ b) {v : Entry n X M}
    (hv : valid C challenge v = true) (q : ℕ) (hq : q < n) :
    1 - (((2 ^ b - 1 : ℕ) : ℝ≥0∞) / (2 ^ b : ℕ)) ^ q ≤
      Pr{let z ← (simulateQ (IndexSpec n X M b).cachingOracle
        (batchGame b indexKey (grind b indexKey v ht q))).run ∅}[Wins C challenge z.1] :=
  batch_grind C challenge b indexKey hord ht hv (fun _ _ h => (Prod.mk.inj h).1) q hq

open Grind in
/-- **Grinding matches the bound, incremental derivation**: the same attacker
reaches `1 - (1 - 2^-b)^q` against incremental derivation, since the second
coefficient of a two-signature batch hashes the whole batch. Compare
`batch_incremental_sound`'s upper bound `(q + 1)/2^b`. -/
theorem batch_incremental_grind [UniformAnswerMeasure (PrefixSpec n X M b)]
    (hord : PrimeOrder n E) (ht : 1 < 2 ^ b) {v : Entry n X M}
    (hv : valid C challenge v = true) (q : ℕ) (hq : q < n) :
    1 - (((2 ^ b - 1 : ℕ) : ℝ≥0∞) / (2 ^ b : ℕ)) ^ q ≤
      Pr{let z ← (simulateQ (PrefixSpec n X M b).cachingOracle
        (batchGame b prefixKey (grind b prefixKey v ht q))).run ∅}[Wins C challenge z.1] :=
  batch_grind C challenge b prefixKey hord ht hv (fun _ _ h => by simpa [prefixKey, cand] using h)
    q hq

end Grinding

/-! ## On secp256k1 with 128-bit coefficients -/

section Secp256k1

open Secp256k1

theorem two_pow_128_le_n : 2 ^ 128 ≤ n := by decide

/-- `batch_incremental_sound` on secp256k1 with 128-bit coefficients: an
invalid batch is accepted with probability at most `(q + 1)/2^128`. Unlike the
generic version this needs no `PrimeOrder` hypothesis: secp256k1 has exactly
`n` points (`Secp256k1.card_eq_n`). -/
theorem secp256k1_batch_incremental_sound {M : Type} [DecidableEq M]
    (challenge : F → F → M → ZMod n) [UniformAnswerMeasure (PrefixSpec n F M 128)]
    (adv : OracleComp (PrefixSpec n F M 128) (List (Entry n F M)))
    (q : ℕ) (hq : IsTotalQueryBound adv q) :
    Pr{let z ← (simulateQ (PrefixSpec n F M 128).cachingOracle
      (batchGame 128 prefixKey adv)).run ∅}[Wins secp256k1 challenge z.1] ≤
        ((q + 1 : ℕ) : ℝ≥0∞) / (2 ^ 128 : ℕ) :=
  batch_incremental_sound secp256k1 challenge 128 primeOrder two_pow_128_le_n adv q hq

/-- `batch_indexed_sound` on secp256k1 with 128-bit coefficients: an invalid
batch is accepted with probability at most `(q + 1)/2^128`, with no
`PrimeOrder` hypothesis. -/
theorem secp256k1_batch_indexed_sound {M : Type} [DecidableEq M]
    (challenge : F → F → M → ZMod n) [UniformAnswerMeasure (IndexSpec n F M 128)]
    (adv : OracleComp (IndexSpec n F M 128) (List (Entry n F M)))
    (q : ℕ) (hq : IsTotalQueryBound adv q) :
    Pr{let z ← (simulateQ (IndexSpec n F M 128).cachingOracle
      (batchGame 128 indexKey adv)).run ∅}[Wins secp256k1 challenge z.1] ≤
        ((q + 1 : ℕ) : ℝ≥0∞) / (2 ^ 128 : ℕ) :=
  batch_indexed_sound secp256k1 challenge 128 primeOrder two_pow_128_le_n adv q hq

end Secp256k1

end BatchVerify.BIP340Batch
