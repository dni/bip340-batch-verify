import BatchVerify.Curve
import BatchVerify.Primes

/-!
# secp256k1

The curve `y² = x³ + 7` over `𝔽_p`, `p = 2^256 - 2^32 - 977`, with the BIP340
generator `G`, built on Mathlib's elliptic-curve group
(`WeierstrassCurve.Affine.Point`, whose group law, associativity included, is
proven in Mathlib).

We construct `secp256k1 : Curve n Point F`, so the BIP340/341 theorems apply.
What goes into it:
* `p` and `n` are prime: kernel-checked Pratt certificates (`BatchVerify.Primes`).
* `G` is on the curve: kernel computation.
* `n • G = 0`: double-and-add evaluated by `native_decide` (this trusts Lean's
  compiler in addition to its kernel).
* `lift_x` is correct: proven, using `p ≡ 3 (mod 4)` and that no point has `y = 0`
  (`-7` is not a cube mod `p`, checked by the kernel).

We also prove that the group has exactly `n` points (`card_eq_n`), so every
point satisfies `n·P = 0` (`primeOrder`).
-/

namespace BatchVerify.Secp256k1

/-- The field size `p`. -/
abbrev p : ℕ := 2 ^ 256 - 2 ^ 32 - 977

/-- The order `n` of the generator. -/
abbrev n : ℕ := 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141

instance : Fact p.Prime := ⟨Primes.prime_p⟩
instance : Fact n.Prime := ⟨Primes.prime_n⟩

/-- The base field `𝔽_p`. -/
abbrev F : Type := ZMod p

/-- secp256k1 as a Weierstrass curve: `y² = x³ + 7`. -/
def W : WeierstrassCurve F := { a₁ := 0, a₂ := 0, a₃ := 0, a₄ := 0, a₆ := 7 }

/-- Points of secp256k1 (including the point at infinity `0`). Mathlib makes this a group. -/
abbrev Point : Type := W.toAffine.Point

theorem seven_ne_zero : (7 : F) ≠ 0 := by decide +kernel

theorem Δ_ne_zero : W.Δ ≠ 0 := by
  have : W.Δ = -21168 := by
    simp only [WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
      WeierstrassCurve.b₆, WeierstrassCurve.b₈, W]
    ring
  rw [this]
  decide +kernel

theorem nonsingular_iff (x y : F) : W.toAffine.Nonsingular x y ↔ y ^ 2 = x ^ 3 + 7 := by
  rw [← W.toAffine.equation_iff_nonsingular_of_Δ_ne_zero Δ_ne_zero,
    WeierstrassCurve.Affine.equation_iff]
  simp [W]

/-! ## The generator -/

def Gx : F := 0x79BE667EF9DCBBAC55A06295CE870B07029BFCDB2DCE28D959F2815B16F81798
def Gy : F := 0x483ADA7726A3C4655DA4FBFC0E1108A8FD17B448A68554199C47D08FFB10D4B8

theorem G_on_curve : Gy ^ 2 = Gx ^ 3 + 7 := by decide +kernel

/-- The BIP340 generator `G`. -/
def G : Point := .some Gx Gy ((nonsingular_iff _ _).mpr G_on_curve)

/-- Double-and-add scalar multiplication. -/
def smulDA {A : Type*} [AddMonoid A] (k : ℕ) (P : A) : A :=
  if k = 0 then 0 else
  let Q := smulDA (k / 2) (P + P)
  if k % 2 = 0 then Q else Q + P
termination_by k
decreasing_by omega

theorem smulDA_eq {A : Type*} [AddMonoid A] (k : ℕ) (P : A) : smulDA k P = k • P := by
  induction k using Nat.strong_induction_on generalizing P with
  | _ k ih =>
    rw [smulDA]
    split_ifs with h0 h2
    · simp [h0]
    · rw [ih _ (by omega), ← two_nsmul, ← mul_nsmul', show k / 2 * 2 = k by omega]
    · rw [ih _ (by omega), ← two_nsmul, ← mul_nsmul', ← succ_nsmul,
        show k / 2 * 2 + 1 = k by omega]

set_option linter.style.native false in
/-- `G` has order `n`, checked by running double-and-add. -/
theorem n_smul_G : n • G = 0 := by
  rw [← smulDA_eq]
  native_decide

/-! ## x-coordinates, parity and `lift_x` -/

/-- The x-coordinate of a point (`0` for the point at infinity). -/
def xCoord : Point → F
  | .zero => 0
  | .some x _ _ => x

/-- BIP340 `has_even_y`. -/
def hasEvenY : Point → Bool
  | .zero => true
  | .some _ y _ => y.val % 2 == 0

/-- Pick the even one of `y` and `-y`. -/
def evenRoot (y : F) : F := if y.val % 2 = 0 then y else -y

theorem evenRoot_sq (y : F) : evenRoot y ^ 2 = y ^ 2 := by
  unfold evenRoot; split_ifs <;> simp

theorem p_odd : p % 2 = 1 := by decide

/-- For `y ≠ 0`, `y` and `-y` have opposite parity (as integers in `[0, p)`). -/
theorem val_neg_parity {y : F} (hy : y ≠ 0) : (-y).val % 2 ≠ y.val % 2 := by
  rw [ZMod.neg_val]
  simp only [hy, ↓reduceIte]
  have := ZMod.val_lt y
  have := p_odd
  omega

/-- No point of secp256k1 has `y = 0`: that would need `x³ = -7`, but `-7` is
not a cube mod `p` since `(-7)^((p-1)/3) ≠ 1`. -/
theorem y_ne_zero {x y : F} (h : y ^ 2 = x ^ 3 + 7) : y ≠ 0 := by
  rintro rfl
  have hx3 : x ^ 3 = -7 := by linear_combination -h
  have hx : x ≠ 0 := by
    rintro rfl
    exact seven_ne_zero (by linear_combination hx3)
  have hcube : (-7 : F) ^ ((p - 1) / 3) = 1 := by
    rw [← hx3, ← pow_mul, show 3 * ((p - 1) / 3) = p - 1 by decide +kernel]
    exact ZMod.pow_card_sub_one_eq_one hx
  have hneg7 : (-7 : F) = ((p - 7 : ℕ) : F) := by
    rw [Nat.cast_sub (by decide +kernel), ZMod.natCast_self, zero_sub, Nat.cast_ofNat]
  rw [hneg7, Pratt.natCast_pow_eq_powMod _ _ _ (by decide +kernel)] at hcube
  revert hcube
  decide +kernel

/-- The square-root exponent `(p+1)/4`. It is kept opaque so that Lean never
tries to unfold `c ^ sqrtExp` by repeated multiplication. -/
irreducible_def sqrtExp : ℕ := (p + 1) / 4

/-- BIP340 `lift_x`: `y = c^((p+1)/4)` for `c = x³ + 7`, fail unless `y² = c`,
then take the even one of `±y`. -/
def liftX (x : F) : Option Point :=
  if h : (((x ^ 3 + 7) ^ sqrtExp) ^ 2 = x ^ 3 + 7) then
    some (.some x (evenRoot ((x ^ 3 + 7) ^ sqrtExp))
      ((nonsingular_iff _ _).mpr (by rw [evenRoot_sq, h])))
  else none

/-- On the curve, `c^((p+1)/4)` is a square root of `c = y²` (since `p ≡ 3 mod 4`). -/
theorem sqrt_sq {x y : F} (h : y ^ 2 = x ^ 3 + 7) :
    ((x ^ 3 + 7) ^ sqrtExp) ^ 2 = x ^ 3 + 7 := by
  rw [sqrtExp_def, ← h, ← pow_mul, ← pow_mul,
    show 2 * ((p + 1) / 4 * 2) = (p - 1) + 2 by decide +kernel,
    pow_add, ZMod.pow_card_sub_one_eq_one (y_ne_zero h), one_mul]

theorem liftX_some {x y : F} (h : W.toAffine.Nonsingular x y) (hy : y.val % 2 = 0) :
    liftX x = some (.some x y h) := by
  have hc := (nonsingular_iff x y).mp h
  have hy0 := y_ne_zero hc
  simp only [liftX, sqrt_sq hc, ↓reduceDIte, Option.some.injEq,
    WeierstrassCurve.Affine.Point.some.injEq, true_and]
  -- The candidate root `r` is `y` or `-y`; `evenRoot` picks the even one, which is `y`.
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp ((sqrt_sq hc).trans hc.symm) with hr | hr <;>
    rw [hr, evenRoot]
  · simp [hy]
  · have := val_neg_parity hy0
    simp [show (-y).val % 2 ≠ 0 by omega]

/-! ## secp256k1 satisfies the BIP340 curve interface -/

theorem x_neg (P : Point) : xCoord (-P) = xCoord P := by
  cases P <;> rfl

theorem hasEvenY_neg (P : Point) (hP : P ≠ 0) : hasEvenY (-P) = !hasEvenY P := by
  cases P with
  | zero => exact absurd rfl hP
  | some x y h =>
    have hy0 := y_ne_zero ((nonsingular_iff x y).mp h)
    have := val_neg_parity hy0
    erw [WeierstrassCurve.Affine.Point.neg_some]
    have hneg : W.toAffine.negY x y = -y := by simp [W]
    simp only [hasEvenY, hneg]
    rcases Nat.mod_two_eq_zero_or_one y.val with h0 | h1
    · simp [h0, show (-y).val % 2 = 1 by omega]
    · simp [h1, show (-y).val % 2 = 0 by omega]

theorem liftX_x (P : Point) (hP : P ≠ 0) (heven : hasEvenY P = true) :
    liftX (xCoord P) = some P := by
  cases P with
  | zero => exact absurd rfl hP
  | some x y h =>
    simp only [hasEvenY, beq_iff_eq] at heven
    exact liftX_some h heven

theorem liftX_spec (r : F) (P : Point) (h : liftX r = some P) :
    P ≠ 0 ∧ hasEvenY P = true ∧ xCoord P = r := by
  unfold liftX at h
  split_ifs at h with hc
  cases h
  refine ⟨WeierstrassCurve.Affine.Point.some_ne_zero _, ?_, rfl⟩
  have hy0 := y_ne_zero hc
  simp only [hasEvenY, evenRoot, beq_iff_eq]
  split_ifs with he
  · exact he
  · have := val_neg_parity hy0
    omega

/-- **secp256k1**, packaged as the curve interface BIP340/341 are proven against. -/
def secp256k1 : Curve n Point F where
  G := G
  G_ne_zero := WeierstrassCurve.Affine.Point.some_ne_zero _
  order_G := n_smul_G
  x := xCoord
  hasEvenY := hasEvenY
  liftX := liftX
  x_neg := x_neg
  hasEvenY_neg := hasEvenY_neg
  liftX_x := liftX_x
  liftX_spec := liftX_spec

/-! ## The group has exactly `n` points

No point-counting algorithm is needed: a point is determined
by its x-coordinate and the parity of its y-coordinate, so there are at most
`2p + 1` points. `n` divides their number (`G` has order `n`), and `3n > 2p + 1`,
so there are `n` or `2n` points. No point has order `2` (that needs `y = 0`), so
by Cauchy's theorem the number of points is odd, hence `n`. -/

/-- A point's x-coordinate and y-parity (`none` for the point at infinity). -/
def code : Point → Option (F × Bool)
  | .zero => none
  | .some x y _ => some (x, y.val % 2 == 0)

theorem code_injective : Function.Injective code := by
  rintro (_ | ⟨x, y, h⟩) (_ | ⟨x', y', h'⟩) hc
  · rfl
  · cases hc
  · cases hc
  · simp only [code, Option.some.injEq, Prod.mk.injEq] at hc
    obtain ⟨rfl, hpar⟩ := hc
    have hc := (nonsingular_iff x y).mp h
    have hc' := (nonsingular_iff x y').mp h'
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp (hc'.trans hc.symm) with rfl | rfl
    · rfl
    · have := val_neg_parity (y_ne_zero hc)
      exfalso
      rcases Nat.mod_two_eq_zero_or_one y.val with h0 | h1 <;>
        simp_all

instance : Finite Point := Finite.of_injective code code_injective

theorem card_le : Nat.card Point ≤ 2 * p + 1 := by
  have := Nat.card_le_card_of_injective code code_injective
  rwa [Finite.card_option, Nat.card_prod, Nat.card_zmod, Nat.card_eq_fintype_card (α := Bool),
    Fintype.card_bool, mul_comm] at this

/-- No point has order `2`: `P = -P` forces `y = -y`, so `y = 0`. -/
theorem eq_zero_of_two_nsmul {P : Point} (h : 2 • P = 0) : P = 0 := by
  cases P with
  | zero => rfl
  | some x y hP =>
    exfalso
    have := val_neg_parity (y_ne_zero ((nonsingular_iff x y).mp hP))
    rw [two_nsmul, add_eq_zero_iff_eq_neg] at h
    erw [WeierstrassCurve.Affine.Point.neg_some] at h
    have hneg : W.toAffine.negY x y = -y := by simp [W]
    simp only [WeierstrassCurve.Affine.Point.some.injEq, hneg] at h
    rw [← h.2] at this
    exact this rfl

theorem card_odd : ¬ 2 ∣ Nat.card Point := by
  intro h2
  have : Fintype Point := Fintype.ofFinite _
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcard : Fintype.card (Multiplicative Point) = Nat.card Point := by
    rw [← Nat.card_eq_fintype_card]; rfl
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card (G := Multiplicative Point) 2 (hcard ▸ h2)
  have h1 : g ^ 2 = 1 := hg ▸ pow_orderOf_eq_one g
  have h0 : Multiplicative.toAdd g = 0 :=
    eq_zero_of_two_nsmul (by rw [← toAdd_pow, h1, toAdd_one])
  have : g = 1 := by rw [← ofAdd_toAdd g, h0, ofAdd_zero]
  rw [this, orderOf_one] at hg
  cases hg

/-- **secp256k1 has exactly `n` points.** -/
theorem card_eq_n : Nat.card Point = n := by
  have hdvd : n ∣ Nat.card Point := by
    rw [← addOrderOf_eq_prime n_smul_G (WeierstrassCurve.Affine.Point.some_ne_zero _)]
    exact addOrderOf_dvd_natCard _
  obtain ⟨k, hk⟩ := hdvd
  have hle := card_le
  have hodd := card_odd
  rw [hk] at hle hodd
  have hk3 : k < 3 := by
    by_contra h
    have : n * 3 ≤ n * k := Nat.mul_le_mul_left n (by omega)
    have : 2 * p + 1 < n * 3 := by decide
    omega
  interval_cases k
  · simp at hodd
  · rw [hk, mul_one]
  · exact absurd (dvd_mul_left 2 n) hodd

/-- **Every point of secp256k1 satisfies `n·P = 0`**, the hypothesis
`Curve.PrimeOrder` of the batch verification results. -/
theorem primeOrder : Curve.PrimeOrder n Point := fun _ => by
  rw [← card_eq_n]
  exact card_nsmul_eq_zero'

end BatchVerify.Secp256k1
