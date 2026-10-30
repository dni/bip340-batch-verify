# bip340-batch-verify

Machine-checked proofs, in [Lean 4](https://lean-lang.org) with [Mathlib](https://github.com/leanprover-community/mathlib4) and [VCVio](https://github.com/Verified-zkEVM/VCV-io), that BIP340 batch verification is sound with **128-bit randomizers derived deterministically from the batch**, and that the bound is tight.

Extracted from [taproot-lean](https://github.com/dni/taproot-lean), which also covers BIP341, MuSig2, DLCs and Bech32m.

## Motivation

[sipa/bips#219](https://github.com/sipa/bips/issues/219) and [sipa/bips#222](https://github.com/sipa/bips/pull/222) propose shrinking BIP340's batch-verification randomizers from 256 to 128 bits, which speeds up batch verification in libsecp256k1 by up to about 9%. The pen-and-paper argument there treats the randomizers as independent uniform values. In practice they are derived deterministically from the batch, and with incremental derivation (as in libsecp256k1's batch API) the attacker can pick later entries after seeing earlier randomizers.

## Results

Each result holds for every choice of the challenge hash.

| Setting | Result | Theorem |
|---|---|---|
| Independent uniform `b`-bit randomizers | An invalid signature is caught except with probability `2^-b`. | `batchVerify_sound_bits` |
| Randomizers hashed from the whole batch (the BIP340 text) | An attacker making `q` hash queries gets an invalid batch accepted with probability **at most `(q + 1)/2^b`**, however large the batch. | `batch_indexed_sound` |
| Incremental derivation (randomizer `i` hashes the first `i` entries) | The same bound, **`(q + 1)/2^b`**, although the attacker chooses later entries after seeing earlier randomizers. | `batch_incremental_sound` |
| Both derivations on secp256k1 with `b = 128` | **`(q + 1)/2^128`** | `secp256k1_batch_indexed_sound`, `secp256k1_batch_incremental_sound` |
| Lower bound, both derivations | An explicit grinding attacker reaches **`1 - (1 - 2^-b)^q ≈ q/2^b`** (for `q ≪ 2^b`), so the bound is tight. | `batch_indexed_grind`, `batch_incremental_grind` |

What this means for 128-bit randomizers: they are sound, and the only extra cost of deriving them deterministically is offline grinding at one hash per attempt. About `2^64` hash evaluations get an invalid batch accepted with probability about `2^-64`.

The grinding attack: from one valid signature `(pk, m, r, s)`, the batch `[(pk, m, r, s - δ), (pk, m, r, s + δ)]` contains two invalid signatures whose errors cancel, so it passes exactly when its second randomizer is `1`. The attacker hashes these batches for `δ = 1, …, q`. For a two-signature batch both derivations hash the whole batch into the second randomizer, so the same attacker works against both.

### All theorems

`BatchVerify/BIP340Props.lean`, randomizers as plain values:

| Theorem | Statement |
|---|---|
| `batchVerify_of_valid` | Batch verification accepts every batch of valid signatures, for every choice of coefficients. |
| `batchVerify_sound` | If one signature is invalid, then once the other coefficients are fixed, at most one value of its coefficient lets the batch pass. |
| `batchVerify_sound_bits` | The same with `b`-bit coefficients (`2^b ≤ n`): at most one `b`-bit value lets the batch pass. |
| `batchVerify_sound_single` | A single invalid signature with a nonzero coefficient (e.g. BIP340's fixed `a₁ = 1`) is always caught. |

`BatchVerify/BIP340Batch.lean`, randomizers from a random oracle with `b`-bit answers:

| Theorem | Statement |
|---|---|
| `batch_incremental_sound` | Incremental derivation: winning probability at most `(q + 1)/2^b` (`2^b ≤ n`), for batches of any size. |
| `batch_indexed_sound` | Whole-batch derivation: the same bound. |
| `secp256k1_batch_indexed_sound`, `secp256k1_batch_incremental_sound` | Both bounds on secp256k1 with `b = 128`. |
| `batch_grind` | The grinding lower bound `1 - (1 - 2^-b)^q` for any derivation that tells the candidate batches apart. |
| `batch_indexed_grind`, `batch_incremental_grind` | The grinding lower bound for each derivation, against the upper bound `(q + 1)/2^b`. |
| `wp_badVal_le` | A generic random-oracle bad-event bound with a potential, in expectation. It allows one fresh answer to complete several bad candidates, as long as earlier queries paid for them, and lets a phase of queries be paid for by the potential alone. |

Proof idea (incremental): cut the winning batch after its last invalid signature. That prefix still passes, and its equation involves only coefficients of its own prefixes. The last of those to be answered must hit the single value that solves the equation. One fresh answer can complete many cached extensions of the queried prefix, but each cached prefix is completed only once, so the total stays at one bad value per query. Whole-batch derivation is simpler: one fresh answer completes at most one batch.

The verifier's own hash queries cost `1/2^b` in total, not `1/2^b` each: only the last missing coefficient of the checked batch can complete it. The proof tracks the expected value of the bad event plus a potential across the attacker's and the verifier's phases, so the potential left by the attacker carries over. While the verifier works, the bad event ignores the proper prefixes of the checked batch, which can pass on their own when a coefficient is `0` without the batch passing.

## Assumptions and trust base

- The seed hash and the CSPRNG are idealized as a random oracle. The first randomizer is fixed to `1`, as in BIP340.
- The generic results assume every point satisfies `n·P = 0` (`Curve.PrimeOrder`). For secp256k1 this is proven (`Secp256k1.primeOrder`): there are at most `2p + 1` points, their number is a multiple of `n` and odd (no point has `y = 0`), so it is exactly `n`. The `secp256k1_…` versions therefore have no such hypothesis.
- The challenge hash is an arbitrary function: no property of SHA-256 is assumed.
- The random oracle is queried on the batch itself (or its prefix), so different batches get independent randomizers. A real implementation hashes a byte encoding, and the results apply only if that encoding is **injective**. See [Encoding of the seed](#encoding-of-the-seed).

The model is checked against the official [BIP340 test vectors](https://github.com/bitcoin/bips/blob/master/bip-0340/test-vectors.csv) (`BatchVerify/TestVectors.lean`, run by every `lake build`). For all 19 vectors, `BIP340.verify` gives the expected result, and where a secret key is given, `BIP340.pubkey` and `BIP340.sign` reproduce the public key and signature. The vectors run through double-and-add versions of these functions, which are proven equal to the model's definitions, with the tagged hashes computed by a SHA-256 implementation in `BatchVerify/SHA256.lean`. Byte decoding and its range checks (`pk < p`, `r < p`, `s < n`) are outside the model and are done in the test harness. The tests use compiled code, but no theorem depends on them.

### Encoding of the seed

BIP340 has allowed messages of arbitrary size since its 2023-04 revision, but its batch seed `seed_hash(pk₁..pkᵤ ‖ m₁..mᵤ ‖ sig₁..sigᵤ)` concatenates the messages without their lengths. Moving a byte from `m₁` to `m₂` gives a different batch with the same seed, and so the same randomizers. The incremental derivation in [bitcoin-core/secp256k1#1134](https://github.com/bitcoin-core/secp256k1/pull/1134) has the same issue. It hashes each entry as `type ‖ sig ‖ msg ‖ pk` without `msglen`, so `[(sig₁, m₁, pk₁), (sig₂, m₂, pk₂)]` reaches the same hash state as the single entry `(sig₁, m₁ ‖ pk₁ ‖ type ‖ sig₂ ‖ m₂, pk₂)`.

- **Bitcoin is not affected.** In Taproot (BIP341/342) every signed message is a 32-byte sighash. With fixed-length messages both encodings are injective, and the results apply as stated.
- **For messages of arbitrary length**, one seed query then serves many batches, so the bound in seed-hash queries does not follow. No practical attack is known, since each extra batch still costs the attacker a challenge-hash evaluation. That is not proven here, though.
- **The fix** is to hash each message's length before the message (e.g. as 8 bytes). This makes the encoding injective, so the results apply to messages of any length.

`lake build` prints `#print axioms` for every result above (`BatchVerify/Summary.lean`). All of them, the `secp256k1_…` versions included, use only Lean's standard axioms (`propext`, `Classical.choice`, `Quot.sound`): every computation on secp256k1 is checked by the kernel, and nothing uses `native_decide`.

## secp256k1

`BatchVerify/Secp256k1.lean` defines `y² = x³ + 7` over `𝔽_p` as a Mathlib `WeierstrassCurve`, using Mathlib's proven group law, and packages it as the interface in `BatchVerify/Curve.lean`. `p` and `n` are proven prime with kernel-checked Pratt certificates (`BatchVerify/Pratt.lean`, `BatchVerify/Primes.lean`, regenerated by `scripts/gen_primes.gp` with [PARI/GP](https://pari.math.u-bordeaux.fr/)). `n·G = 0` is checked by the kernel replaying a double-and-add chain for `(n - 1)·G` whose slopes come from a certificate (`BatchVerify/OrderCert.lean`, regenerated by `scripts/gen_order_cert.py`), so the kernel only adds and multiplies and never inverts a field element. Each step is proven to be Mathlib's group law.

## Building

Requirements: [elan](https://github.com/leanprover/elan), which installs the Lean toolchain pinned in `lean-toolchain`.

```sh
git clone https://github.com/dni/bip340-batch-verify
cd bip340-batch-verify
lake exe cache get   # download prebuilt Mathlib (several GB)
lake build
```

The first build also compiles the needed parts of VCVio, which has no prebuilt cache and can take an hour or more. The build succeeding means every proof has been checked. On machines with little memory, use `LEAN_NUM_THREADS=1 lake build`.

**Troubleshooting (Linux):** if the build fails with `undefined symbol` errors from Lean's bundled `clang`, run `env -u LD_LIBRARY_PATH lake build`.

## Layout

```
BatchVerify/
  Curve.lean        the curve interface the proofs are written against
  BIP340.lean       BIP340 Schnorr signatures
  BIP340Props.lean  batch verification with plain coefficients (plus non-malleability, key extraction)
  BIP340Batch.lean  batch verification with hash-derived coefficients (ROM), grinding lower bound
  Secp256k1.lean    the concrete curve, built on Mathlib's elliptic curves
  Pratt.lean        kernel-checked Pratt primality certificates
  Primes.lean       primality of p and n
  OrderCert.lean    slope certificate for n·G = 0
  SHA256.lean       SHA-256 and BIP340 tagged hashes, for the test vectors
  TestVectors.lean  the BIP340 test vectors, run against the model
  Summary.lean      axioms of the main results
```

## References

- [BIP340](https://github.com/bitcoin/bips/blob/master/bip-0340.mediawiki): Schnorr Signatures for secp256k1
- [sipa/bips#219](https://github.com/sipa/bips/issues/219), [sipa/bips#222](https://github.com/sipa/bips/pull/222): reducing BIP340 batch randomizers to 128 bits
- [VCVio](https://github.com/Verified-zkEVM/VCV-io): formally verified cryptography proofs in Lean 4
