import Mathlib
import Proofs.CayleyHamiltonReductionOQ02OQ01WIP01

/-
# Rational Canonical Form: the coprime (CRT) merge of companion blocks

  cayley-hamilton-cyclic-vector-all-fields-oq-01-oq-02-oq-05
  "Multi-block rational canonical form via the K[X]-module structure theorem."

## What this file adds

The direct-sum of two companion blocks `C(p) ⊕ C(q) = fromBlocks C(p) 0 0 C(q)`
already has, from `Proofs.CayleyHamiltonReductionOQ02OQ01WIP01` (sorry-free):

  * `charpoly_companion_block` :  `charpoly (C(p) ⊕ C(q)) = p · q`      (product)
  * `minpoly_companion_block`  :  `minpoly  (C(p) ⊕ C(q)) = lcm p q`    (lcm)

In general `lcm p q ∣ p · q` strictly, so the block sum is *derogatory*
(`minpoly ≠ charpoly`). The rational canonical form's **elementary-divisor / CRT
decomposition** singles out the case where the two invariant factors are
**coprime**: then `lcm p q = p · q`, the minimal and characteristic polynomials
coincide, and the block sum is **nonderogatory** — i.e. cyclic, hence similar to
the *single* companion matrix `C(p · q)`. This is the matrix incarnation of the
Chinese Remainder Theorem `K[X]/(p·q) ≅ K[X]/(p) × K[X]/(q)` for coprime `p, q`.

This file proves the coprime specialisation:

  * `lcm_eq_mul_of_isCoprime_monic` : for coprime monic `p, q`, `lcm p q = p · q`;
  * `companion_block_coprime_minpoly_eq_charpoly` : `minpoly = charpoly = p · q`;
  * `companion_block_coprime_nonderogatory` : `minpoly (C(p) ⊕ C(q)) = charpoly`.

The last statement is exactly the nonderogatory (cyclic) criterion, from which
the explicit similarity `C(p) ⊕ C(q) ~ C(p·q)` follows via the cyclic-vector
bridge (deferred; it needs the `companionMatrix`-flavoured restatement of
`nonderogatory_iff_similar_to_companion`).

## Build status

VERIFIED. Machine-checked with
`./proofs/scripts/docker-build.sh Proofs.CayleyHamiltonCyclicVectorAllFieldsOQ01OQ02OQ05`
(Mathlib 4.26.0): 0 sorries, no axioms beyond the standard
`propext`/`Classical.choice`/`Quot.sound`. (Originally drafted build-pending during a
tooling blackout; this session adds the `[DecidableEq F]` instance needed for the
`GCDMonoid F[X]` `lcm` lemma, build-verifies the file, and adds the gallery entry.)
-/

namespace CayleyHamiltonCyclicVectorAllFieldsOQ01OQ02OQ05

open Matrix Polynomial
open CayleyHamiltonReductionOQ02OQ01
open CayleyHamiltonReductionOQ02OQ01WIP01

variable {F : Type*} [Field F]

/-- **L5.** For coprime monic polynomials over a field, the least common multiple
is the product. Proof: `lcm p q ∣ p·q` always, and `p·q ∣ lcm p q` because `p, q`
are coprime and both divide `lcm p q` (`IsCoprime.mul_dvd`); both `lcm p q` and
`p·q` are monic, so mutual divisibility forces equality. -/
theorem lcm_eq_mul_of_isCoprime_monic [DecidableEq F] {p q : F[X]}
    (hp : p.Monic) (hq : q.Monic) (h : IsCoprime p q) :
    lcm p q = p * q := by
  have hp0 : p ≠ 0 := hp.ne_zero
  have hq0 : q ≠ 0 := hq.ne_zero
  have hlcm0 : lcm p q ≠ 0 := by
    rw [Ne, lcm_eq_zero_iff]; push_neg; exact ⟨hp0, hq0⟩
  have hlcm_monic : (lcm p q).Monic := by
    rw [← normalize_eq_self_iff_monic hlcm0]; exact normalize_lcm p q
  have hmul_monic : (p * q).Monic := hp.mul hq
  have hd1 : lcm p q ∣ p * q := lcm_dvd (dvd_mul_right p q) (dvd_mul_left q p)
  have hd2 : p * q ∣ lcm p q := h.mul_dvd (dvd_lcm_left p q) (dvd_lcm_right p q)
  exact eq_of_monic_of_associated hlcm_monic hmul_monic (associated_of_dvd_dvd hd1 hd2)

/-- **Coprime (CRT) merge — polynomial readout.**
For coprime monic `p, q`, the block-diagonal companion matrix `C(p) ⊕ C(q)` has
both its minimal polynomial and its characteristic polynomial equal to the
product `p · q`. Combines `minpoly_companion_block` + `charpoly_companion_block`
(from `CayleyHamiltonReductionOQ02OQ01WIP01`) with `lcm_eq_mul_of_isCoprime_monic`. -/
theorem companion_block_coprime_minpoly_eq_charpoly
    {dp dq : ℕ} [NeZero dp] [NeZero dq] [DecidableEq F]
    (p q : F[X]) (hp : p.Monic) (hpd : p.natDegree = dp)
    (hq : q.Monic) (hqd : q.natDegree = dq) (hpq : IsCoprime p q) :
    minpoly F (Matrix.fromBlocks (companionMatrix (d := dp) p) 0 0
        (companionMatrix (d := dq) q)) = p * q
      ∧ (Matrix.fromBlocks (companionMatrix (d := dp) p) 0 0
        (companionMatrix (d := dq) q)).charpoly = p * q := by
  refine ⟨?_, charpoly_companion_block p q hp hpd hq hqd⟩
  rw [minpoly_companion_block p q hp hpd hq hqd, lcm_eq_mul_of_isCoprime_monic hp hq hpq]

/-- **Coprime companion blocks are nonderogatory.**
For coprime monic `p, q`, the block sum `C(p) ⊕ C(q)` satisfies
`minpoly = charpoly`, the defining nonderogatory (cyclic) condition. Hence it is
similar to the single companion matrix `C(p · q)` — the CRT collapse of two
coprime invariant factors into one. -/
theorem companion_block_coprime_nonderogatory
    {dp dq : ℕ} [NeZero dp] [NeZero dq] [DecidableEq F]
    (p q : F[X]) (hp : p.Monic) (hpd : p.natDegree = dp)
    (hq : q.Monic) (hqd : q.natDegree = dq) (hpq : IsCoprime p q) :
    minpoly F (Matrix.fromBlocks (companionMatrix (d := dp) p) 0 0
        (companionMatrix (d := dq) q))
      = (Matrix.fromBlocks (companionMatrix (d := dp) p) 0 0
        (companionMatrix (d := dq) q)).charpoly := by
  obtain ⟨hmin, hchar⟩ :=
    companion_block_coprime_minpoly_eq_charpoly p q hp hpd hq hqd hpq
  rw [hmin, hchar]

end CayleyHamiltonCyclicVectorAllFieldsOQ01OQ02OQ05
