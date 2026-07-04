import Proofs.CayleyHamiltonMinpolyOQ04BackwardIncomplete01
import Mathlib.Tactic

/-
# Cyclic Vectors for a Prime-Power Minimal Polynomial `μ = qᵏ`

## Research Problem: cayley-hamilton-minpoly-oq-04-backward-incomplete-01-oq-02

The parent file `CayleyHamiltonMinpolyOQ04BackwardIncomplete01` proves that when
`minpoly K M` is **irreducible** of full degree `n`, *every nonzero* vector is a cyclic
vector.  The sibling `…OQ01` then upgrades this to a full characterization (`cyclic ↔ v ≠ 0`)
and counts the cyclic vectors over a finite field.

This file handles the **next** case of the primary-decomposition ladder: the minimal
polynomial is a **prime power**, `μ = qᵏ` with `q` irreducible.  Here the irreducible-case
conclusion "every nonzero vector is cyclic" fails; instead the cyclic vectors are exactly
those *not* killed by `qᵏ⁻¹`.

## Main results

* `cyclic_of_qkm1_ne_zero` — if `μ = qᵏ` (`q` irreducible, `deg μ = n`, `k ≥ 1`) and
  `qᵏ⁻¹(M) v ≠ 0`, then `v` is a cyclic vector.
* `qkm1_ne_zero_of_cyclic` — the converse: a cyclic vector is never annihilated by `qᵏ⁻¹`.
* `cyclic_iff_qkm1_ne_zero` — the two directions combined: **`v` is cyclic iff
  `qᵏ⁻¹(M) v ≠ 0`**.  This is the sharp characterization for the prime-power case.

### Idea

`IsCyclicVector M v` says the `M`-order of `v` (its monic annihilator) has degree `≥ n = deg μ`,
i.e. equals `μ` since it always divides `μ`.  When `μ = qᵏ`, the order of `v` is `qʲ` for some
`j ≤ k`, and it equals `qᵏ` iff `qᵏ⁻¹` does not annihilate `v`.

For the substantive direction, suppose `qᵏ⁻¹(M) v ≠ 0` yet some nonzero `p` with `deg p < n`
annihilates `v`.  Let `d = gcd(p, μ)`.  By Bézout (the parent's `gcd_aeval_mulVec_eq_zero`),
`d(M) v = 0`.  Since `d ∣ qᵏ` and `q` is prime, `d` is associated to `qʲ` for some `j ≤ k`.
If `j = k` then `μ = qᵏ ∣ p`, impossible for a nonzero `p` of degree `< deg μ`; hence
`j ≤ k − 1`, so `d ∣ qᵏ⁻¹`.  Writing `qᵏ⁻¹ = e · d` and using that polynomials in `M` commute,
`qᵏ⁻¹(M) v = e(M) (d(M) v) = 0`, contradicting the hypothesis.

This generalizes the irreducible case (`k = 1`): there `qᵏ⁻¹ = q⁰ = 1`, so `qᵏ⁻¹(M) v = v`
and the characterization collapses to `cyclic ↔ v ≠ 0`.

## Status (0 axioms, 0 sorries)
-/

namespace CayleyHamiltonMinpolyOQ04BackwardInc01

open Matrix Polynomial

variable {K : Type*} [Field K] {n : ℕ}

/-- **Prime-power case, hard direction.** If `minpoly K M = qᵏ` with `q` irreducible of full
degree `n` and `k ≥ 1`, then any vector not annihilated by `qᵏ⁻¹` is a cyclic vector. -/
theorem cyclic_of_qkm1_ne_zero [DecidableEq K[X]]
    (M : Matrix (Fin n) (Fin n) K) {q : K[X]} {k : ℕ} (_hk : 0 < k)
    (hirr : Irreducible q) (hμ : minpoly K M = q ^ k)
    (hdeg : (minpoly K M).natDegree = n)
    {v : Fin n → K} (hv : (aeval M (q ^ (k - 1))).mulVec v ≠ 0) :
    IsCyclicVector M v := by
  intro p hp hann
  by_contra hp0
  -- Bézout: gcd(p, μ) annihilates v
  set μ := minpoly K M with hμdef
  set d := EuclideanDomain.gcd p μ with hddef
  have hdv : (aeval M d).mulVec v = 0 := gcd_aeval_mulVec_eq_zero hann
  have hd_dvd_p : d ∣ p := EuclideanDomain.gcd_dvd_left p μ
  have hd_dvd_μ : d ∣ μ := EuclideanDomain.gcd_dvd_right p μ
  -- q is prime, so divisors of qᵏ are associates of qʲ, j ≤ k
  have hqp : Prime q := hirr.prime
  have hd_dvd_qk : d ∣ q ^ k := by rw [← hμ]; exact hd_dvd_μ
  obtain ⟨j, hjk, hassoc⟩ := (dvd_prime_pow hqp k).mp hd_dvd_qk
  -- j ≠ k: otherwise μ = qᵏ ∣ p, impossible for nonzero p of degree < n
  have hjlt : j < k := by
    rcases lt_or_eq_of_le hjk with h | h
    · exact h
    · exfalso
      -- j = k ⟹ q^k ~ d ∣ p ⟹ μ ∣ p ⟹ n ≤ deg p, contradicting deg p < n
      have hμ_dvd_p : μ ∣ p := by
        rw [hμ, ← h]
        exact hassoc.symm.dvd.trans hd_dvd_p
      have := Polynomial.natDegree_le_of_dvd hμ_dvd_p hp0
      rw [hdeg] at this
      omega
  -- hence d ∣ qᵏ⁻¹
  have hd_dvd_qkm1 : d ∣ q ^ (k - 1) :=
    hassoc.dvd.trans (pow_dvd_pow q (Nat.le_sub_one_of_lt hjlt))
  obtain ⟨e, he⟩ := hd_dvd_qkm1
  -- qᵏ⁻¹(M) v = e(M) (d(M) v) = 0, contradicting hv
  apply hv
  have hcomm : q ^ (k - 1) = e * d := by rw [he]; ring
  rw [hcomm, map_mul, ← Matrix.mulVec_mulVec, hdv, Matrix.mulVec_zero]

/-- **Prime-power case, easy direction.** A cyclic vector is never annihilated by `qᵏ⁻¹`
(when `q` is non-constant and `deg μ = n`): `qᵏ⁻¹` is a nonzero polynomial of degree
`(k−1)·deg q < k·deg q = n`, so if it annihilated the cyclic `v` it would have to be `0`. -/
theorem qkm1_ne_zero_of_cyclic [DecidableEq K[X]]
    (M : Matrix (Fin n) (Fin n) K) {q : K[X]} {k : ℕ} (hk : 0 < k)
    (hirr : Irreducible q) (hμ : minpoly K M = q ^ k)
    (hdeg : (minpoly K M).natDegree = n)
    {v : Fin n → K} (hcyc : IsCyclicVector M v) :
    (aeval M (q ^ (k - 1))).mulVec v ≠ 0 := by
  intro hzero
  -- degree bookkeeping: n = k * deg q, and deg (qᵏ⁻¹) = (k−1) * deg q < n
  have hdq : 0 < q.natDegree := hirr.natDegree_pos
  have hn : n = k * q.natDegree := by
    rw [← hdeg, hμ, Polynomial.natDegree_pow]
  have hdeg_lt : (q ^ (k - 1)).natDegree < n := by
    rw [Polynomial.natDegree_pow, hn]
    have hk1 : k - 1 < k := Nat.sub_lt hk one_pos
    exact (Nat.mul_lt_mul_right hdq).mpr hk1
  -- qᵏ⁻¹ ≠ 0 since q ≠ 0
  have hq0 : q ≠ 0 := hirr.ne_zero
  have hpow0 : q ^ (k - 1) ≠ 0 := pow_ne_zero _ hq0
  exact hpow0 (hcyc _ hdeg_lt hzero)

/-- **Sharp characterization (prime-power minimal polynomial).** With `minpoly K M = qᵏ`
(`q` irreducible, `deg μ = n`, `k ≥ 1`), a vector is cyclic **iff** it is not annihilated by
`qᵏ⁻¹`.  For `k = 1` this is exactly the irreducible-case result `cyclic ↔ v ≠ 0`. -/
theorem cyclic_iff_qkm1_ne_zero [DecidableEq K[X]]
    (M : Matrix (Fin n) (Fin n) K) {q : K[X]} {k : ℕ} (hk : 0 < k)
    (hirr : Irreducible q) (hμ : minpoly K M = q ^ k)
    (hdeg : (minpoly K M).natDegree = n)
    (v : Fin n → K) :
    IsCyclicVector M v ↔ (aeval M (q ^ (k - 1))).mulVec v ≠ 0 :=
  ⟨fun hcyc => qkm1_ne_zero_of_cyclic M hk hirr hμ hdeg hcyc,
   fun hv => cyclic_of_qkm1_ne_zero M hk hirr hμ hdeg hv⟩

end CayleyHamiltonMinpolyOQ04BackwardInc01

#print axioms CayleyHamiltonMinpolyOQ04BackwardInc01.cyclic_of_qkm1_ne_zero
#print axioms CayleyHamiltonMinpolyOQ04BackwardInc01.qkm1_ne_zero_of_cyclic
#print axioms CayleyHamiltonMinpolyOQ04BackwardInc01.cyclic_iff_qkm1_ne_zero
