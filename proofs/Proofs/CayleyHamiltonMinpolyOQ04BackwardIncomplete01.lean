import Mathlib.LinearAlgebra.Matrix.Charpoly.Minpoly
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.Tactic

/-
# Nonderogatory → Cyclic Vector: the Irreducible Minimal Polynomial Case

## Research Problem: cayley-hamilton-minpoly-oq-04-backward-incomplete-01

The parent file `CayleyHamiltonMinpolyOQ04Backward` proves the backward direction of
the nonderogatory ⇔ cyclic-vector equivalence over infinite fields, *except* for the
main theorem `nonderogatory_has_cyclic_vector_infinite`, which is left as a `sorry`.
The documented obstruction is an import conflict: the general proof needs the
`normalizedFactors` (unique factorization) API, whose import breaks `DecidableEq`
instance resolution for the existing proofs in that file.

This file makes concrete progress by completing the theorem in the important special
case where the minimal polynomial is **irreducible** — which needs no factorization
machinery at all, only Bézout/gcd. In this case the conclusion is even stronger:
**every nonzero vector is cyclic**.

(The file is fully self-contained: the parent currently does not compile against the
present Mathlib toolchain, so the needed definitions and the gcd/Bézout lemma are
reproved here rather than imported.)

## Main results

* `cyclic_of_irreducible_minpoly` — if `minpoly K M` is irreducible and has degree `n`,
  then every nonzero `v` is a cyclic vector.
* `nonderogatory_irreducible_cyclic` — same, phrased via `IsNonderogatory`.
* `exists_cyclic_of_nonderogatory_irreducible` — existence of a cyclic vector (`n > 0`).

### Idea

If `p(M)v = 0` for nonzero `p` with `deg p < n`, then `d = gcd(p, μ)` divides `μ` and
`d(M)v = 0` (Bézout). Because `μ` is irreducible and `μ ∤ p` (degrees), `d` is a
**unit**, so `d(M)` is invertible; `d(M)v = 0` then forces `v = 0`. Hence the only `p`
annihilating a nonzero `v` is `p = 0`.

This removes the parent's cyclic-vector axiom for every nonderogatory matrix with
irreducible minimal polynomial — e.g. companion matrices of irreducible polynomials,
and matrices with irreducible characteristic polynomial.

## Status (0 axioms, 0 sorries)
-/

set_option linter.unusedVariables false

namespace CayleyHamiltonMinpolyOQ04BackwardInc01

open Matrix Polynomial

variable {K : Type*} [Field K] {n : ℕ}

/-- A vector `v` is a cyclic vector for `M` if no nonzero polynomial of degree `< n`
    annihilates `v` under `M`. -/
def IsCyclicVector (M : Matrix (Fin n) (Fin n) K) (v : Fin n → K) : Prop :=
  ∀ p : K[X], p.natDegree < n → (aeval M p).mulVec v = 0 → p = 0

/-- A matrix is nonderogatory if `minpoly = charpoly`. -/
def IsNonderogatory (M : Matrix (Fin n) (Fin n) K) : Prop :=
  minpoly K M = M.charpoly

/-- **GCD annihilation (Bézout).** If `p(M)v = 0`, then `gcd(p, minpoly M)(M)v = 0`.
    From `gcd = a·p + b·μ`, both `p(M)v = 0` and `μ(M) = 0`. -/
theorem gcd_aeval_mulVec_eq_zero [DecidableEq K[X]] {M : Matrix (Fin n) (Fin n) K}
    {p : K[X]} {v : Fin n → K}
    (hp_ann : (aeval M p).mulVec v = 0) :
    (aeval M (EuclideanDomain.gcd p (minpoly K M))).mulVec v = 0 := by
  set μ := minpoly K M with hμ
  have bezout : EuclideanDomain.gcd p μ
      = EuclideanDomain.gcdA p μ * p + EuclideanDomain.gcdB p μ * μ := by
    rw [EuclideanDomain.gcd_eq_gcd_ab p μ]; ring
  have hμ_ann : (aeval M μ : Matrix (Fin n) (Fin n) K) = 0 := minpoly.aeval K M
  calc (aeval M (EuclideanDomain.gcd p μ)).mulVec v
      = (aeval M (EuclideanDomain.gcdA p μ * p +
          EuclideanDomain.gcdB p μ * μ)).mulVec v := by rw [bezout]
    _ = ((aeval M (EuclideanDomain.gcdA p μ * p)) +
         (aeval M (EuclideanDomain.gcdB p μ * μ))).mulVec v := by rw [map_add]
    _ = (aeval M (EuclideanDomain.gcdA p μ * p)).mulVec v +
        (aeval M (EuclideanDomain.gcdB p μ * μ)).mulVec v := Matrix.add_mulVec _ _ _
    _ = (aeval M (EuclideanDomain.gcdA p μ) * aeval M p).mulVec v +
        (aeval M (EuclideanDomain.gcdB p μ) * aeval M μ).mulVec v := by rw [map_mul, map_mul]
    _ = (aeval M (EuclideanDomain.gcdA p μ)).mulVec ((aeval M p).mulVec v) +
        (aeval M (EuclideanDomain.gcdB p μ)).mulVec ((aeval M μ).mulVec v) := by
        rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
    _ = 0 := by simp [hp_ann, hμ_ann, Matrix.zero_mulVec, Matrix.mulVec_zero]

/-- **Irreducible minimal polynomial ⟹ every nonzero vector is cyclic.**
    If `minpoly K M` is irreducible of degree `n`, then for any `v ≠ 0` and any nonzero
    `p` of degree `< n`, `p(M)v ≠ 0`; i.e. `v` is a cyclic vector. -/
theorem cyclic_of_irreducible_minpoly [DecidableEq K[X]]
    (M : Matrix (Fin n) (Fin n) K)
    (hirr : Irreducible (minpoly K M))
    (hdeg : (minpoly K M).natDegree = n)
    {v : Fin n → K} (hv : v ≠ 0) :
    IsCyclicVector M v := by
  intro p hp hann
  by_contra hp0
  set μ := minpoly K M with hμ
  set d := EuclideanDomain.gcd p μ with hd
  have hdvd_p : d ∣ p := EuclideanDomain.gcd_dvd_left p μ
  have hdvd_μ : d ∣ μ := EuclideanDomain.gcd_dvd_right p μ
  -- μ ∤ p since deg p < deg μ = n and p ≠ 0
  have hnμp : ¬ μ ∣ p := by
    intro h
    have := Polynomial.natDegree_le_of_dvd h hp0
    rw [hdeg] at this; omega
  -- d is a unit: d ∣ μ irreducible, and d ~ μ would force μ ∣ p
  have hd_unit : IsUnit d := by
    obtain ⟨e, he⟩ := hdvd_μ
    rcases hirr.isUnit_or_isUnit he with hdu | heu
    · exact hdu
    · exfalso
      have hassoc : Associated d μ := ⟨heu.unit, by rw [heu.unit_spec]; exact he.symm⟩
      exact hnμp (hassoc.symm.dvd.trans hdvd_p)
  -- d(M)v = 0 by Bézout, and d(M) is invertible, so v = 0
  have hdv : (aeval M d).mulVec v = 0 := gcd_aeval_mulVec_eq_zero hann
  obtain ⟨u, hu⟩ := hd_unit.map (aeval M)
  have key : v = 0 := by
    have hB : Units.val u⁻¹ * Units.val u = (1 : Matrix (Fin n) (Fin n) K) := u.inv_mul
    have huv : Units.val u *ᵥ v = 0 := by rw [hu]; exact hdv
    calc v = (1 : Matrix (Fin n) (Fin n) K) *ᵥ v := (Matrix.one_mulVec v).symm
      _ = (Units.val u⁻¹ * Units.val u) *ᵥ v := by rw [hB]
      _ = Units.val u⁻¹ *ᵥ (Units.val u *ᵥ v) := by rw [Matrix.mulVec_mulVec]
      _ = Units.val u⁻¹ *ᵥ 0 := by rw [huv]
      _ = 0 := Matrix.mulVec_zero _
  exact hv key

/-- Same statement phrased through `IsNonderogatory` (`minpoly K M = charpoly M`),
    which supplies `deg = n` automatically. -/
theorem nonderogatory_irreducible_cyclic [DecidableEq K[X]]
    (M : Matrix (Fin n) (Fin n) K)
    (hnd : IsNonderogatory M) (hirr : Irreducible (minpoly K M))
    {v : Fin n → K} (hv : v ≠ 0) :
    IsCyclicVector M v := by
  have heq : minpoly K M = M.charpoly := hnd
  refine cyclic_of_irreducible_minpoly M hirr ?_ hv
  rw [heq, M.charpoly_natDegree_eq_dim, Fintype.card_fin]

/-- A nonderogatory matrix with irreducible minimal polynomial has a cyclic vector
    (in fact, every nonzero vector is one). This removes the parent's axiom in this
    case. -/
theorem exists_cyclic_of_nonderogatory_irreducible [DecidableEq K[X]]
    (M : Matrix (Fin n) (Fin n) K) (hn : 0 < n)
    (hnd : IsNonderogatory M) (hirr : Irreducible (minpoly K M)) :
    ∃ v, IsCyclicVector M v := by
  haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  haveI : Nontrivial (Fin n → K) := Function.nontrivial
  obtain ⟨v, hv⟩ := exists_ne (0 : Fin n → K)
  exact ⟨v, nonderogatory_irreducible_cyclic M hnd hirr hv⟩

end CayleyHamiltonMinpolyOQ04BackwardInc01
