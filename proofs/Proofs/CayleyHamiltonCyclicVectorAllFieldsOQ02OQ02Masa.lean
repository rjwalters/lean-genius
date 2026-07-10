/-
  The commutant of a nonderogatory matrix is a **maximal commutative subalgebra**
  (cayley-hamilton-cyclic-vector-all-fields-oq-02-oq-02)

  The sibling file `...OQ02OQ02` establishes, for an `n × n` matrix `M` over a
  field `K`, the triple-equivalence headline

      `C(M) = K[M] ⟺ M nonderogatory`,   and   `dim_K C(M) = n` for nonderogatory `M`,

  where `C(M) = Subalgebra.centralizer K {M}` is the commutant.  This file adds the
  structural refinement that makes `C(M)` a **maximal abelian subalgebra (MASA)**:

    * `centralizer_isMaximalCommutative` — for *any* `M`, a commutative subalgebra
      that contains `C(M)` is already equal to `C(M)`.  (Any `a` in such an
      algebra `A` commutes with `M ∈ C(M) ⊆ A`, so `a ∈ C(M)`.)  This needs no
      hypothesis on `M` at all — the commutant is always maximal *among*
      commutative subalgebras that contain it.

    * `centralizer_mul_comm_of_nonderogatory` — for nonderogatory `M`, the commutant
      is itself commutative (it equals `K[M]`, and polynomials in `M` commute).

    * `centralizer_isMASA_of_nonderogatory` (capstone) — for nonderogatory `M`,
      `C(M)` is a commutative subalgebra, is maximal among commutative subalgebras,
      and has `K`-dimension `n`.  In short: the commutant of a nonderogatory matrix
      is a maximal abelian subalgebra of `Mₙ(K)` of the minimal possible dimension.

  All results are `0`-sorry / `0`-axiom on top of Mathlib and the sibling files.
-/
import Mathlib
import Proofs.CayleyHamiltonCyclicVectorAllFieldsOQ02OQ02

open Matrix Polynomial

noncomputable section

namespace CyclicCommutantMasa

open CyclicCommutantDimension

variable {K : Type*} [Field K] {n : ℕ}

/-- `M` lies in its own commutant (it commutes with itself). -/
theorem self_mem_centralizer (M : Matrix (Fin n) (Fin n) K) :
    M ∈ Subalgebra.centralizer K ({M} : Set (Matrix (Fin n) (Fin n) K)) := by
  rw [Subalgebra.mem_centralizer_iff]
  intro g hg
  rw [Set.mem_singleton_iff.mp hg]

/-- **The commutant is maximal among the commutative subalgebras containing it.**
For *any* matrix `M`, if a subalgebra `A` contains the centralizer `C(M)` and is
commutative, then `A = C(M)`.

Reason: every `a ∈ A` commutes with `M` (because `M ∈ C(M) ⊆ A` and `A` is
commutative), so `a ∈ C(M)`; hence `A ⊆ C(M)`, and the reverse inclusion is the
hypothesis. No assumption on `M` is required. -/
theorem centralizer_isMaximalCommutative
    (M : Matrix (Fin n) (Fin n) K)
    (A : Subalgebra K (Matrix (Fin n) (Fin n) K))
    (hCA : Subalgebra.centralizer K ({M} : Set (Matrix (Fin n) (Fin n) K)) ≤ A)
    (hAcomm : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x) :
    A = Subalgebra.centralizer K ({M} : Set (Matrix (Fin n) (Fin n) K)) := by
  refine le_antisymm (fun a ha => ?_) hCA
  rw [Subalgebra.mem_centralizer_iff]
  intro g hg
  rw [Set.mem_singleton_iff.mp hg]
  -- `M ∈ A` and `a ∈ A`, and `A` is commutative, so `M * a = a * M`.
  exact hAcomm M (hCA (self_mem_centralizer M)) a ha

/-- **The commutant of a nonderogatory matrix is commutative.**  For nonderogatory
`M` (`minpoly K M = charpoly M`), any two matrices commuting with `M` commute with
each other: both are polynomials in `M`, and polynomials in a fixed matrix commute.
This is the subalgebra-membership formulation of `CyclicCommutant.commutant_commutative`,
routed through the equality `C(M) = K[M]`. -/
theorem centralizer_mul_comm_of_nonderogatory
    (M : Matrix (Fin n) (Fin n) K) (hM : minpoly K M = M.charpoly)
    {A B : Matrix (Fin n) (Fin n) K}
    (hA : A ∈ Subalgebra.centralizer K ({M} : Set (Matrix (Fin n) (Fin n) K)))
    (hB : B ∈ Subalgebra.centralizer K ({M} : Set (Matrix (Fin n) (Fin n) K))) :
    A * B = B * A := by
  rw [centralizer_eq_adjoin_of_nonderogatory M hM,
    Algebra.adjoin_singleton_eq_range_aeval K M, AlgHom.mem_range] at hA hB
  obtain ⟨p, rfl⟩ := hA
  obtain ⟨q, rfl⟩ := hB
  rw [← map_mul, ← map_mul, mul_comm]

/-- **Capstone: the commutant of a nonderogatory matrix is a maximal abelian
subalgebra (MASA) of minimal dimension.**  For nonderogatory `M` the centralizer
`C(M) = {N : NM = MN}`:

  1. is **commutative**;
  2. is **maximal** among commutative subalgebras (any commutative subalgebra
     containing it equals it); and
  3. has `K`-**dimension `n`** — the smallest a commutant can be (equality in the
     Frobenius bound `dim_K C(M) ≥ n`).

Thus the commutant of a nonderogatory matrix is a maximal abelian subalgebra of
`Mₙ(K)` of dimension `n`. -/
theorem centralizer_isMASA_of_nonderogatory
    (M : Matrix (Fin n) (Fin n) K) (hM : minpoly K M = M.charpoly) :
    (∀ A ∈ Subalgebra.centralizer K ({M} : Set (Matrix (Fin n) (Fin n) K)),
        ∀ B ∈ Subalgebra.centralizer K ({M} : Set (Matrix (Fin n) (Fin n) K)),
          A * B = B * A)
    ∧ (∀ A : Subalgebra K (Matrix (Fin n) (Fin n) K),
        Subalgebra.centralizer K ({M} : Set (Matrix (Fin n) (Fin n) K)) ≤ A →
        (∀ x ∈ A, ∀ y ∈ A, x * y = y * x) →
          A = Subalgebra.centralizer K ({M} : Set (Matrix (Fin n) (Fin n) K)))
    ∧ Module.finrank K
        ↥(Subalgebra.centralizer K ({M} : Set (Matrix (Fin n) (Fin n) K))) = n :=
  ⟨fun _ hA _ hB => centralizer_mul_comm_of_nonderogatory M hM hA hB,
   centralizer_isMaximalCommutative M,
   finrank_centralizer_eq_of_nonderogatory M hM⟩

end CyclicCommutantMasa

end
