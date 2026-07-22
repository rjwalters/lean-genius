/-
  The commutant of a cyclic endomorphism is a maximal abelian subalgebra
  (cayley-hamilton-cyclic-vector-all-fields-oq-02-oq-03)

  This file lifts the MASA (maximal abelian subalgebra) refinement of the
  commutant characterization from concrete matrices
  (`CayleyHamiltonCyclicVectorAllFieldsOQ02OQ02Masa.lean`,
   `CyclicCommutantMasa.centralizer_isMASA_of_nonderogatory`) to the
  coordinate-free endomorphism setting `Module.End K V`.

  ## Statement

  Let `V` be a finite-dimensional `K`-vector space and `T : Module.End K V`
  an endomorphism with a cyclic vector (`IsEndCyclicVector`).  Then the
  centralizer `C(T) = {A | A·T = T·A}` inside `Module.End K V`:

    1. is **commutative** (`end_centralizer_mul_comm_of_cyclic` — the
       subalgebra-membership form of `end_commutant_commutative`);
    2. is **maximal** among commutative subalgebras containing it
       (`end_centralizer_isMaximalCommutative` — this leg needs NO
       hypothesis on `T` at all); and
    3. has `K`-dimension `dim_K V` — the smallest a centralizer can be,
       by the general Frobenius lower bound
       (`finrank_centralizer_eq_of_cyclic`, proved in the Frobenius file).

  The capstone `end_centralizer_isMasa_of_cyclic` packages all three legs:
  the commutant of a cyclic endomorphism is a maximal abelian subalgebra of
  `End_K(V)` of the minimal possible dimension.

  ## Proof

  * Maximality is formal: if `A ⊇ C(T)` is commutative, every `a ∈ A`
    commutes with `T ∈ C(T) ⊆ A`, so `a ∈ C(T)`.
  * Commutativity routes through the subalgebra equality
    `C(T) = K[T] = Algebra.adjoin K {T}` (`end_centralizer_eq_adjoin`):
    two polynomials in `T` commute.
  * The dimension leg is `finrank_centralizer_eq_of_cyclic` from the
    companion Frobenius file.

  Status: 0 sorries, 0 axioms.
-/
import Mathlib
import Proofs.CayleyHamiltonCyclicVectorAllFieldsOQ02OQ03Frobenius

noncomputable section

namespace EndCyclicCommutant

open Polynomial Module

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]

-- ============================================================
-- SECTION I: the centralizer contains T and is maximal-commutative
-- ============================================================

/-- `T` lies in its own centralizer (it commutes with itself). -/
theorem end_self_mem_centralizer (T : Module.End K V) :
    T ∈ Subalgebra.centralizer K ({T} : Set (Module.End K V)) := by
  rw [Subalgebra.mem_centralizer_iff]
  intro g hg
  rw [Set.mem_singleton_iff.mp hg]

/-- **The centralizer is maximal among the commutative subalgebras containing
    it.**  For *any* endomorphism `T` (no cyclic vector, no finite dimension
    needed): if a subalgebra `A` of `Module.End K V` contains the centralizer
    `C(T)` and is commutative, then `A = C(T)`.

    Reason: every `a ∈ A` commutes with `T` (because `T ∈ C(T) ⊆ A` and `A`
    is commutative), so `a ∈ C(T)`; hence `A ⊆ C(T)`, and the reverse
    inclusion is the hypothesis.  Endomorphism analogue of
    `CyclicCommutantMasa.centralizer_isMaximalCommutative`. -/
theorem end_centralizer_isMaximalCommutative
    (T : Module.End K V) (A : Subalgebra K (Module.End K V))
    (hCA : Subalgebra.centralizer K ({T} : Set (Module.End K V)) ≤ A)
    (hAcomm : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x) :
    A = Subalgebra.centralizer K ({T} : Set (Module.End K V)) := by
  refine le_antisymm (fun a ha => ?_) hCA
  rw [Subalgebra.mem_centralizer_iff]
  intro g hg
  rw [Set.mem_singleton_iff.mp hg]
  exact hAcomm T (hCA (end_self_mem_centralizer T)) a ha

-- ============================================================
-- SECTION II: commutativity, in subalgebra-membership form
-- ============================================================

/-- **The centralizer of a cyclic endomorphism is commutative** — membership
    form.  Two endomorphisms lying in `C(T)` (as a subalgebra) commute with
    each other: both are polynomials in `T` by the subalgebra equality
    `C(T) = K[T]`.  This is `end_commutant_commutative` restated for
    subalgebra membership, the form the MASA capstone consumes. -/
theorem end_centralizer_mul_comm_of_cyclic [FiniteDimensional K V]
    (T : Module.End K V) (v : V) (hcyc : IsEndCyclicVector T v)
    {A B : Module.End K V}
    (hA : A ∈ Subalgebra.centralizer K ({T} : Set (Module.End K V)))
    (hB : B ∈ Subalgebra.centralizer K ({T} : Set (Module.End K V))) :
    A * B = B * A := by
  rw [end_centralizer_eq_adjoin T v hcyc,
    Algebra.adjoin_singleton_eq_range_aeval K T, AlgHom.mem_range] at hA hB
  obtain ⟨p, rfl⟩ := hA
  obtain ⟨q, rfl⟩ := hB
  rw [← map_mul, ← map_mul, mul_comm]

-- ============================================================
-- SECTION III: capstone — C(T) is a MASA of minimal dimension
-- ============================================================

/-- **Capstone: the commutant of a cyclic endomorphism is a maximal abelian
    subalgebra of minimal dimension.**  For `T : Module.End K V` with a cyclic
    vector, the centralizer `C(T)`:

      1. is **commutative**;
      2. is **maximal** among commutative subalgebras (any commutative
         subalgebra containing it equals it); and
      3. has `K`-**dimension `dim_K V`** — the smallest possible, being the
         equality case of the Frobenius bound `dim_K C(T) ≥ dim_K V`.

    Coordinate-free lift of
    `CyclicCommutantMasa.centralizer_isMASA_of_nonderogatory`. -/
theorem end_centralizer_isMasa_of_cyclic [FiniteDimensional K V]
    (T : Module.End K V) (v : V) (hcyc : IsEndCyclicVector T v) :
    (∀ A ∈ Subalgebra.centralizer K ({T} : Set (Module.End K V)),
        ∀ B ∈ Subalgebra.centralizer K ({T} : Set (Module.End K V)),
          A * B = B * A)
    ∧ (∀ A : Subalgebra K (Module.End K V),
        Subalgebra.centralizer K ({T} : Set (Module.End K V)) ≤ A →
        (∀ x ∈ A, ∀ y ∈ A, x * y = y * x) →
          A = Subalgebra.centralizer K ({T} : Set (Module.End K V)))
    ∧ Module.finrank K
        (Subalgebra.centralizer K ({T} : Set (Module.End K V)))
      = Module.finrank K V :=
  ⟨fun _ hA _ hB => end_centralizer_mul_comm_of_cyclic T v hcyc hA hB,
   end_centralizer_isMaximalCommutative T,
   finrank_centralizer_eq_of_cyclic T v hcyc⟩

end EndCyclicCommutant

end
