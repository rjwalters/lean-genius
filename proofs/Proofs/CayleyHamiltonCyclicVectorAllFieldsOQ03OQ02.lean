/-
  Closing the operator cyclic-vector bridge to a biconditional
  (cayley-hamilton-cyclic-vector-all-fields-oq-03-oq-02)

  The main OQ-03 file (`CayleyHamiltonCyclicVectorAllFieldsOQ03.lean`) proves one
  half of the span-form bridge:

      `IsCyclicVectorOp T v  →  cyclicSubspace T v = ⊤`

  (`CyclicVectorOperator.cyclicSubspace_eq_top_of_isCyclicVectorOp`), where
  `IsCyclicVectorOp` is the annihilator-free notion "no nonzero polynomial of
  degree `< finrank K V` kills `v`" and `NonderogatoryModule.cyclicSubspace T v`
  is the span of the full Krylov orbit `{Tᵏ v : k}`.

  This companion supplies the **missing converse**, upgrading the one-way bridge
  to a full biconditional:

      `IsCyclicVectorOp T v  ↔  cyclicSubspace T v = ⊤`.

  The point worth making is that the equivalence holds for an **arbitrary**
  operator `T` — nonderogatority of `T` is not assumed anywhere. The two a-priori
  different definitions of "`v` is a cyclic vector for `T`" therefore coincide on
  every finite-dimensional space.

  ## Contents

  * `pow_mem_span_krylov_of_monic_annihilator` — the reduction engine: if a monic
    polynomial `q` of degree `d` annihilates `v`, then every Krylov vector
    `Tᵏ v` (all `k`) lies in the span of the first `d` of them
    `{Tⁱ v : i < d}`. (This generalises the merged
    `NonderogatoryModule.cyclicSubspace_le_minpoly_degree`, which is the special
    case `q = minpoly K T`, to any monic annihilator of `v`.)
  * `cyclicSubspace_le_span_krylov_of_annihilator` — from any nonzero (not
    necessarily monic) `p` annihilating `v`: the whole cyclic subspace is
    contained in the span of `{Tⁱ v : i < p.natDegree}`. Proof normalises `p` to
    a monic polynomial of the same degree and applies the engine.
  * `isCyclicVectorOp_of_cyclicSubspace_eq_top` — **the converse.** If the Krylov
    orbit spans `V`, then no nonzero polynomial of degree `< finrank K V`
    annihilates `v`: such a `p` would trap the whole space inside the span of
    fewer than `finrank K V` vectors, forcing `finrank K V ≤ p.natDegree`, a
    contradiction.
  * `isCyclicVectorOp_iff_cyclicSubspace_eq_top` — the biconditional, combining
    the merged forward direction with the converse above.
  * `isCyclicVectorOp_iff_isCyclicVector` — the same statement phrased against
    `NonderogatoryModule.IsCyclicVector` (definitionally `cyclicSubspace = ⊤`),
    identifying the annihilator-free operator notion with the registered
    span-based module notion of a cyclic vector.

  ## Status

  0 sorries, 0 `axiom` declarations. Self-contained over `import Mathlib` plus the
  merged operator (`…OQ03`) and module (`…MinpolyOQ05OQ01OQ03`) developments.
-/

import Mathlib
import Proofs.CayleyHamiltonCyclicVectorAllFieldsOQ03

noncomputable section

namespace CayleyHamiltonCyclicVectorAllFieldsOQ03OQ02

open Polynomial

variable {K : Type*} [Field K]
variable {V : Type*} [AddCommGroup V] [Module K V]

/-! ## The reduction engine

A single monic relation `q(T) v = 0` of degree `d` collapses the entire Krylov
orbit into the span of its first `d` members. This is exactly the mechanism used
by `NonderogatoryModule.cyclicSubspace_le_minpoly_degree` (the case
`q = minpoly K T`); we restate it for an arbitrary monic annihilator of the
*vector* `v`, which is what the degree bookkeeping in the converse needs. -/

/-- If a monic polynomial `q` of degree `d` annihilates `v` (i.e. `q(T) v = 0`),
then every Krylov vector `Tᵏ v` lies in the `K`-span of the first `d` Krylov
vectors `{Tⁱ v : i < d}`.

The base case `T^d v ∈ span` comes from solving the monic relation
`∑_{i≤d} q.coeff i • Tⁱ v = 0` (top coefficient `1`) for `T^d v`; the span of the
first `d` powers is `T`-invariant, so `Tᵏ v` stays inside for every `k ≥ d`
(and trivially for `k < d`). -/
theorem pow_mem_span_krylov_of_monic_annihilator
    (T : Module.End K V) (v : V) (q : K[X]) (d : ℕ)
    (hmonic : q.Monic) (hdeg : q.natDegree = d) (hqv : (aeval T q) v = 0) (k : ℕ) :
    (T ^ k) v ∈ Submodule.span K (Set.range fun i : Fin d => (T ^ (i : ℕ)) v) := by
  set W := Submodule.span K (Set.range fun i : Fin d => (T ^ (i : ℕ)) v) with hW
  -- Base case: `T^d v ∈ W`, from the monic annihilating relation.
  have h_Td : (T ^ d) v ∈ W := by
    have h0 : ∑ i ∈ Finset.range (d + 1), q.coeff i • ((T ^ i) v) = 0 := by
      have happ : (aeval T q) v = 0 := hqv
      rw [aeval_eq_sum_range, LinearMap.sum_apply] at happ
      rw [← hdeg]
      simpa only [LinearMap.smul_apply] using happ
    rw [Finset.sum_range_succ] at h0
    have hcoeff : q.coeff d = 1 := by rw [← hdeg]; exact hmonic.coeff_natDegree
    rw [hcoeff, one_smul] at h0
    have hmem : (∑ i ∈ Finset.range d, q.coeff i • ((T ^ i) v)) ∈ W :=
      Submodule.sum_mem W fun i hi =>
        W.smul_mem _ (Submodule.subset_span ⟨⟨i, Finset.mem_range.mp hi⟩, rfl⟩)
    have hTd : (T ^ d) v = -(∑ i ∈ Finset.range d, q.coeff i • ((T ^ i) v)) := by
      have h := congrArg (· - (∑ i ∈ Finset.range d, q.coeff i • ((T ^ i) v))) h0
      simpa using h
    rw [hTd]
    exact W.neg_mem hmem
  -- `W` is `T`-invariant.
  have hT_inv : ∀ w ∈ W, T w ∈ W := by
    intro w hw
    refine Submodule.span_induction (p := fun x _ => T x ∈ W) ?_ ?_ ?_ ?_ hw
    · rintro _ ⟨⟨i, hi⟩, rfl⟩
      have step : T ((T ^ i) v) = (T ^ (i + 1)) v := by
        rw [pow_succ', Module.End.mul_apply]
      rw [step]
      by_cases hi1 : i + 1 < d
      · exact Submodule.subset_span ⟨⟨i + 1, hi1⟩, rfl⟩
      · have hid : i + 1 = d := by omega
        rw [hid]; exact h_Td
    · show T (0 : V) ∈ W; rw [map_zero]; exact W.zero_mem
    · rintro x y _ _ ihx ihy; rw [map_add]; exact W.add_mem ihx ihy
    · rintro c x _ ih; rw [map_smul]; exact W.smul_mem c ih
  -- Powers `≥ d` stay in `W` by iterating invariance from the base case.
  have hge : ∀ m, d ≤ m → (T ^ m) v ∈ W := by
    intro m hm
    induction hm with
    | refl => exact h_Td
    | @step m _ ih => rw [pow_succ']; exact hT_inv _ ih
  by_cases hk : k < d
  · exact Submodule.subset_span ⟨⟨k, hk⟩, rfl⟩
  · exact hge k (by omega)

/-- If **any** nonzero polynomial `p` annihilates `v`, the whole cyclic subspace
`cyclicSubspace T v` is contained in the span of the first `p.natDegree` Krylov
vectors. Normalise `p` to the monic `q = p * C (leadingCoeff p)⁻¹` of the same
degree (still annihilating `v`, as `aeval T` is linear) and apply the engine. -/
theorem cyclicSubspace_le_span_krylov_of_annihilator
    (T : Module.End K V) (v : V) (p : K[X]) (hp0 : p ≠ 0) (hpv : (aeval T p) v = 0) :
    NonderogatoryModule.cyclicSubspace T v ≤
      Submodule.span K (Set.range fun i : Fin p.natDegree => (T ^ (i : ℕ)) v) := by
  set q := p * C (p.leadingCoeff)⁻¹ with hq
  have hqmonic : q.Monic := monic_mul_leadingCoeff_inv hp0
  have hqdeg : q.natDegree = p.natDegree := natDegree_mul_leadingCoeff_inv p hp0
  have hqv : (aeval T q) v = 0 := by
    rw [hq, map_mul, Module.End.mul_apply, aeval_C, Module.algebraMap_end_apply, map_smul, hpv,
      smul_zero]
  rw [show NonderogatoryModule.cyclicSubspace T v
        = Submodule.span K (Set.range fun k : ℕ => (T ^ k) v) from rfl, Submodule.span_le]
  rintro _ ⟨k, rfl⟩
  rw [SetLike.mem_coe]
  exact pow_mem_span_krylov_of_monic_annihilator T v q p.natDegree hqmonic hqdeg hqv k

/-! ## The converse and the biconditional -/

/-- **Converse of the span-form bridge.** If the Krylov orbit of `v` spans the
whole space (`cyclicSubspace T v = ⊤`), then `v` is cyclic in the
annihilator-free sense: no nonzero polynomial of degree `< finrank K V`
annihilates `v`.

Such a `p` would, via `cyclicSubspace_le_span_krylov_of_annihilator`, trap all of
`V = cyclicSubspace T v` inside the span of `p.natDegree < finrank K V` vectors,
forcing `finrank K V ≤ p.natDegree` — impossible. No hypothesis on `T` (such as
nonderogatority) is used. -/
theorem isCyclicVectorOp_of_cyclicSubspace_eq_top [FiniteDimensional K V]
    (T : Module.End K V) (v : V) (h : NonderogatoryModule.cyclicSubspace T v = ⊤) :
    CyclicVectorOperator.IsCyclicVectorOp T v := by
  intro p hpdeg hpv
  by_contra hp0
  have hle := cyclicSubspace_le_span_krylov_of_annihilator T v p hp0 hpv
  rw [h] at hle
  have htop : Submodule.span K (Set.range fun i : Fin p.natDegree => (T ^ (i : ℕ)) v) = ⊤ :=
    top_le_iff.mp hle
  have hcard : Module.finrank K V ≤ Fintype.card (Fin p.natDegree) :=
    finrank_le_of_span_eq_top htop
  rw [Fintype.card_fin] at hcard
  omega

/-- **The span-form bridge as a biconditional.** For any operator `T` on a
finite-dimensional space and any `v`, the annihilator-free notion of cyclicity
(`IsCyclicVectorOp`) is equivalent to the span-based one
(`cyclicSubspace T v = ⊤`). Combines the merged forward direction
`CyclicVectorOperator.cyclicSubspace_eq_top_of_isCyclicVectorOp` with the
converse above. -/
theorem isCyclicVectorOp_iff_cyclicSubspace_eq_top [FiniteDimensional K V]
    (T : Module.End K V) (v : V) :
    CyclicVectorOperator.IsCyclicVectorOp T v ↔
      NonderogatoryModule.cyclicSubspace T v = ⊤ :=
  ⟨CyclicVectorOperator.cyclicSubspace_eq_top_of_isCyclicVectorOp T v,
    isCyclicVectorOp_of_cyclicSubspace_eq_top T v⟩

/-- **Identification of the two cyclic-vector notions.** The annihilator-free
operator notion `IsCyclicVectorOp` coincides with the registered span-based
module notion `NonderogatoryModule.IsCyclicVector` (definitionally
`cyclicSubspace T v = ⊤`) on every finite-dimensional space. -/
theorem isCyclicVectorOp_iff_isCyclicVector [FiniteDimensional K V]
    (T : Module.End K V) (v : V) :
    CyclicVectorOperator.IsCyclicVectorOp T v ↔ NonderogatoryModule.IsCyclicVector T v :=
  isCyclicVectorOp_iff_cyclicSubspace_eq_top T v

end CayleyHamiltonCyclicVectorAllFieldsOQ03OQ02
