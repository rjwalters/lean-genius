import Proofs.Erdos85SymmetricSectorFactorization
import Proofs.Erdos85PositiveExcessQuotientTrace
import Proofs.Erdos85FrequencyPairTransport
import Proofs.Erdos85NonprincipalCharpoly

/-!
# The principal defect sector carries the component quotient trace

For a `k`-regular defect graph `D`, the `k`-eigenspace of its adjacency
operator over `ℚ` is exactly the span of the connected-component indicator
vectors: a `k`-eigenvector attains its maximum on each component, and
`k`-regularity propagates the maximum across every edge, so eigenvectors
are constant on components.

Under the equitability of the component partition (the commuting relation
with the ambient adjacency matrix), the ambient adjacency operator acts on
the indicator basis through the integral component quotient matrix.  Hence
the trace of its restriction to the principal sector
`ker (aeval T (X - k))` is the quotient trace `∑ c, Q c c` — the quantity
the positive-excess weighted trace identity evaluates to `d`.

The file also records the rational versions of the second-order defect
identities and the `toLin'` transport helpers used by the engine.
-/

open Polynomial
open scoped Matrix

namespace Erdos85

open SimpleGraph

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ## `toLin'` transport helpers -/

/-- The trace of `toLin'` is the matrix trace. -/
theorem trace_toLin'_eq_matrix_trace (M : Matrix V V ℚ) :
    LinearMap.trace ℚ (V → ℚ) (Matrix.toLin' M) = Matrix.trace M := by
  rw [LinearMap.trace_eq_matrix_trace ℚ (Pi.basisFun ℚ V),
    LinearMap.toMatrix_eq_toMatrix', LinearMap.toMatrix'_toLin']

/-- The characteristic polynomial of `toLin'` is the matrix characteristic
polynomial. -/
theorem charpoly_toLin'_eq (M : Matrix V V ℚ) :
    (Matrix.toLin' M).charpoly = M.charpoly := by
  rw [← LinearMap.charpoly_toMatrix (Matrix.toLin' M) (Pi.basisFun ℚ V),
    LinearMap.toMatrix_eq_toMatrix', LinearMap.toMatrix'_toLin']

/-- Polynomial evaluation commutes with `toLin'`. -/
theorem aeval_toLin' (M : Matrix V V ℚ) (p : ℚ[X]) :
    Polynomial.aeval (Matrix.toLin' M) p = Matrix.toLin' (Polynomial.aeval M p) := by
  have hEq : ∀ N : Matrix V V ℚ, Matrix.toLin' N = Matrix.toLinAlgEquiv' N := by
    intro N
    apply LinearMap.ext
    intro v
    rw [Matrix.toLin'_apply, Matrix.toLinAlgEquiv'_apply]
  calc
    Polynomial.aeval (Matrix.toLin' M) p =
        Polynomial.aeval (Matrix.toLinAlgEquiv' M) p := by rw [hEq]
    _ = Matrix.toLinAlgEquiv' (Polynomial.aeval M p) := by
        simpa using Polynomial.aeval_algHom_apply
          (Matrix.toLinAlgEquiv' (n := V) (R := ℚ)).toAlgHom M p
    _ = Matrix.toLin' (Polynomial.aeval M p) := (hEq _).symm

/-- Kernel membership for a linear sector of `toLin'`. -/
theorem mem_ker_aeval_toLin'_X_sub_C_iff (M : Matrix V V ℚ) (k : ℚ)
    (v : V → ℚ) :
    v ∈ LinearMap.ker (Polynomial.aeval (Matrix.toLin' M) (X - C k)) ↔
      M.mulVec v = k • v := by
  rw [LinearMap.mem_ker, aeval_X_sub_C_eq, LinearMap.sub_apply,
    LinearMap.smul_apply, Module.End.one_apply, sub_eq_zero,
    Matrix.toLin'_apply]

/-! ## Rational identity pack -/

/-- The all-ones matrix over `ℚ`. -/
def ratOnesMatrix (V : Type*) : Matrix V V ℚ := Matrix.of fun _ _ => 1

theorem onesMatrix_map_ratCast :
    (FriendshipTheoremOQ01.onesMatrix V).map (Int.castRingHom ℚ) =
      ratOnesMatrix V := by
  ext x y
  simp [FriendshipTheoremOQ01.onesMatrix, ratOnesMatrix, Matrix.map_apply]

/-- Commutation of adjacency and defect matrices over `ℚ`. -/
theorem adjMatrix_comm_secondOrderDefect_of_regular_rat
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {d : ℕ}
    (hreg : ∀ x, G.degree x = d) :
    G.adjMatrix ℚ * (secondOrderDefectGraph G).adjMatrix ℚ =
      (secondOrderDefectGraph G).adjMatrix ℚ * G.adjMatrix ℚ := by
  have hz := adjMatrix_comm_secondOrderDefect_of_regular G hfree hreg
  have h := congrArg (fun M ↦ M.map (Int.castRingHom ℚ)) hz
  simpa only [Matrix.map_mul, adjMatrix_map_intCast] using h

/-- The second-order defect identity over `ℚ`. -/
theorem adjMatrix_sq_eq_sub_secondOrderDefect_of_regular_rat
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {d : ℕ}
    (hreg : ∀ x, G.degree x = d) :
    G.adjMatrix ℚ * G.adjMatrix ℚ =
      ((d : ℚ) - 1) • (1 : Matrix V V ℚ) + ratOnesMatrix V -
        (secondOrderDefectGraph G).adjMatrix ℚ := by
  have hz := adjMatrix_sq_eq_sub_secondOrderDefect_of_regular G hfree hreg
  have h := congrArg (fun M ↦ M.map (Int.castRingHom ℚ)) hz
  simp only [Matrix.map_mul, adjMatrix_map_intCast] at h
  rw [h]
  ext x y
  simp only [Matrix.map_apply, Matrix.sub_apply, Matrix.add_apply,
    Matrix.smul_apply, Matrix.one_apply, Matrix.of_apply,
    FriendshipTheoremOQ01.onesMatrix, ratOnesMatrix,
    SimpleGraph.adjMatrix_apply, smul_eq_mul]
  split_ifs <;> simp only [eq_intCast] <;> push_cast <;> ring

/-- A regular graph's column sums against the all-ones matrix over `ℚ`. -/
theorem ratOnesMatrix_mul_adjMatrix_of_regular
    (H : SimpleGraph V) [DecidableRel H.Adj] {k : ℕ}
    (hreg : ∀ x, H.degree x = k) :
    ratOnesMatrix V * H.adjMatrix ℚ = (k : ℚ) • ratOnesMatrix V := by
  have hz := onesMatrix_mul_adjMatrix_of_regular H k hreg
  have h := congrArg (fun M ↦ M.map (Int.castRingHom ℚ)) hz
  rw [Matrix.map_mul, onesMatrix_map_ratCast, adjMatrix_map_intCast] at h
  rw [h]
  ext x y
  simp only [Matrix.map_apply, Matrix.smul_apply,
    FriendshipTheoremOQ01.onesMatrix, ratOnesMatrix, Matrix.of_apply,
    smul_eq_mul, mul_one, eq_intCast]
  norm_cast

/-! ## Eigenvectors of a regular graph at the top eigenvalue -/

/-- **Maximum principle.**  A rational `k`-eigenvector of a `k`-regular
graph is constant on reachability classes. -/
theorem apply_eq_of_mulVec_eq_smul_of_reachable
    (D : SimpleGraph V) [DecidableRel D.Adj]
    {k : ℕ} (hregD : ∀ x, D.degree x = k) {v : V → ℚ}
    (hv : (D.adjMatrix ℚ).mulVec v = (k : ℚ) • v)
    {x y : V} (hxy : D.Reachable x y) : v x = v y := by
  classical
  set s : Finset V := Finset.univ.filter (fun z => D.Reachable x z) with hs
  have hxs : x ∈ s := by simp [hs]
  obtain ⟨x1, hx1s, hmax⟩ := Finset.exists_max_image s v ⟨x, hxs⟩
  have hx1r : D.Reachable x x1 := by
    have := hx1s
    rw [hs, Finset.mem_filter] at this
    exact this.2
  have key : ∀ a, D.Reachable x a → v a = v x1 →
      ∀ b, D.Adj a b → v b = v x1 := by
    intro a hra hva b hab
    have hbs : b ∈ s := by
      rw [hs, Finset.mem_filter]
      exact ⟨Finset.mem_univ b, hra.trans hab.reachable⟩
    have hble : v b ≤ v x1 := hmax b hbs
    by_contra hne
    have hblt : v b < v x1 := lt_of_le_of_ne hble hne
    have hsum : (∑ u ∈ D.neighborFinset a, v u) = (k : ℚ) * v a := by
      have hcf := congrFun hv a
      rw [Pi.smul_apply, smul_eq_mul] at hcf
      rw [← hcf, SimpleGraph.adjMatrix_mulVec_apply]
    have hub : ∀ u ∈ D.neighborFinset a, v u ≤ v x1 := by
      intro u hu
      apply hmax
      rw [hs, Finset.mem_filter]
      exact ⟨Finset.mem_univ u,
        hra.trans ((D.mem_neighborFinset a u).mp hu).reachable⟩
    have hlt : (∑ u ∈ D.neighborFinset a, v u) <
        ∑ _u ∈ D.neighborFinset a, v x1 :=
      Finset.sum_lt_sum hub ⟨b, (D.mem_neighborFinset a b).mpr hab, hblt⟩
    have hcard : (D.neighborFinset a).card = k := by
      rw [D.card_neighborFinset_eq_degree, hregD a]
    rw [hsum, hva, Finset.sum_const, hcard, nsmul_eq_mul] at hlt
    exact lt_irrefl _ hlt
  have hwalk : ∀ (a b : V) (p : D.Walk a b),
      D.Reachable x a → v a = v x1 → v b = v x1 := by
    intro a b p
    induction p with
    | nil => exact fun _ h => h
    | cons hadj q ih =>
        intro hra hva
        exact ih (hra.trans hadj.reachable) (key _ hra hva _ hadj)
  have hvx : v x = v x1 := by
    obtain ⟨p⟩ := hx1r.symm
    exact hwalk x1 x p hx1r rfl
  have hvy : v y = v x1 := by
    have hry : D.Reachable x1 y := hx1r.symm.trans hxy
    obtain ⟨p⟩ := hry
    exact hwalk x1 y p hx1r rfl
  rw [hvx, hvy]

/-! ## The indicator basis of the principal sector -/

/-- Rational component indicator. -/
def ratComponentIndicator (D : SimpleGraph V)
    [DecidableEq D.ConnectedComponent] (c : D.ConnectedComponent) :
    V → ℚ :=
  fun x => if D.connectedComponentMk x = c then 1 else 0

/-- The indicator is a `k`-eigenvector of a `k`-regular graph. -/
theorem adjMatrix_mulVec_ratComponentIndicator
    (D : SimpleGraph V) [DecidableRel D.Adj]
    [DecidableEq D.ConnectedComponent]
    {k : ℕ} (hregD : ∀ x, D.degree x = k) (c : D.ConnectedComponent) :
    (D.adjMatrix ℚ).mulVec (ratComponentIndicator D c) =
      (k : ℚ) • ratComponentIndicator D c := by
  funext x
  rw [SimpleGraph.adjMatrix_mulVec_apply]
  have hconst : ∀ y ∈ D.neighborFinset x,
      ratComponentIndicator D c y = ratComponentIndicator D c x := by
    intro y hy
    have hxy : D.Adj x y := (D.mem_neighborFinset x y).mp hy
    have hcomp :=
      SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj hxy
    unfold ratComponentIndicator
    rw [← hcomp]
  rw [Finset.sum_congr rfl hconst, Finset.sum_const,
    D.card_neighborFinset_eq_degree, hregD x, nsmul_eq_mul]
  rfl

/-- **Principal sector trace.**  For a `k`-regular defect graph in an
equitable commuting pair, the ambient adjacency trace on the sector
`ker (aeval T (X - k))` is the component quotient trace. -/
theorem trace_principal_kerAevalRestrict
    (G D : SimpleGraph V) [DecidableRel G.Adj] [DecidableRel D.Adj]
    [Fintype D.ConnectedComponent] [DecidableEq D.ConnectedComponent]
    {k : ℕ} (hregD : ∀ x, D.degree x = k)
    (hcommR : G.adjMatrix ℝ * D.adjMatrix ℝ =
      D.adjMatrix ℝ * G.adjMatrix ℝ)
    (hcommQ : Matrix.toLin' (G.adjMatrix ℚ) * Matrix.toLin' (D.adjMatrix ℚ) =
      Matrix.toLin' (D.adjMatrix ℚ) * Matrix.toLin' (G.adjMatrix ℚ)) :
    LinearMap.trace ℚ _
        (kerAevalRestrict (Matrix.toLin' (G.adjMatrix ℚ))
          (Matrix.toLin' (D.adjMatrix ℚ)) hcommQ (X - C (k : ℚ))) =
      ∑ c, (componentQuotientMatrix G D c c : ℚ) := by
  classical
  set W := LinearMap.ker
    (Polynomial.aeval (Matrix.toLin' (D.adjMatrix ℚ)) (X - C (k : ℚ)))
    with hWdef
  -- indicators live in the principal sector
  have hmem : ∀ c : D.ConnectedComponent, ratComponentIndicator D c ∈ W := by
    intro c
    rw [hWdef, mem_ker_aeval_toLin'_X_sub_C_iff]
    exact adjMatrix_mulVec_ratComponentIndicator D hregD c
  set fam : D.ConnectedComponent → W :=
    (fun c => ⟨ratComponentIndicator D c, hmem c⟩) with hfam
  have hrepmk : ∀ c : D.ConnectedComponent,
      D.connectedComponentMk (componentRepresentative D c) = c := fun c =>
    (SimpleGraph.ConnectedComponent.mem_supp_iff c _).mp
      (componentRepresentative_mem D c)
  -- linear independence via evaluation at representatives
  have hli : LinearIndependent ℚ fam := by
    apply LinearIndependent.of_comp W.subtype
    have hli0 : LinearIndependent ℚ
        (fun c : D.ConnectedComponent => ratComponentIndicator D c) := by
      rw [Fintype.linearIndependent_iff]
      intro g hg c
      have hcf := congrFun hg (componentRepresentative D c)
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
        ratComponentIndicator, hrepmk c, mul_ite, mul_one, mul_zero,
        Pi.zero_apply, Finset.sum_ite_eq, Finset.mem_univ, if_true] at hcf
      exact hcf
    exact hli0
  -- spanning via constancy on components
  have hspan : ⊤ ≤ Submodule.span ℚ (Set.range fam) := by
    intro w _
    have hweig : (D.adjMatrix ℚ).mulVec (w : V → ℚ) =
        (k : ℚ) • (w : V → ℚ) :=
      (mem_ker_aeval_toLin'_X_sub_C_iff _ _ _).mp w.2
    have hconst : ∀ x : V, (w : V → ℚ) x =
        (w : V → ℚ)
          (componentRepresentative D (D.connectedComponentMk x)) := by
      intro x
      apply apply_eq_of_mulVec_eq_smul_of_reachable D hregD hweig
      exact SimpleGraph.ConnectedComponent.eq.mp
        (hrepmk (D.connectedComponentMk x)).symm
    have hrepr : w = ∑ c,
        ((w : V → ℚ) (componentRepresentative D c)) • fam c := by
      apply Subtype.ext
      have hcoe : ((∑ c,
          ((w : V → ℚ) (componentRepresentative D c)) • fam c : W) :
            V → ℚ) = ∑ c,
          ((w : V → ℚ) (componentRepresentative D c)) •
            (fam c : V → ℚ) := by
        simp
      rw [hcoe]
      funext x
      rw [Finset.sum_apply]
      simp only [Pi.smul_apply, smul_eq_mul, hfam, ratComponentIndicator,
        mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ,
        if_true]
      exact hconst x
    rw [hrepr]
    exact Submodule.sum_mem _ fun c _ => Submodule.smul_mem _ _
      (Submodule.subset_span ⟨c, rfl⟩)
  set B : Module.Basis D.ConnectedComponent ℚ W := Module.Basis.mk hli hspan with hB
  rw [LinearMap.trace_eq_matrix_trace ℚ B]
  -- image of an indicator under the restricted adjacency operator
  have himg : ∀ c, kerAevalRestrict (Matrix.toLin' (G.adjMatrix ℚ))
      (Matrix.toLin' (D.adjMatrix ℚ)) hcommQ (X - C (k : ℚ)) (fam c) =
      ∑ c', (componentQuotientMatrix G D c' c : ℚ) • fam c' := by
    intro c
    apply Subtype.ext
    have hcoe1 : ((kerAevalRestrict (Matrix.toLin' (G.adjMatrix ℚ))
        (Matrix.toLin' (D.adjMatrix ℚ)) hcommQ (X - C (k : ℚ))
          (fam c)) : V → ℚ) =
        (G.adjMatrix ℚ).mulVec (ratComponentIndicator D c) := by
      rw [kerAevalRestrict_coe, hfam, Matrix.toLin'_apply]
    have hcoe2 : ((∑ c',
        (componentQuotientMatrix G D c' c : ℚ) • fam c' : W) : V → ℚ) =
        ∑ c', (componentQuotientMatrix G D c' c : ℚ) •
          (fam c' : V → ℚ) := by
      simp
    rw [hcoe1, hcoe2]
    funext x
    have hx : x ∈ (D.connectedComponentMk x).supp := rfl
    have hQ := componentQuotientMatrix_apply_eq G D k hregD hcommR
      (D.connectedComponentMk x) c hx
    have hsum : ((G.adjMatrix ℚ).mulVec (ratComponentIndicator D c)) x =
        ((componentNeighborFinset G D c x).card : ℚ) := by
      rw [SimpleGraph.adjMatrix_mulVec_apply]
      unfold ratComponentIndicator componentNeighborFinset
      rw [Finset.sum_boole]
    rw [hsum, ← hQ]
    rw [Finset.sum_apply]
    simp only [Pi.smul_apply, smul_eq_mul, hfam, ratComponentIndicator,
      mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ,
      if_true]
  -- matrix entries are the quotient entries
  have hentry : ∀ c' c, LinearMap.toMatrix B B
      (kerAevalRestrict (Matrix.toLin' (G.adjMatrix ℚ))
        (Matrix.toLin' (D.adjMatrix ℚ)) hcommQ (X - C (k : ℚ))) c' c =
      (componentQuotientMatrix G D c' c : ℚ) := by
    intro c' c
    rw [LinearMap.toMatrix_apply]
    have hBc : B c = fam c := by
      rw [hB]
      exact Module.Basis.mk_apply hli hspan c
    rw [hBc, himg c]
    have hfamB : ∀ c'', fam c'' = B c'' := by
      intro c''
      rw [hB]
      exact (Module.Basis.mk_apply hli hspan c'').symm
    simp_rw [hfamB]
    rw [map_sum]
    simp only [map_smul, Module.Basis.repr_self]
    rw [Finsupp.finset_sum_apply]
    simp only [Finsupp.smul_apply, Finsupp.single_apply, smul_eq_mul,
      mul_ite, mul_one, mul_zero]
    rw [Finset.sum_ite_eq' Finset.univ c'
      (fun c'' => (componentQuotientMatrix G D c'' c : ℚ))]
    simp

  rw [Matrix.trace]
  exact Finset.sum_congr rfl fun c _ => by
    rw [Matrix.diag_apply, hentry c c]

end

end Erdos85
