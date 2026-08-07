import Proofs.Erdos85InvariantDecomposition
import Proofs.Erdos85EvenCharpolyTrace
import Proofs.Erdos85QuadraticSixTrace
import Mathlib.LinearAlgebra.Projection

/-!
# The canonical spectral projection for a union of triangles

If an endomorphism `D` satisfies `D² = D + 2I`, then `(D+I)/3` projects
onto the `2`-eigenspace along the `-1`-eigenspace.  For the adjacency matrix
of a disjoint union of triangles these are respectively the
component-constant and component-orthogonal spaces.
-/

namespace Erdos85

open LinearMap

variable {E : Type*} [AddCommGroup E] [Module ℚ E]

/-- Projection onto the `2`-eigenspace of a triangle-union operator. -/
noncomputable def trianglePlusProjection (D : E →ₗ[ℚ] E) : E →ₗ[ℚ] E :=
  (3 : ℚ)⁻¹ • (D + LinearMap.id)

theorem trianglePlusProjection_isIdempotent
    (D : E →ₗ[ℚ] E)
    (hD : D * D = D + (2 : ℚ) • LinearMap.id) :
    IsIdempotentElem (trianglePlusProjection D) := by
  rw [IsIdempotentElem]
  ext x
  have happ := LinearMap.congr_fun hD x
  simp only [Module.End.mul_apply, LinearMap.add_apply,
    LinearMap.smul_apply, LinearMap.id_apply] at happ ⊢
  simp only [trianglePlusProjection, LinearMap.smul_apply,
    LinearMap.add_apply, LinearMap.id_apply, map_smul, map_add]
  rw [happ]
  module

/-- Vectors in the range of the triangle projection are `2`-eigenvectors. -/
theorem trianglePlusProjection_apply_eq_two_smul_of_mem_range
    (D : E →ₗ[ℚ] E)
    (hD : D * D = D + (2 : ℚ) • LinearMap.id)
    {x : E} (hx : x ∈ LinearMap.range (trianglePlusProjection D)) :
    D x = 2 • x := by
  obtain ⟨y, rfl⟩ := hx
  have happ := LinearMap.congr_fun hD y
  simp only [Module.End.mul_apply, LinearMap.add_apply,
    LinearMap.smul_apply, LinearMap.id_apply] at happ ⊢
  simp only [trianglePlusProjection, LinearMap.smul_apply,
    LinearMap.add_apply, LinearMap.id_apply]
  rw [map_smul, map_add, happ]
  module

/-- Vectors in the kernel of the triangle projection are `-1`-eigenvectors. -/
theorem trianglePlusProjection_apply_eq_neg_of_mem_ker
    (D : E →ₗ[ℚ] E) {x : E}
    (hx : x ∈ LinearMap.ker (trianglePlusProjection D)) :
    D x = -x := by
  change trianglePlusProjection D x = 0 at hx
  simp only [trianglePlusProjection, LinearMap.smul_apply,
    LinearMap.add_apply, LinearMap.id_apply] at hx
  have hthree : (3 : ℚ) ≠ 0 := by norm_num
  have := (smul_eq_zero.mp hx)
  rcases this with h | h
  · exact (hthree (inv_eq_zero.mp h)).elim
  · exact eq_neg_of_add_eq_zero_left h

/-- The two triangle spectral spaces are complementary. -/
theorem trianglePlusProjection_isCompl
    (D : E →ₗ[ℚ] E)
    (hD : D * D = D + (2 : ℚ) • LinearMap.id) :
    IsCompl (LinearMap.range (trianglePlusProjection D))
      (LinearMap.ker (trianglePlusProjection D)) :=
  LinearMap.IsIdempotentElem.isCompl
    (trianglePlusProjection_isIdempotent D hD)

/-- Any endomorphism commuting with `D` preserves the triangle projection's
range. -/
theorem mapsTo_trianglePlusProjection_range_of_commute
    (A D : E →ₗ[ℚ] E) (hcomm : A * D = D * A) :
    ∀ x ∈ LinearMap.range (trianglePlusProjection D),
      A x ∈ LinearMap.range (trianglePlusProjection D) := by
  rintro _ ⟨y, rfl⟩
  refine ⟨A y, ?_⟩
  simp only [trianglePlusProjection, LinearMap.smul_apply,
    LinearMap.add_apply, LinearMap.id_apply,
    map_smul, map_add]
  have happ := LinearMap.congr_fun hcomm y
  simp only [Module.End.mul_apply] at happ
  rw [happ]

/-- Any endomorphism commuting with `D` preserves the triangle projection's
kernel. -/
theorem mapsTo_trianglePlusProjection_ker_of_commute
    (A D : E →ₗ[ℚ] E) (hcomm : A * D = D * A) :
    ∀ x ∈ LinearMap.ker (trianglePlusProjection D),
      A x ∈ LinearMap.ker (trianglePlusProjection D) := by
  intro x hx
  rw [LinearMap.mem_ker] at hx ⊢
  simp only [trianglePlusProjection, LinearMap.smul_apply,
    LinearMap.add_apply, LinearMap.id_apply,
    map_smul, map_add] at hx ⊢
  have happ := LinearMap.congr_fun hcomm x
  simp only [Module.End.mul_apply] at happ
  rw [← happ, ← map_add, ← map_smul, hx, map_zero]

/-- On the triangle-orthogonal space, the Moore square equation
`A² = 5I + J - D` reduces to `A² = 6I` as soon as the all-ones term vanishes. -/
theorem restrict_trianglePlusProjection_ker_sq_eq_six
    (A D J : E →ₗ[ℚ] E)
    (hcomm : A * D = D * A)
    (hsq : A * A = (5 : ℚ) • LinearMap.id + J - D)
    (hJzero : ∀ x ∈ LinearMap.ker (trianglePlusProjection D), J x = 0) :
    let hW := mapsTo_trianglePlusProjection_ker_of_commute A D hcomm
    (A.restrict hW) * (A.restrict hW) =
      (6 : ℚ) • LinearMap.id := by
  let hW := mapsTo_trianglePlusProjection_ker_of_commute A D hcomm
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  have hs := LinearMap.congr_fun hsq x
  have hDx := trianglePlusProjection_apply_eq_neg_of_mem_ker D x.property
  have hJx := hJzero x x.property
  simp only [Module.End.mul_apply, LinearMap.add_apply, LinearMap.sub_apply,
    LinearMap.smul_apply, LinearMap.id_apply] at hs ⊢
  change A (A x) = 6 • (x : E)
  rw [hs, hJx, hDx]
  module

/-- Convenient form where vanishing of the all-ones operator follows from
`JD=2J`: on the `-1` eigenspace of `D`, this gives `-Jx=2Jx`. -/
theorem restrict_trianglePlusProjection_ker_sq_eq_six_of_J_mul_D
    (A D J : E →ₗ[ℚ] E)
    (hcomm : A * D = D * A)
    (hsq : A * A = (5 : ℚ) • LinearMap.id + J - D)
    (hJD : J * D = (2 : ℚ) • J) :
    let hW := mapsTo_trianglePlusProjection_ker_of_commute A D hcomm
    (A.restrict hW) * (A.restrict hW) =
      (6 : ℚ) • LinearMap.id := by
  apply restrict_trianglePlusProjection_ker_sq_eq_six A D J hcomm hsq
  intro x hx
  have hDx := trianglePlusProjection_apply_eq_neg_of_mem_ker D hx
  have hrel := LinearMap.congr_fun hJD x
  simp only [Module.End.mul_apply, LinearMap.smul_apply] at hrel
  rw [hDx, map_neg] at hrel
  have hthree : (3 : ℚ) • J x = 0 := by
    calc
      (3 : ℚ) • J x = (2 : ℚ) • J x - (-J x) := by module
      _ = 0 := by rw [hrel]; module
  exact (smul_eq_zero.mp hthree).resolve_left (by norm_num)

/-- The trace on the range of the canonical projection can be computed in
the ambient space as `trace (A P)`. -/
theorem trace_restrict_trianglePlusProjection_range_eq_trace_mul
    [FiniteDimensional ℚ E]
    (A D : E →ₗ[ℚ] E)
    (hD : D * D = D + (2 : ℚ) • LinearMap.id)
    (hcomm : A * D = D * A) :
    LinearMap.trace ℚ (LinearMap.range (trianglePlusProjection D))
        (A.restrict
          (mapsTo_trianglePlusProjection_range_of_commute A D hcomm)) =
      LinearMap.trace ℚ E (A * trianglePlusProjection D) := by
  let P := trianglePlusProjection D
  let U := LinearMap.range P
  let W := LinearMap.ker P
  let hAU := mapsTo_trianglePlusProjection_range_of_commute A D hcomm
  have hPidem : IsIdempotentElem P :=
    trianglePlusProjection_isIdempotent D hD
  have hAPU : ∀ x ∈ U, (A * P) x ∈ U := by
    intro x hx
    exact hAU (P x) ⟨x, rfl⟩
  have hAPW : ∀ x ∈ W, (A * P) x ∈ W := by
    intro x hx
    rw [LinearMap.mem_ker] at hx ⊢
    simp only [Module.End.mul_apply, hx, map_zero]
  have hsplit := trace_eq_add_trace_restrict_of_isCompl
    (A * P) U W (trianglePlusProjection_isCompl D hD) hAPU hAPW
  have hUeq : (A * P).restrict hAPU = A.restrict hAU := by
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    simp only [LinearMap.restrict_apply, Module.End.mul_apply]
    obtain ⟨y, hy⟩ := x.property
    have hPx : P x = x := by
      rw [← hy]
      simpa [IsIdempotentElem, Module.End.mul_apply] using
        LinearMap.congr_fun hPidem y
    rw [hPx]
  have hWeq : (A * P).restrict hAPW = 0 := by
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    have hx := x.property
    rw [LinearMap.mem_ker] at hx
    simp [LinearMap.restrict_apply, Module.End.mul_apply, hx]
  rw [hUeq, hWeq] at hsplit
  simpa [U, W, P] using hsplit.symm

/-- Expanding the canonical projection turns its ambient mixed trace into
one third of `trace (A D) + trace A`. -/
theorem trace_mul_trianglePlusProjection
    [FiniteDimensional ℚ E]
    (A D : E →ₗ[ℚ] E) :
    LinearMap.trace ℚ E (A * trianglePlusProjection D) =
      (LinearMap.trace ℚ E (A * D) + LinearMap.trace ℚ E A) / 3 := by
  simp [trianglePlusProjection, mul_add]
  rw [show A * LinearMap.id = A by ext x; rfl]
  ring

/-- Abstract final trace contradiction for the triangle decomposition.  The
graph-specific work only has to identify the trace on the plus space and
certify that the complementary characteristic polynomial is even. -/
theorem false_of_triangle_projection_traces
    [FiniteDimensional ℚ E]
    (A D : E →ₗ[ℚ] E)
    (hD : D * D = D + (2 : ℚ) • LinearMap.id)
    (hcomm : A * D = D * A)
    (htrace : LinearMap.trace ℚ E A = 0)
    (q : ℚ) (hq : q ≠ 0)
    (hplus : LinearMap.trace ℚ (LinearMap.range (trianglePlusProjection D))
        (A.restrict (mapsTo_trianglePlusProjection_range_of_commute A D hcomm)) = q)
    (p : Polynomial ℚ)
    (hchar :
      (A.restrict (mapsTo_trianglePlusProjection_ker_of_commute A D hcomm)).charpoly =
        Polynomial.expand ℚ 2 p)
    (hkerpos : 0 < Module.finrank ℚ
      (LinearMap.ker (trianglePlusProjection D)))
    (hkereven : Even (Module.finrank ℚ
      (LinearMap.ker (trianglePlusProjection D)))) : False := by
  let U := LinearMap.range (trianglePlusProjection D)
  let W := LinearMap.ker (trianglePlusProjection D)
  let hU := mapsTo_trianglePlusProjection_range_of_commute A D hcomm
  let hW := mapsTo_trianglePlusProjection_ker_of_commute A D hcomm
  have hsplit := trace_eq_add_trace_restrict_of_isCompl A U W
    (trianglePlusProjection_isCompl D hD) hU hW
  have hzero : LinearMap.trace ℚ W (A.restrict hW) = 0 :=
    LinearMap.trace_eq_zero_of_charpoly_eq_expand_two
      (A.restrict hW) p hchar hkerpos hkereven
  rw [htrace, hplus, hzero, add_zero] at hsplit
  exact hq hsplit.symm

/-- Sharpened final contradiction for the degree-six triangle case.  The
quadratic identity on the 22-dimensional complementary space supplies its
trace-zero conclusion directly, so no characteristic-polynomial hypothesis
is needed at the graph-facing call site. -/
theorem false_of_triangle_projection_traces_sq_six
    [FiniteDimensional ℚ E]
    (A D : E →ₗ[ℚ] E)
    (hD : D * D = D + (2 : ℚ) • LinearMap.id)
    (hcomm : A * D = D * A)
    (htrace : LinearMap.trace ℚ E A = 0)
    (q : ℚ) (hq : q ≠ 0)
    (hplus : LinearMap.trace ℚ (LinearMap.range (trianglePlusProjection D))
        (A.restrict (mapsTo_trianglePlusProjection_range_of_commute A D hcomm)) = q)
    (hkerfin : Module.finrank ℚ
      (LinearMap.ker (trianglePlusProjection D)) = 22)
    (hkersq :
      let hW := mapsTo_trianglePlusProjection_ker_of_commute A D hcomm
      (A.restrict hW) * (A.restrict hW) =
        (6 : ℚ) • LinearMap.id) : False := by
  let U := LinearMap.range (trianglePlusProjection D)
  let W := LinearMap.ker (trianglePlusProjection D)
  let hU := mapsTo_trianglePlusProjection_range_of_commute A D hcomm
  let hW := mapsTo_trianglePlusProjection_ker_of_commute A D hcomm
  have hsplit := trace_eq_add_trace_restrict_of_isCompl A U W
    (trianglePlusProjection_isCompl D hD) hU hW
  have hzero : LinearMap.trace ℚ W (A.restrict hW) = 0 :=
    LinearMap.trace_eq_zero_of_sq_eq_six_of_finrank_twentyTwo
      (A.restrict hW) hkerfin hkersq
  rw [htrace, hplus, hzero, add_zero] at hsplit
  exact hq hsplit.symm

end Erdos85
