/-
# Erdős Problem #101 — OQ-04: similarity invariance of the lower-bound framework

The parent `Proofs/Erdos101Problem.lean` fixes the elementary objects
`PlanarPointSet`, `collinear`, `NoFiveCollinear`, and `fourPointLineCount`,
and `Proofs/Erdos101OQ04.lean` packages a lower-bound construction as
`Erdos101OQ04.IsLowerBoundConstruction P threshold`
(`NoFiveCollinear P ∧ threshold ≤ fourPointLineCount P`).

The remaining OPEN content of OQ-04 is the Solymosi–Stojaković construction
itself.  Every candidate construction (the `F_p` parabola of Path B, the
projected high-dimensional grid of Path A, or the "fixed sphere"
`{∑x = 0, ∑x² = 10}` reduction already recorded in the file) is naturally
specified only *up to a similarity of the plane*: a construction may be built
around a convenient origin and at a convenient scale and then normalised.

This file supplies that normalisation as reusable, axiom-free infrastructure:
a **plane automorphism** (`Erdos101OQ04.Similarity.PlaneAut`) is a self-bijection
of `ℝ²` given with an explicit two-sided inverse, both directions of which
preserve `collinear`.  Translations and nonzero scalings are the two basic
examples.  The induced action on a `PlanarPointSet` preserves the entire
framework:

* `PlaneAut.map_noFiveCollinear` — the five-collinear obstruction is invariant;
* `PlaneAut.map_fourPointLineCount` — the four-point-line **count is exactly
  preserved** (a `Finset` bijection on collinear 4-subsets, not merely a bound);
* `PlaneAut.map_isLowerBoundConstruction` — hence `IsLowerBoundConstruction`
  transfers verbatim, so a witness may be relocated/rescaled at will.

Concretely `translatePlane v` and `scalePlane c hc` (with `c ≠ 0`) let any
future construction PR place its witness at the origin and normalise its scale
(e.g. move between the spheres `∑x² = c` for different `c > 0`) without
re-proving the no-five-collinear condition or recounting its four-point lines.

Axiom-free (`propext`/`Classical.choice`/`Quot.sound` only), 0 `sorry`.  Does
not touch the single OPEN obligation `solymosi_stojakovic_lower_bound`; it is
orthogonal supporting infrastructure.
-/
import Proofs.Erdos101OQ04

namespace Erdos101OQ04.Similarity

/-- A collinearity-preserving self-bijection of the plane, given with an
explicit two-sided inverse.  Both the map and its inverse preserve
collinearity, so the induced action on point sets preserves the whole
lower-bound framework (`NoFiveCollinear`, `fourPointLineCount`, and hence
`Erdos101OQ04.IsLowerBoundConstruction`). -/
structure PlaneAut where
  /-- The underlying map of the plane. -/
  toFun : ℝ × ℝ → ℝ × ℝ
  /-- Its explicit inverse. -/
  invFun : ℝ × ℝ → ℝ × ℝ
  left_inv : Function.LeftInverse invFun toFun
  right_inv : Function.RightInverse invFun toFun
  map_collinear : ∀ {p q r}, collinear p q r → collinear (toFun p) (toFun q) (toFun r)
  inv_map_collinear :
    ∀ {p q r}, collinear p q r → collinear (invFun p) (invFun q) (invFun r)

namespace PlaneAut

theorem injective (a : PlaneAut) : Function.Injective a.toFun :=
  a.left_inv.injective

theorem inv_injective (a : PlaneAut) : Function.Injective a.invFun :=
  a.right_inv.injective

/-- Collinearity is *characterised* by its image: both directions hold, since the
inverse of a `PlaneAut` is again collinearity-preserving. -/
theorem collinear_iff (a : PlaneAut) {p q r} :
    collinear (a.toFun p) (a.toFun q) (a.toFun r) ↔ collinear p q r := by
  constructor
  · intro h
    have := a.inv_map_collinear h
    simpa only [a.left_inv p, a.left_inv q, a.left_inv r] using this
  · exact a.map_collinear

/-- The induced action of a plane automorphism on a planar point set:
push the finite point set forward through `toFun`. -/
noncomputable def map (a : PlaneAut) (P : PlanarPointSet) : PlanarPointSet where
  points := P.points.image a.toFun
  size_pos := Finset.card_pos.mpr ((Finset.card_pos.mp P.size_pos).image a.toFun)

/-- The no-five-collinear obstruction is invariant under a plane automorphism. -/
theorem map_noFiveCollinear (a : PlaneAut) {P : PlanarPointSet}
    (h : NoFiveCollinear P) : NoFiveCollinear (a.map P) := by
  intro A B C D E hA hB hC hD hE hAB hAC hAD hAE hBC hBD hBE hCD hCE hDE
  simp only [PlaneAut.map, Finset.mem_image] at hA hB hC hD hE
  obtain ⟨a', ha', rfl⟩ := hA
  obtain ⟨b', hb', rfl⟩ := hB
  obtain ⟨c', hc', rfl⟩ := hC
  obtain ⟨d', hd', rfl⟩ := hD
  obtain ⟨e', he', rfl⟩ := hE
  rintro ⟨h1, h2, h3⟩
  exact h a' b' c' d' e' ha' hb' hc' hd' he'
    (mt (congrArg a.toFun) hAB) (mt (congrArg a.toFun) hAC)
    (mt (congrArg a.toFun) hAD) (mt (congrArg a.toFun) hAE)
    (mt (congrArg a.toFun) hBC) (mt (congrArg a.toFun) hBD)
    (mt (congrArg a.toFun) hBE) (mt (congrArg a.toFun) hCD)
    (mt (congrArg a.toFun) hCE) (mt (congrArg a.toFun) hDE)
    ⟨(a.collinear_iff).mp h1, (a.collinear_iff).mp h2, (a.collinear_iff).mp h3⟩

/-- **The four-point-line count is preserved exactly** under a plane
automorphism.  The proof is a `Finset` bijection between the collinear
4-subsets of `P` and those of `a.map P`, given by `S ↦ S.image a.toFun`
with explicit inverse `T ↦ T.image a.invFun`. -/
theorem map_fourPointLineCount (a : PlaneAut) (P : PlanarPointSet) :
    fourPointLineCount (a.map P) = fourPointLineCount P := by
  classical
  have hcomp₁ : a.toFun ∘ a.invFun = id := funext a.right_inv
  have hcomp₂ : a.invFun ∘ a.toFun = id := funext a.left_inv
  unfold fourPointLineCount PlaneAut.map
  apply Finset.card_nbij' (fun S => S.image a.invFun) (fun S => S.image a.toFun)
  · -- forward: an image-side collinear 4-subset pulls back to a P-side one
    intro S hS
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_powerset] at hS ⊢
    obtain ⟨hSsub, hScard, ai, bi, hai, hbi, hab, hcol⟩ := hS
    refine ⟨?_, ?_, a.invFun ai, a.invFun bi, ?_, ?_, ?_, ?_⟩
    · intro x hx
      rw [Finset.mem_image] at hx
      obtain ⟨y, hy, rfl⟩ := hx
      obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp (hSsub hy)
      rw [a.left_inv z]; exact hz
    · rw [Finset.card_image_of_injective _ a.inv_injective, hScard]
    · exact Finset.mem_image_of_mem _ hai
    · exact Finset.mem_image_of_mem _ hbi
    · exact fun h => hab (a.inv_injective h)
    · intro p hp
      rw [Finset.mem_image] at hp
      obtain ⟨q, hq, rfl⟩ := hp
      exact a.inv_map_collinear (hcol q hq)
  · -- backward: a P-side collinear 4-subset pushes forward to an image-side one
    intro T hT
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_powerset] at hT ⊢
    obtain ⟨hTsub, hTcard, ai, bi, hai, hbi, hab, hcol⟩ := hT
    refine ⟨?_, ?_, a.toFun ai, a.toFun bi, ?_, ?_, ?_, ?_⟩
    · exact Finset.image_subset_image hTsub
    · rw [Finset.card_image_of_injective _ a.injective, hTcard]
    · exact Finset.mem_image_of_mem _ hai
    · exact Finset.mem_image_of_mem _ hbi
    · exact fun h => hab (a.injective h)
    · intro p hp
      rw [Finset.mem_image] at hp
      obtain ⟨q, hq, rfl⟩ := hp
      exact a.map_collinear (hcol q hq)
  · -- the two maps are mutually inverse (image side)
    intro S _
    show (S.image a.invFun).image a.toFun = S
    rw [Finset.image_image, hcomp₁, Finset.image_id]
  · -- and on the P side
    intro T _
    show (T.image a.toFun).image a.invFun = T
    rw [Finset.image_image, hcomp₂, Finset.image_id]

/-- **Similarity invariance of the lower-bound framework.**  If `P` is a
lower-bound construction for threshold `t`, so is its image under any plane
automorphism.  The threshold transfers verbatim because both the
no-five-collinear condition and the exact four-point-line count are preserved. -/
theorem map_isLowerBoundConstruction (a : PlaneAut) {P : PlanarPointSet} {t : ℝ}
    (h : IsLowerBoundConstruction P t) : IsLowerBoundConstruction (a.map P) t :=
  ⟨a.map_noFiveCollinear h.1, by rw [a.map_fourPointLineCount]; exact h.2⟩

end PlaneAut

/-- Translation of the plane by a fixed vector `v`; a `PlaneAut`.  Lets a
construction be recentred at any chosen point (e.g. the origin) without
disturbing collinearity. -/
def translatePlane (v : ℝ × ℝ) : PlaneAut where
  toFun p := (p.1 + v.1, p.2 + v.2)
  invFun p := (p.1 - v.1, p.2 - v.2)
  left_inv p := by simp
  right_inv p := by simp
  map_collinear {p q r} h := by
    simp only [collinear] at h ⊢; linear_combination h
  inv_map_collinear {p q r} h := by
    simp only [collinear] at h ⊢; linear_combination h

/-- Scaling of the plane by a nonzero factor `c`; a `PlaneAut`.  Lets a
construction be rescaled (e.g. moved between the spheres `∑x² = c` for
different `c > 0`) without disturbing collinearity. -/
noncomputable def scalePlane (c : ℝ) (hc : c ≠ 0) : PlaneAut where
  toFun p := (c * p.1, c * p.2)
  invFun p := (p.1 / c, p.2 / c)
  left_inv p := by simp [hc]
  right_inv p := by field_simp
  map_collinear {p q r} h := by
    simp only [collinear] at h ⊢; linear_combination c ^ 2 * h
  inv_map_collinear {p q r} h := by
    simp only [collinear] at h ⊢
    field_simp
    linear_combination h

/-- Translating a lower-bound construction preserves it (the threshold is
unchanged). -/
theorem translate_isLowerBoundConstruction (v : ℝ × ℝ) {P : PlanarPointSet}
    {t : ℝ} (h : IsLowerBoundConstruction P t) :
    IsLowerBoundConstruction ((translatePlane v).map P) t :=
  (translatePlane v).map_isLowerBoundConstruction h

/-- Rescaling a lower-bound construction by a nonzero factor preserves it (the
threshold is unchanged). -/
theorem scale_isLowerBoundConstruction (c : ℝ) (hc : c ≠ 0) {P : PlanarPointSet}
    {t : ℝ} (h : IsLowerBoundConstruction P t) :
    IsLowerBoundConstruction ((scalePlane c hc).map P) t :=
  (scalePlane c hc).map_isLowerBoundConstruction h

end Erdos101OQ04.Similarity
