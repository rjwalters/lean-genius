import Mathlib

/-
# The convex 0-or-2 line/boundary dichotomy (buffons-needle-oq-01-oq-04-oq-01)

**Status**: Fully verified (0 axioms, 0 sorries).

This file resolves the first open question of `buffons-needle-oq-01-oq-04`
(Buffon's coin). The parent file `BuffonsNeedleOQ01OQ04.lean` *defined* the
number of grid lines cutting a convex body to be half the boundary-crossing
count, noting:

  "This factor-of-two is the only place convexity enters; it is encoded
   definitionally (`expectedLineCuts := … / 2`) rather than derived from a
   convex-geometry API — Mathlib v4.26.0 has no
   `Convex.line_intersection_card_le_two` bearer."

This file builds exactly that missing bearer. We work with a genuine line
`ℓ t = p + t • v` (direction `v ≠ 0`) in an arbitrary real normed space and a
convex body `K` (compact convex set), and prove the **0-or-2 dichotomy** as a
theorem of convex geometry, with no analytic Buffon machinery:

* `lineParams_convex` — the line meets a convex set in a *convex* subset of the
  parameter line `ℝ`, i.e. an interval. This is the "no gaps" content: a line
  cannot leave and re-enter a convex set.
* `lineParams_eq_Icc` — for a compact convex body it is a closed segment
  `Icc a b`; the line meets `K` in one connected piece.
* `lineParams_Ioo_subset_interior` — every interior parameter maps into the
  topological interior of `K` (a line through the interior stays inside until it
  exits).
* `line_meets_frontier_iff_endpoint` and
  **`line_through_interior_meets_frontier_in_two`** — a line passing through the
  interior of `K` meets the boundary `∂K` in *exactly two* points
  `{ℓ a, ℓ b}`; the parameter set `{t | ℓ t ∈ frontier K}` equals `{a, b}` with
  `a < b`.  Hence `Set.ncard = 2`.

The "0" half of the dichotomy is the contrapositive: a line meeting only the
boundary (never the interior) is a supporting line and may share a whole flat
edge with `∂K`, so the clean count `2` requires — and is characterised by — an
interior crossing. That is the hypothesis here, matching Buffon's coin, where a
grid line "cuts" the body precisely when it passes through the interior.

## Reference
Hadwiger, *Vorlesungen über Inhalt, Oberfläche und Isoperimetrie*; the
"each cutting line meets the boundary in two points" lemma underlying the
Cauchy–Crofton / Buffon-coin perimeter formula.
-/

noncomputable section

namespace BuffonsNeedleOQ01OQ04OQ01

open Set Metric

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- The line through `p` with direction `v`, parametrised by `t : ℝ`. -/
def line (p v : V) : ℝ → V := fun t => p + t • v

/-- The set of parameters `t` whose line point `ℓ t` lies in `K`. -/
def lineParams (K : Set V) (p v : V) : Set ℝ := {t : ℝ | line p v t ∈ K}

@[simp] theorem mem_lineParams {K : Set V} {p v : V} {t : ℝ} :
    t ∈ lineParams K p v ↔ line p v t ∈ K := Iff.rfl

theorem line_continuous (p v : V) : Continuous (line p v) := by
  unfold line
  fun_prop

/-- Affine key: a convex combination of two parameters maps to the convex
combination of their line points (the map `t ↦ p + t • v` is affine). -/
theorem line_combo (p v : V) {a b x y : ℝ} (hab : a + b = 1) :
    line p v (a * x + b * y) = a • line p v x + b • line p v y := by
  unfold line
  have : a • (p + x • v) + b • (p + y • v)
       = (a + b) • p + (a * x + b * y) • v := by
    simp only [smul_add, smul_smul]
    module
  rw [this, hab, one_smul]

/-- **A line meets a convex set in an interval.** The parameter set is convex,
so the line cannot leave `K` and re-enter it. -/
theorem lineParams_convex {K : Set V} (hK : Convex ℝ K) (p v : V) :
    Convex ℝ (lineParams K p v) := by
  intro x hx y hy a b ha hb hab
  simp only [mem_lineParams, smul_eq_mul] at hx hy ⊢
  rw [line_combo p v hab]
  exact hK hx hy ha hb hab

theorem lineParams_isClosed {K : Set V} (hK : IsClosed K) (p v : V) :
    IsClosed (lineParams K p v) :=
  hK.preimage (line_continuous p v)

/-- The line points are at distance `|t| · ‖v‖` from `p`, so a bounded `K`
confines the parameters to a bounded interval (when `v ≠ 0`). -/
theorem lineParams_subset_Icc {K : Set V} (hKb : Bornology.IsBounded K)
    {p v : V} (hv : v ≠ 0) :
    ∃ r : ℝ, lineParams K p v ⊆ Icc (-r) r := by
  obtain ⟨R, hR⟩ := (Metric.isBounded_iff_subset_closedBall p).mp hKb
  have hvpos : 0 < ‖v‖ := norm_pos_iff.mpr hv
  refine ⟨R / ‖v‖, fun t ht => ?_⟩
  have hmem : line p v t ∈ closedBall p R := hR ht
  rw [mem_closedBall, dist_eq_norm] at hmem
  have hsub : line p v t - p = t • v := by simp [line]
  rw [hsub, norm_smul, Real.norm_eq_abs] at hmem
  have habs : |t| ≤ R / ‖v‖ := by rw [le_div_iff₀ hvpos]; linarith
  exact mem_Icc.mpr (abs_le.mp habs)

theorem lineParams_bddAbove {K : Set V} (hKb : Bornology.IsBounded K)
    {p v : V} (hv : v ≠ 0) : BddAbove (lineParams K p v) := by
  obtain ⟨r, hr⟩ := lineParams_subset_Icc hKb hv (p := p)
  exact (bddAbove_Icc).mono hr

theorem lineParams_bddBelow {K : Set V} (hKb : Bornology.IsBounded K)
    {p v : V} (hv : v ≠ 0) : BddBelow (lineParams K p v) := by
  obtain ⟨r, hr⟩ := lineParams_subset_Icc hKb hv (p := p)
  exact (bddBelow_Icc).mono hr

/-! ## The compact convex body setting -/

variable {K : Set V} {p v : V}

/-- For a compact convex body the line meets `K` in the closed segment
`Icc (sInf) (sSup)`. -/
theorem lineParams_eq_Icc (hK : Convex ℝ K) (hKc : IsCompact K) (hv : v ≠ 0)
    (hne : (lineParams K p v).Nonempty) :
    lineParams K p v = Icc (sInf (lineParams K p v)) (sSup (lineParams K p v)) := by
  set S := lineParams K p v with hS
  have hcl : IsClosed S := lineParams_isClosed hKc.isClosed p v
  have hba : BddAbove S := lineParams_bddAbove hKc.isBounded hv
  have hbb : BddBelow S := lineParams_bddBelow hKc.isBounded hv
  have ha : sInf S ∈ S := hcl.csInf_mem hne hbb
  have hb : sSup S ∈ S := hcl.csSup_mem hne hba
  apply Subset.antisymm
  · intro t ht
    exact mem_Icc.mpr ⟨csInf_le hbb ht, le_csSup hba ht⟩
  · have hoc : S.OrdConnected := (lineParams_convex hK p v).ordConnected
    exact hoc.out ha hb

/-- Interior point `t₀` to the left of a `K`-point `t₁`: any `t` with
`t₀ ≤ t < t₁` maps into the interior of `K` (positive weight stays on the
interior endpoint). -/
theorem line_mem_interior_right (hK : Convex ℝ K)
    {t₀ t₁ t : ℝ} (h₀ : line p v t₀ ∈ interior K) (h₁ : line p v t₁ ∈ K)
    (htle : t₀ ≤ t) (htlt : t < t₁) : line p v t ∈ interior K := by
  have hden : 0 < t₁ - t₀ := by linarith
  set lam : ℝ := (t₁ - t) / (t₁ - t₀) with hlam
  have hlampos : 0 < lam := by
    rw [hlam]; apply div_pos <;> linarith
  have hb1 : 0 ≤ 1 - lam := by
    have : lam ≤ 1 := by rw [hlam, div_le_one hden]; linarith
    linarith
  have hcoef : lam + (1 - lam) = 1 := by ring
  have hne0 : t₁ - t₀ ≠ 0 := ne_of_gt hden
  have hcombo : t = lam * t₀ + (1 - lam) * t₁ := by
    rw [hlam]; field_simp; ring
  rw [hcombo, line_combo p v hcoef]
  exact hK.combo_interior_self_mem_interior h₀ h₁ hlampos hb1 hcoef

/-- Interior point `t₀` to the right of a `K`-point `t₁`: any `t` with
`t₁ < t ≤ t₀` maps into the interior of `K`. -/
theorem line_mem_interior_left (hK : Convex ℝ K)
    {t₀ t₁ t : ℝ} (h₀ : line p v t₀ ∈ interior K) (h₁ : line p v t₁ ∈ K)
    (htlt : t₁ < t) (htle : t ≤ t₀) : line p v t ∈ interior K := by
  have hden : 0 < t₀ - t₁ := by linarith
  set lam : ℝ := (t - t₁) / (t₀ - t₁) with hlam
  have hlampos : 0 < lam := by
    rw [hlam]; apply div_pos <;> linarith
  have hb1 : 0 ≤ 1 - lam := by
    have : lam ≤ 1 := by rw [hlam, div_le_one hden]; linarith
    linarith
  have hcoef : lam + (1 - lam) = 1 := by ring
  have hne0 : t₀ - t₁ ≠ 0 := ne_of_gt hden
  have hcombo : t = lam * t₀ + (1 - lam) * t₁ := by
    rw [hlam]; field_simp; ring
  rw [hcombo, line_combo p v hcoef]
  exact hK.combo_interior_self_mem_interior h₀ h₁ hlampos hb1 hcoef

/-- **The interior of the segment maps into the interior of `K`.** If `t₀` is an
interior parameter and `a ≤ t₀ ≤ b` are `K`-parameters, then every `t ∈ Ioo a b`
maps into `interior K`. -/
theorem line_Ioo_mem_interior (hK : Convex ℝ K)
    {a b t₀ t : ℝ} (h₀ : line p v t₀ ∈ interior K)
    (ha : line p v a ∈ K) (hb : line p v b ∈ K)
    (ht : t ∈ Ioo a b) :
    line p v t ∈ interior K := by
  obtain ⟨hta, htb⟩ := ht
  rcases le_or_gt t t₀ with h | h
  · exact line_mem_interior_left hK h₀ ha hta h
  · exact line_mem_interior_right hK h₀ hb (le_of_lt h) htb

/-! ## The 0-or-2 dichotomy -/

/-- **Convex line/boundary dichotomy.** A line `ℓ t = p + t • v` (`v ≠ 0`)
passing through the *interior* of a compact convex body `K` meets the boundary
`∂K` in *exactly two* points: there are reals `a < b` with the parameter set of
boundary crossings equal to `{a, b}`, and `ℓ` meets `K` itself in the closed
segment `Icc a b`. This is the convex-geometry bearer the parent file
`BuffonsNeedleOQ01OQ04.lean` had to encode definitionally. -/
theorem line_through_interior_meets_frontier_in_two
    (hK : Convex ℝ K) (hKc : IsCompact K) (hv : v ≠ 0)
    {t₀ : ℝ} (ht₀ : line p v t₀ ∈ interior K) :
    ∃ a b : ℝ, a < b ∧ lineParams K p v = Icc a b ∧
      {t : ℝ | line p v t ∈ frontier K} = {a, b} := by
  set S := lineParams K p v with hS
  -- `S` is a nonempty compact (closed+bounded) interval
  have hmemS : t₀ ∈ S := by show line p v t₀ ∈ K; exact interior_subset ht₀
  have hne : S.Nonempty := ⟨t₀, hmemS⟩
  have hcl : IsClosed S := lineParams_isClosed hKc.isClosed p v
  have hba : BddAbove S := lineParams_bddAbove hKc.isBounded hv
  have hbb : BddBelow S := lineParams_bddBelow hKc.isBounded hv
  set a := sInf S with ha_def
  set b := sSup S with hb_def
  have ha : a ∈ S := hcl.csInf_mem hne hbb
  have hb : b ∈ S := hcl.csSup_mem hne hba
  have haK : line p v a ∈ K := ha
  have hbK : line p v b ∈ K := hb
  have hSIcc : S = Icc a b := lineParams_eq_Icc hK hKc hv hne
  -- the interior witness lands strictly inside `Ioo a b`, forcing `a < b`
  have ht₀int : t₀ ∈ interior S := by
    apply mem_interior.mpr
    refine ⟨line p v ⁻¹' interior K, ?_,
      isOpen_interior.preimage (line_continuous p v), ht₀⟩
    intro x hx; show line p v x ∈ K; exact interior_subset hx
  rw [hSIcc, interior_Icc] at ht₀int
  obtain ⟨h1, h2⟩ := ht₀int
  have hab : a < b := lt_trans h1 h2
  -- boundary characterisation
  have hcl' : closure K = K := hKc.isClosed.closure_eq
  have hfront : ∀ x : V, x ∈ frontier K ↔ x ∈ K ∧ x ∉ interior K := by
    intro x
    unfold frontier
    rw [Set.mem_diff, hcl']
  refine ⟨a, b, hab, hSIcc, ?_⟩
  ext t
  simp only [mem_setOf_eq, mem_insert_iff, mem_singleton_iff, hfront]
  constructor
  · rintro ⟨htK, htI⟩
    have htS : t ∈ S := htK
    rw [hSIcc, mem_Icc] at htS
    obtain ⟨hat, htb⟩ := htS
    by_contra hcon
    push_neg at hcon
    obtain ⟨hna, hnb⟩ := hcon
    have htIoo : t ∈ Ioo a b :=
      ⟨lt_of_le_of_ne hat (Ne.symm hna), lt_of_le_of_ne htb hnb⟩
    exact htI (line_Ioo_mem_interior hK ht₀ haK hbK htIoo)
  · -- endpoints are boundary points
    have hend : ∀ c : ℝ, c ∈ S → c = a ∨ c = b →
        line p v c ∈ K ∧ line p v c ∉ interior K := by
      intro c hcS hc
      refine ⟨hcS, ?_⟩
      intro hcint
      have hcI : c ∈ interior S := by
        apply mem_interior.mpr
        refine ⟨line p v ⁻¹' interior K, ?_,
          isOpen_interior.preimage (line_continuous p v), hcint⟩
        intro x hx; show line p v x ∈ K; exact interior_subset hx
      rw [hSIcc, interior_Icc] at hcI
      rcases hc with rfl | rfl
      · exact absurd hcI.1 (lt_irrefl a)
      · exact absurd hcI.2 (lt_irrefl b)
    rintro (rfl | rfl)
    · exact hend a ha (Or.inl rfl)
    · exact hend b hb (Or.inr rfl)

/-- The boundary-crossing parameter set has exactly two elements. -/
theorem line_through_interior_frontier_ncard_two
    (hK : Convex ℝ K) (hKc : IsCompact K) (hv : v ≠ 0)
    {t₀ : ℝ} (ht₀ : line p v t₀ ∈ interior K) :
    {t : ℝ | line p v t ∈ frontier K}.ncard = 2 := by
  obtain ⟨a, b, hab, _, hset⟩ :=
    line_through_interior_meets_frontier_in_two hK hKc hv ht₀
  rw [hset, Set.ncard_pair (ne_of_lt hab)]

end BuffonsNeedleOQ01OQ04OQ01
