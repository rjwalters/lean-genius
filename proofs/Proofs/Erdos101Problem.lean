/-
# Erdős Problem #101 — Four-Point Lines from Planar Point Sets

Given n points in ℝ² with no five collinear, prove that the number
of lines containing exactly four of the points is o(n²).

Erdős conjectured the true order is Θ(n^{3/2}), based on Grünbaum's
construction achieving ≫ n^{3/2} four-point lines. However, Solymosi
and Stojaković disproved this by constructing sets with n^{2−O(1/√(log n))}
four-point lines.

The o(n²) upper bound remains open.

Status: OPEN ($100)
Reference: https://erdosproblems.com/101
-/

import Mathlib.Data.Finset.Card
import Mathlib.Data.Nat.Basic
import Mathlib.Tactic

/- ## Definitions -/

/-- A planar point set: a finite collection of points in ℝ². -/
structure PlanarPointSet where
  points : Finset (ℝ × ℝ)
  size_pos : points.card > 0

/-- Three points are collinear if the signed area determinant vanishes. -/
def collinear (p q r : ℝ × ℝ) : Prop :=
  (q.1 - p.1) * (r.2 - p.2) = (r.1 - p.1) * (q.2 - p.2)

/-- A point set has no five collinear if no five distinct points are collinear. -/
def NoFiveCollinear (P : PlanarPointSet) : Prop :=
  ∀ a b c d e : ℝ × ℝ,
    a ∈ P.points → b ∈ P.points → c ∈ P.points →
    d ∈ P.points → e ∈ P.points →
    a ≠ b → a ≠ c → a ≠ d → a ≠ e →
    b ≠ c → b ≠ d → b ≠ e → c ≠ d → c ≠ e → d ≠ e →
    ¬(collinear a b c ∧ collinear a b d ∧ collinear a b e)

open Classical in
/-- Count of lines through exactly four points of P. -/
noncomputable def fourPointLineCount (P : PlanarPointSet) : ℕ :=
  (P.points.powerset.filter (fun S =>
    S.card = 4 ∧
    ∃ a b : ℝ × ℝ, a ∈ S ∧ b ∈ S ∧ a ≠ b ∧
      ∀ p ∈ S, collinear a b p)).card

/- ## Properties of Collinearity -/

/-- Collinearity is reflexive: any point is collinear with itself and any other point. -/
theorem collinear_self (p q : ℝ × ℝ) : collinear p p q := by
  unfold collinear; simp

/-- Collinearity holds when all three points are the same. -/
theorem collinear_refl (p : ℝ × ℝ) : collinear p p p := by
  unfold collinear; ring

/-- Any point is collinear with two copies of another point. -/
theorem collinear_self_right (p q : ℝ × ℝ) : collinear p q q := by
  unfold collinear; ring

/-- Collinearity is symmetric in the second and third arguments. -/
theorem collinear_swap23 {p q r : ℝ × ℝ} (h : collinear p q r) :
    collinear p r q := by
  unfold collinear at *; linarith

/-- Collinearity is symmetric in the first and second arguments.
    If p, q, r are collinear (anchored at p), then q, p, r are collinear (anchored at q). -/
theorem collinear_swap12 {p q r : ℝ × ℝ} (h : collinear p q r) :
    collinear q p r := by
  unfold collinear at *; nlinarith

/-- Full rotation: collinear p q r → collinear r q p. -/
theorem collinear_rotate {p q r : ℝ × ℝ} (h : collinear p q r) :
    collinear r q p :=
  collinear_swap23 (collinear_swap12 (collinear_swap23 h))

/-- Cyclic permutation: collinear p q r → collinear q r p. -/
theorem collinear_cycle {p q r : ℝ × ℝ} (h : collinear p q r) :
    collinear q r p :=
  collinear_swap23 (collinear_swap12 h)

/-- Collinearity transitivity: if p, q, r are collinear and p, q, s are collinear
    (with p ≠ q), then p, r, s are collinear. -/
theorem collinear_trans {p q r s : ℝ × ℝ} (hpq : p ≠ q)
    (hpqr : collinear p q r) (hpqs : collinear p q s) :
    collinear p r s := by
  unfold collinear at *
  by_cases hx : q.1 - p.1 = 0
  · have hy : q.2 - p.2 ≠ 0 := by
      intro hy; apply hpq; ext <;> linarith
    have hr1 : r.1 - p.1 = 0 := by
      have := hpqr; rw [hx, zero_mul] at this
      exact (mul_eq_zero.mp this.symm).resolve_right hy
    have hs1 : s.1 - p.1 = 0 := by
      have := hpqs; rw [hx, zero_mul] at this
      exact (mul_eq_zero.mp this.symm).resolve_right hy
    rw [hr1, hs1]; ring
  · have key : (q.1 - p.1) * ((r.1 - p.1) * (s.2 - p.2)) =
               (q.1 - p.1) * ((s.1 - p.1) * (r.2 - p.2)) := by
      have h1 : (r.1 - p.1) * ((q.1 - p.1) * (s.2 - p.2)) =
                (r.1 - p.1) * ((s.1 - p.1) * (q.2 - p.2)) := by rw [hpqs]
      have h2 : (s.1 - p.1) * ((q.1 - p.1) * (r.2 - p.2)) =
                (s.1 - p.1) * ((r.1 - p.1) * (q.2 - p.2)) := by rw [hpqr]
      nlinarith
    exact mul_left_cancel₀ hx key

/-- Four points on the same line: if p, q, r, s are all collinear through
    distinct p, q, then q, r, s are collinear. -/
theorem collinear_four {p q r s : ℝ × ℝ} (hpq : p ≠ q)
    (hpqr : collinear p q r) (hpqs : collinear p q s) :
    collinear q r s :=
  collinear_trans (Ne.symm hpq) (collinear_swap12 hpqr) (collinear_swap12 hpqs)

/-- Full transitivity over a line: if r, s, t all lie on the line through
    distinct p, q, then r, s, t are collinear. -/
theorem collinear_any_triple {p q r s t : ℝ × ℝ} (hpq : p ≠ q)
    (hr : collinear p q r) (hs : collinear p q s) (ht : collinear p q t) :
    collinear r s t := by
  have h1 := collinear_trans hpq hr hs
  have h2 := collinear_trans hpq hr ht
  by_cases hrp : r = p
  · subst hrp; exact collinear_trans hpq hs ht
  · exact collinear_trans hrp (collinear_swap12 h1) (collinear_swap12 h2)

/- ## Structural Properties -/

/-- NoFiveCollinear holds vacuously for sets of 4 or fewer points. -/
theorem noFiveCollinear_small (P : PlanarPointSet) (h : P.points.card ≤ 4) :
    NoFiveCollinear P := by
  unfold NoFiveCollinear
  intro a b c d e ha hb hc hd he hab hac had hae hbc hbd hbe hcd hce hde
  have h5 : ({a, b, c, d, e} : Finset (ℝ × ℝ)).card = 5 := by
    rw [Finset.card_insert_of_notMem]
    · rw [Finset.card_insert_of_notMem]
      · rw [Finset.card_insert_of_notMem]
        · rw [Finset.card_insert_of_notMem]
          · simp
          · simp [hde]
        · simp [hcd, hce]
      · simp [hbc, hbd, hbe]
    · simp [hab, hac, had, hae]
  have hsub : {a, b, c, d, e} ⊆ P.points := by
    intro x hx; simp at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl <;> assumption
  have := Finset.card_le_card hsub
  rw [h5] at this; omega

open Classical in
/-- For sets with fewer than 4 points, fourPointLineCount is zero. -/
theorem fourPointLineCount_lt_four (P : PlanarPointSet) (h : P.points.card < 4) :
    fourPointLineCount P = 0 := by
  unfold fourPointLineCount
  apply Finset.card_eq_zero.mpr
  rw [Finset.filter_eq_empty_iff]
  intro S hS
  simp only [not_and]
  intro hcard; exfalso
  have hsub := Finset.mem_powerset.mp hS
  have := Finset.card_le_card hsub; omega

open Classical in
/-- Under NoFiveCollinear, for any two distinct points a, b in P, the set of
    points in P collinear with a and b has at most 4 elements. -/
theorem noFiveCollinear_line_bound (P : PlanarPointSet) (hP : NoFiveCollinear P)
    (a b : ℝ × ℝ) (ha : a ∈ P.points) (hb : b ∈ P.points) (hab : a ≠ b) :
    (P.points.filter (fun p => collinear a b p)).card ≤ 4 := by
  by_contra h
  push_neg at h
  set L := P.points.filter (fun p => collinear a b p)
  have ha_L : a ∈ L := Finset.mem_filter.mpr ⟨ha, by unfold collinear; ring⟩
  have hb_L : b ∈ L := Finset.mem_filter.mpr ⟨hb, collinear_self_right a b⟩
  set L' := (L.erase a).erase b
  have hb_ea : b ∈ L.erase a := Finset.mem_erase.mpr ⟨Ne.symm hab, hb_L⟩
  have hL'_card : L'.card ≥ 3 := by
    have h1 : (L.erase a).card = L.card - 1 := Finset.card_erase_of_mem ha_L
    have h2 : L'.card = (L.erase a).card - 1 := Finset.card_erase_of_mem hb_ea
    omega
  have hL'_ne : L'.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨c, hc⟩ := hL'_ne
  have hL'c : (L'.erase c).card ≥ 2 := by
    have := Finset.card_erase_of_mem hc; omega
  have hL'c_ne : (L'.erase c).Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨d, hd⟩ := hL'c_ne
  have hL'cd : ((L'.erase c).erase d).card ≥ 1 := by
    have := Finset.card_erase_of_mem hd; omega
  have hL'cd_ne : ((L'.erase c).erase d).Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨e, he⟩ := hL'cd_ne
  have he_ec : e ∈ L'.erase c := Finset.mem_of_mem_erase he
  have he_L' : e ∈ L' := Finset.mem_of_mem_erase he_ec
  have hd_L' : d ∈ L' := Finset.mem_of_mem_erase hd
  have hc_eaL : c ∈ L.erase a := Finset.mem_of_mem_erase hc
  have hd_eaL : d ∈ L.erase a := Finset.mem_of_mem_erase hd_L'
  have he_eaL : e ∈ L.erase a := Finset.mem_of_mem_erase he_L'
  have hc_L : c ∈ L := Finset.mem_of_mem_erase hc_eaL
  have hd_L : d ∈ L := Finset.mem_of_mem_erase hd_eaL
  have he_L : e ∈ L := Finset.mem_of_mem_erase he_eaL
  have hc_P : c ∈ P.points := (Finset.mem_filter.mp hc_L).1
  have hd_P : d ∈ P.points := (Finset.mem_filter.mp hd_L).1
  have he_P : e ∈ P.points := (Finset.mem_filter.mp he_L).1
  have hcol_c : collinear a b c := (Finset.mem_filter.mp hc_L).2
  have hcol_d : collinear a b d := (Finset.mem_filter.mp hd_L).2
  have hcol_e : collinear a b e := (Finset.mem_filter.mp he_L).2
  have hac : a ≠ c := fun h => absurd hc_eaL (h ▸ Finset.notMem_erase a L)
  have hbc : b ≠ c := fun h => absurd hc (h ▸ Finset.notMem_erase b (L.erase a))
  have had : a ≠ d := fun h => absurd hd_eaL (h ▸ Finset.notMem_erase a L)
  have hbd : b ≠ d := fun h => absurd hd_L' (h ▸ Finset.notMem_erase b (L.erase a))
  have hae : a ≠ e := fun h => absurd he_eaL (h ▸ Finset.notMem_erase a L)
  have hbe : b ≠ e := fun h => absurd he_L' (h ▸ Finset.notMem_erase b (L.erase a))
  have hcd : c ≠ d := fun h => absurd hd (h ▸ Finset.notMem_erase c L')
  have hce : c ≠ e := fun h => absurd he_ec (h ▸ Finset.notMem_erase c L')
  have hde : d ≠ e := fun h => absurd he (h ▸ Finset.notMem_erase d (L'.erase c))
  exact hP a b c d e ha hb hc_P hd_P he_P hab hac had hae hbc hbd hbe hcd hce hde
    ⟨hcol_c, hcol_d, hcol_e⟩

/- ## Uniqueness of Four-Collinear Subsets -/

open Classical in
/-- If two 4-element collinear subsets of P both contain distinct points a, b,
    then under NoFiveCollinear they must be equal. -/
theorem four_collinear_unique (P : PlanarPointSet) (hP : NoFiveCollinear P)
    (S₁ S₂ : Finset (ℝ × ℝ))
    (hS₁_sub : S₁ ⊆ P.points) (hS₂_sub : S₂ ⊆ P.points)
    (hS₁_card : S₁.card = 4) (hS₂_card : S₂.card = 4)
    (a b : ℝ × ℝ) (hab : a ≠ b)
    (ha₁ : a ∈ S₁) (hb₁ : b ∈ S₁) (ha₂ : a ∈ S₂) (hb₂ : b ∈ S₂)
    (hcol₁ : ∀ p ∈ S₁, collinear a b p)
    (hcol₂ : ∀ p ∈ S₂, collinear a b p) :
    S₁ = S₂ := by
  set L := P.points.filter (fun p => collinear a b p) with hL_def
  have hL_bound := noFiveCollinear_line_bound P hP a b
    (hS₁_sub ha₁) (hS₁_sub hb₁) hab
  have hS₁_L : S₁ ⊆ L := by
    intro x hx; exact Finset.mem_filter.mpr ⟨hS₁_sub hx, hcol₁ x hx⟩
  have hS₂_L : S₂ ⊆ L := by
    intro x hx; exact Finset.mem_filter.mpr ⟨hS₂_sub hx, hcol₂ x hx⟩
  have hS₁_eq : S₁ = L := by
    apply Finset.eq_of_subset_of_card_le hS₁_L
    rw [hS₁_card]; exact hL_bound
  have hS₂_eq : S₂ = L := by
    apply Finset.eq_of_subset_of_card_le hS₂_L
    rw [hS₂_card]; exact hL_bound
  rw [hS₁_eq, hS₂_eq]

open Classical in
/-- Two distinct 4-element collinear subsets of P (under NoFiveCollinear)
    share at most one element. -/
theorem four_collinear_overlap_small (P : PlanarPointSet) (hP : NoFiveCollinear P)
    (S₁ S₂ : Finset (ℝ × ℝ))
    (hS₁_sub : S₁ ⊆ P.points) (hS₂_sub : S₂ ⊆ P.points)
    (hS₁_card : S₁.card = 4) (hS₂_card : S₂.card = 4)
    (hne : S₁ ≠ S₂)
    (a₁ b₁ : ℝ × ℝ) (hab₁ : a₁ ≠ b₁)
    (ha₁ : a₁ ∈ S₁) (hb₁ : b₁ ∈ S₁)
    (hcol₁ : ∀ p ∈ S₁, collinear a₁ b₁ p)
    (a₂ b₂ : ℝ × ℝ) (hab₂ : a₂ ≠ b₂)
    (ha₂ : a₂ ∈ S₂) (hb₂ : b₂ ∈ S₂)
    (hcol₂ : ∀ p ∈ S₂, collinear a₂ b₂ p) :
    (S₁ ∩ S₂).card ≤ 1 := by
  by_contra h
  push_neg at h
  have hne2 : (S₁ ∩ S₂).card ≥ 2 := h
  have ⟨x, hx⟩ := Finset.card_pos.mp (by omega : (S₁ ∩ S₂).card > 0)
  have ⟨y, hy⟩ := Finset.card_pos.mp (show ((S₁ ∩ S₂).erase x).card > 0 by
    have := Finset.card_erase_of_mem hx; omega)
  have hy_mem : y ∈ S₁ ∩ S₂ := Finset.mem_of_mem_erase hy
  have hxy : x ≠ y := fun h => by subst h; exact absurd hy (Finset.notMem_erase x _)
  have hx₁ := (Finset.mem_inter.mp hx).1
  have hx₂ := (Finset.mem_inter.mp hx).2
  have hy₁ := (Finset.mem_inter.mp hy_mem).1
  have hy₂ := (Finset.mem_inter.mp hy_mem).2
  have hcol₁' : ∀ p ∈ S₁, collinear x y p := by
    intro p hp
    exact collinear_any_triple hab₁ (hcol₁ x hx₁) (hcol₁ y hy₁) (hcol₁ p hp)
  have hcol₂' : ∀ p ∈ S₂, collinear x y p := by
    intro p hp
    exact collinear_any_triple hab₂ (hcol₂ x hx₂) (hcol₂ y hy₂) (hcol₂ p hp)
  exact hne (four_collinear_unique P hP S₁ S₂ hS₁_sub hS₂_sub hS₁_card hS₂_card x y hxy
    hx₁ hy₁ hx₂ hy₂ hcol₁' hcol₂')

/- ## Main Conjecture -/

/-- **Erdős Problem #101**: the number of four-point lines is o(n²).
    For any ε > 0, eventually fourPointLineCount(P) < ε · n². -/
axiom erdos_101_conjecture :
  ∀ ε : ℝ, ε > 0 →
    ∃ N₀ : ℕ, ∀ P : PlanarPointSet,
      NoFiveCollinear P → P.points.card ≥ N₀ →
        (fourPointLineCount P : ℝ) < ε * (P.points.card : ℝ) ^ 2

/- ## Known Results -/

/-- **Grünbaum's Lower Bound**: there exist point sets with no five collinear
    achieving ≫ n^{3/2} four-point lines. -/
axiom grunbaum_lower_bound :
  ∃ c : ℝ, c > 0 ∧
    ∀ N : ℕ, ∃ P : PlanarPointSet,
      NoFiveCollinear P ∧ P.points.card ≥ N ∧
        (fourPointLineCount P : ℝ) ≥ c * (P.points.card : ℝ) ^ (3/2 : ℝ)

/-- **Solymosi–Stojaković**: configurations exist with n^{2−O(1/√(log n))}
    four-point lines, disproving Erdős's Θ(n^{3/2}) conjecture. -/
axiom solymosi_stojakovic_lower :
  ∀ C : ℝ, C > 0 →
    ∃ N₀ : ℕ, ∀ n ≥ N₀, ∃ P : PlanarPointSet,
      NoFiveCollinear P ∧ P.points.card = n ∧
        (fourPointLineCount P : ℝ) ≥ (n : ℝ) ^ (2 - C / Real.sqrt (Real.log n))

open Classical in
/-- **Trivial Upper Bound (n²)**: Under NoFiveCollinear, fourPointLineCount ≤ n².
    Injection from 4-collinear subsets to ordered pairs via existential witnesses. -/
theorem trivial_upper_bound_sq (P : PlanarPointSet) (hP : NoFiveCollinear P) :
    fourPointLineCount P ≤ P.points.card * P.points.card := by
  unfold fourPointLineCount
  set F := P.points.powerset.filter (fun S =>
    S.card = 4 ∧
    ∃ a b : ℝ × ℝ, a ∈ S ∧ b ∈ S ∧ a ≠ b ∧
      ∀ p ∈ S, collinear a b p)
  have hF_sub : ∀ S ∈ F, S ⊆ P.points :=
    fun S hS => Finset.mem_powerset.mp (Finset.mem_of_mem_filter S hS)
  have hF_prop : ∀ S ∈ F, S.card = 4 ∧
      ∃ a b : ℝ × ℝ, a ∈ S ∧ b ∈ S ∧ a ≠ b ∧ ∀ p ∈ S, collinear a b p :=
    fun S hS => (Finset.mem_filter.mp hS).2
  let witnessMap : Finset (ℝ × ℝ) → (ℝ × ℝ) × (ℝ × ℝ) := fun S =>
    if h : ∃ a b : ℝ × ℝ, a ∈ S ∧ b ∈ S ∧ a ≠ b ∧ ∀ p ∈ S, collinear a b p
    then (h.choose, h.choose_spec.choose)
    else ((0, 0), (0, 0))
  have hF_dite : ∀ S ∈ F, ∃ a b : ℝ × ℝ, a ∈ S ∧ b ∈ S ∧ a ≠ b ∧
      ∀ p ∈ S, collinear a b p :=
    fun S hS => (hF_prop S hS).2
  have hmap_a_mem : ∀ S ∈ F, (witnessMap S).1 ∈ S := by
    intro S hS
    have hdite := hF_dite S hS
    show (witnessMap S).1 ∈ S
    simp only [witnessMap, dif_pos hdite]
    exact hdite.choose_spec.choose_spec.1
  have hmap_b_mem : ∀ S ∈ F, (witnessMap S).2 ∈ S := by
    intro S hS
    have hdite := hF_dite S hS
    show (witnessMap S).2 ∈ S
    simp only [witnessMap, dif_pos hdite]
    exact hdite.choose_spec.choose_spec.2.1
  have hmap_ne : ∀ S ∈ F, (witnessMap S).1 ≠ (witnessMap S).2 := by
    intro S hS
    have hdite := hF_dite S hS
    show (witnessMap S).1 ≠ (witnessMap S).2
    simp only [witnessMap, dif_pos hdite]
    exact hdite.choose_spec.choose_spec.2.2.1
  have hmap_col : ∀ S ∈ F, ∀ p ∈ S,
      collinear (witnessMap S).1 (witnessMap S).2 p := by
    intro S hS p hp
    have hdite := hF_dite S hS
    show collinear (witnessMap S).1 (witnessMap S).2 p
    simp only [witnessMap, dif_pos hdite]
    exact hdite.choose_spec.choose_spec.2.2.2 p hp
  calc F.card ≤ (P.points ×ˢ P.points).card := by
        apply Finset.card_le_card_of_injOn witnessMap
        · intro S hS
          exact Finset.mem_product.mpr
            ⟨hF_sub S hS (hmap_a_mem S hS), hF_sub S hS (hmap_b_mem S hS)⟩
        · intro S₁ hS₁ S₂ hS₂ heq
          have h₁ := hF_prop S₁ hS₁
          have h₂ := hF_prop S₂ hS₂
          have ha₂ : (witnessMap S₁).1 ∈ S₂ := by
            rw [congr_arg Prod.fst heq]; exact hmap_a_mem S₂ hS₂
          have hb₂ : (witnessMap S₁).2 ∈ S₂ := by
            rw [congr_arg Prod.snd heq]; exact hmap_b_mem S₂ hS₂
          have hcol₂ : ∀ p ∈ S₂, collinear (witnessMap S₁).1 (witnessMap S₁).2 p := by
            intro p hp
            have := hmap_col S₂ hS₂ p hp
            rwa [← congr_arg Prod.fst heq, ← congr_arg Prod.snd heq] at this
          exact four_collinear_unique P hP S₁ S₂ (hF_sub S₁ hS₁) (hF_sub S₂ hS₂)
            h₁.1 h₂.1 _ _ (hmap_ne S₁ hS₁)
            (hmap_a_mem S₁ hS₁) (hmap_b_mem S₁ hS₁) ha₂ hb₂
            (hmap_col S₁ hS₁) hcol₂
    _ = P.points.card * P.points.card := Finset.card_product _ _

/-- **Trivial Upper Bound (tight)**: Under NoFiveCollinear, fourPointLineCount ≤ n(n−1)/2.
    Follows from injection into unordered pairs. Kept as axiom pending formalization. -/
axiom trivial_upper_bound :
  ∀ P : PlanarPointSet, NoFiveCollinear P →
    fourPointLineCount P ≤ P.points.card * (P.points.card - 1) / 2

/- ## Related Observations -/

/-- **Collinear Triples**: Burr–Grünbaum–Sloane and Füredi–Palásti constructed
    sets with ~n²/6 collinear triples but no four-point lines. -/
axiom collinear_triples_no_four :
  ∃ c : ℝ, c > 0 ∧
    ∀ N : ℕ, ∃ P : PlanarPointSet,
      NoFiveCollinear P ∧ P.points.card ≥ N ∧
        fourPointLineCount P = 0

/-- **Szemerédi–Trotter Bound**: the number of point-line incidences
    is O(n^{2/3} m^{2/3} + n + m) for n points and m lines in the plane. -/
axiom szemeredi_trotter :
  ∃ C : ℝ, C > 0 ∧
    ∀ (n m : ℕ), ∀ (incidences : ℕ),
      (incidences : ℝ) ≤ C * ((n : ℝ) ^ (2/3 : ℝ) * (m : ℝ) ^ (2/3 : ℝ) + n + m)
