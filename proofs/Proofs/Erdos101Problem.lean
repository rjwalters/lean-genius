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
    (ha₁ : a ∈ S₁) (hb₁ : b ∈ S₁) (_ha₂ : a ∈ S₂) (_hb₂ : b ∈ S₂)
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
    (_ha₁ : a₁ ∈ S₁) (_hb₁ : b₁ ∈ S₁)
    (hcol₁ : ∀ p ∈ S₁, collinear a₁ b₁ p)
    (a₂ b₂ : ℝ × ℝ) (hab₂ : a₂ ≠ b₂)
    (_ha₂ : a₂ ∈ S₂) (_hb₂ : b₂ ∈ S₂)
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
/- ## Known Results -/

/-- **Grünbaum's Lower Bound**: there exist point sets with no five collinear
    achieving ≫ n^{3/2} four-point lines. -/
/-- **Solymosi–Stojaković**: configurations exist with n^{2−O(1/√(log n))}
    four-point lines, disproving Erdős's Θ(n^{3/2}) conjecture. -/
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

open Classical in
/-- **PROVED: Trivial Upper Bound (tight)**: Under NoFiveCollinear, fourPointLineCount ≤ n(n-1)/2.
    Each four-collinear subset S determines a unique line (by NoFiveCollinear), and each line
    is determined by any 2 of its points. So the map S to (a, b) in offDiag is injective,
    giving at most n(n-1). The tighter /2 follows because `four_collinear_unique` means
    each unordered pair determines at most one S. -/
theorem trivial_upper_bound :
    ∀ P : PlanarPointSet, NoFiveCollinear P →
      fourPointLineCount P ≤ P.points.card * (P.points.card - 1) / 2 := by
  intro P hP
  -- The n² bound already proved; we improve to n(n-1)/2 via offDiag injection
  unfold fourPointLineCount
  set F := P.points.powerset.filter (fun S =>
    S.card = 4 ∧
    ∃ a b : ℝ × ℝ, a ∈ S ∧ b ∈ S ∧ a ≠ b ∧
      ∀ p ∈ S, collinear a b p)
  -- Step 1: Map each S to an ordered pair (a, b) ∈ P.offDiag
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
    intro S hS; have h := hF_dite S hS
    simp only [witnessMap, dif_pos h]; exact h.choose_spec.choose_spec.1
  have hmap_b_mem : ∀ S ∈ F, (witnessMap S).2 ∈ S := by
    intro S hS; have h := hF_dite S hS
    simp only [witnessMap, dif_pos h]; exact h.choose_spec.choose_spec.2.1
  have hmap_ne : ∀ S ∈ F, (witnessMap S).1 ≠ (witnessMap S).2 := by
    intro S hS; have h := hF_dite S hS
    simp only [witnessMap, dif_pos h]; exact h.choose_spec.choose_spec.2.2.1
  have hmap_col : ∀ S ∈ F, ∀ p ∈ S,
      collinear (witnessMap S).1 (witnessMap S).2 p := by
    intro S hS p hp; have h := hF_dite S hS
    simp only [witnessMap, dif_pos h]; exact h.choose_spec.choose_spec.2.2.2 p hp
  -- Step 2: Show witnessMap lands in offDiag (since a ≠ b)
  have hmap_offDiag : ∀ S ∈ F, witnessMap S ∈ P.points.offDiag := by
    intro S hS
    exact Finset.mem_offDiag.mpr
      ⟨hF_sub S hS (hmap_a_mem S hS), hF_sub S hS (hmap_b_mem S hS), hmap_ne S hS⟩
  -- Step 3: witnessMap is injective on F
  have hmap_inj : Set.InjOn witnessMap (↑F) := by
    intro S₁ hS₁ S₂ hS₂ heq
    have h₁ := hF_prop S₁ (Finset.mem_coe.mp hS₁)
    have h₂ := hF_prop S₂ (Finset.mem_coe.mp hS₂)
    have ha₂ : (witnessMap S₁).1 ∈ S₂ := by
      rw [congr_arg Prod.fst heq]; exact hmap_a_mem S₂ (Finset.mem_coe.mp hS₂)
    have hb₂ : (witnessMap S₁).2 ∈ S₂ := by
      rw [congr_arg Prod.snd heq]; exact hmap_b_mem S₂ (Finset.mem_coe.mp hS₂)
    have hcol₂ : ∀ p ∈ S₂, collinear (witnessMap S₁).1 (witnessMap S₁).2 p := by
      intro p hp
      have := hmap_col S₂ (Finset.mem_coe.mp hS₂) p hp
      rwa [← congr_arg Prod.fst heq, ← congr_arg Prod.snd heq] at this
    exact four_collinear_unique P hP S₁ S₂
      (hF_sub S₁ (Finset.mem_coe.mp hS₁)) (hF_sub S₂ (Finset.mem_coe.mp hS₂))
      h₁.1 h₂.1 _ _ (hmap_ne S₁ (Finset.mem_coe.mp hS₁))
      (hmap_a_mem S₁ (Finset.mem_coe.mp hS₁)) (hmap_b_mem S₁ (Finset.mem_coe.mp hS₁))
      ha₂ hb₂ (hmap_col S₁ (Finset.mem_coe.mp hS₁)) hcol₂
  -- Step 4: |F| ≤ |offDiag| = n(n-1) ≤ n(n-1), then /2 via injection refinement
  -- Actually, we first get |F| ≤ |offDiag| = n(n-1)
  -- Then we refine: each unordered pair {a,b} is hit at most once by witnessMap
  -- So |F| ≤ n(n-1)/2
  -- Use: offDiag has card n*(n-1), and the image under witnessMap has at most
  -- half the offDiag since for each (a,b) in the image, (b,a) is NOT also in the image
  -- (because witnessMap is a function, so S ↦ witnessMap(S) is deterministic)
  -- But actually, it's simpler to bound F.card ≤ (P.points.powersetCard 2).card
  -- Map S to the 2-element set {(witnessMap S).1, (witnessMap S).2}
  let pairMap : Finset (ℝ × ℝ) → Finset (ℝ × ℝ) := fun S =>
    {(witnessMap S).1, (witnessMap S).2}
  have hpair_card : ∀ S ∈ F, (pairMap S).card = 2 := by
    intro S hS
    simp only [pairMap, Finset.card_pair (hmap_ne S hS)]
  have hpair_sub : ∀ S ∈ F, pairMap S ⊆ P.points := by
    intro S hS x hx
    simp only [pairMap, Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact hF_sub S hS (hmap_a_mem S hS)
    · exact hF_sub S hS (hmap_b_mem S hS)
  have hpair_mem : ∀ S ∈ F, pairMap S ∈ P.points.powersetCard 2 := by
    intro S hS
    exact Finset.mem_powersetCard.mpr ⟨hpair_sub S hS, hpair_card S hS⟩
  -- Injectivity of pairMap: if {a₁,b₁} = {a₂,b₂}, then a₂,b₂ both lie on the
  -- line through a₁,b₁ (collinear), so four_collinear_unique gives S₁ = S₂
  have hpair_inj : ∀ S₁ ∈ F, ∀ S₂ ∈ F, pairMap S₁ = pairMap S₂ → S₁ = S₂ := by
    intro S₁ hS₁ S₂ hS₂ heq
    have h₁ := hF_prop S₁ hS₁
    have h₂ := hF_prop S₂ hS₂
    -- From heq, the 2-element sets {a₁,b₁} = {a₂,b₂}
    -- So a₂ ∈ {a₁,b₁} and b₂ ∈ {a₁,b₁}
    -- From heq: {a₂, b₂} = {a₁, b₁}, so a₂ and b₂ are each equal to a₁ or b₁
    have ha₂_mem : (witnessMap S₂).1 ∈ pairMap S₁ := by
      rw [heq]; simp [pairMap]
    have hb₂_mem : (witnessMap S₂).2 ∈ pairMap S₁ := by
      rw [heq]; simp [pairMap]
    simp only [pairMap, Finset.mem_insert, Finset.mem_singleton] at ha₂_mem hb₂_mem
    -- a₂ is either a₁ or b₁; b₂ is either a₁ or b₁
    -- In any case, a₂ and b₂ are in S₁ and collinear with line(a₁, b₁)
    have ha₂_S₁ : (witnessMap S₂).1 ∈ S₁ := by
      rcases ha₂_mem with h | h <;> rw [h]
      · exact hmap_a_mem S₁ hS₁
      · exact hmap_b_mem S₁ hS₁
    have hb₂_S₁ : (witnessMap S₂).2 ∈ S₁ := by
      rcases hb₂_mem with h | h <;> rw [h]
      · exact hmap_a_mem S₁ hS₁
      · exact hmap_b_mem S₁ hS₁
    -- All points of S₂ lie on the line through (witnessMap S₂).1 and (witnessMap S₂).2
    -- These two points also belong to S₁ and lie on the line through S₁'s witnesses
    -- By four_collinear_unique, S₁ = S₂
    have hne₂ : (witnessMap S₂).1 ≠ (witnessMap S₂).2 := hmap_ne S₂ hS₂
    -- Need: ∀ p ∈ S₁, collinear (witnessMap S₂).1 (witnessMap S₂).2 p
    have hcol_12 : ∀ p ∈ S₁, collinear (witnessMap S₂).1 (witnessMap S₂).2 p := by
      intro p hp
      -- p ∈ S₁, so collinear (witnessMap S₁).1 (witnessMap S₁).2 p
      have hp_col := hmap_col S₁ hS₁ p hp
      -- a₂, b₂ ∈ S₁, so collinear with S₁'s witnesses
      have ha₂_col := hmap_col S₁ hS₁ _ ha₂_S₁
      have hb₂_col := hmap_col S₁ hS₁ _ hb₂_S₁
      -- All three (a₂, b₂, p) are on line through S₁'s witnesses
      -- a₂ ≠ b₂, and they're collinear with S₁'s witnesses
      exact collinear_any_triple (hmap_ne S₁ hS₁) ha₂_col hb₂_col hp_col
    exact four_collinear_unique P hP S₁ S₂
      (hF_sub S₁ hS₁) (hF_sub S₂ hS₂) h₁.1 h₂.1
      (witnessMap S₂).1 (witnessMap S₂).2 hne₂
      ha₂_S₁ hb₂_S₁
      (hmap_a_mem S₂ hS₂) (hmap_b_mem S₂ hS₂)
      hcol_12 (hmap_col S₂ hS₂)
  -- Step 5: F.card ≤ (powersetCard 2 P.points).card = n.choose 2 = n(n-1)/2
  calc F.card ≤ (P.points.powersetCard 2).card := by
        apply Finset.card_le_card_of_injOn pairMap hpair_mem
        intro S₁ hS₁ S₂ hS₂ heq
        exact hpair_inj S₁ hS₁ S₂ hS₂ heq
    _ = P.points.card.choose 2 := Finset.card_powersetCard 2 P.points
    _ = P.points.card * (P.points.card - 1) / 2 := Nat.choose_two_right P.points.card

/- ## Improved Upper Bound -/

/-- If two Finsets share at most 1 element, their 2-element subsets are disjoint. -/
theorem powersetCard2_disjoint {α : Type*} [DecidableEq α]
    {S₁ S₂ : Finset α} (h : (S₁ ∩ S₂).card ≤ 1) :
    Disjoint (S₁.powersetCard 2) (S₂.powersetCard 2) := by
  rw [Finset.disjoint_left]
  intro T hT₁ hT₂
  have hsub₁ := (Finset.mem_powersetCard.mp hT₁).1
  have hsub₂ := (Finset.mem_powersetCard.mp hT₂).1
  have hcard := (Finset.mem_powersetCard.mp hT₁).2
  have hT_inter : T ⊆ S₁ ∩ S₂ := Finset.subset_inter hsub₁ hsub₂
  have := Finset.card_le_card hT_inter
  omega

open Classical in
/-- **Improved Upper Bound**: Under NoFiveCollinear, fourPointLineCount(P) ≤ n(n-1)/12.
    Each 4-collinear subset has C(4,2) = 6 pairs. Distinct subsets share ≤1 point,
    so their pair-sets are disjoint. Packing into C(n,2) = n(n-1)/2 total pairs
    gives 6·|F| ≤ n(n-1)/2, hence |F| ≤ n(n-1)/12. -/
theorem improved_upper_bound (P : PlanarPointSet) (hP : NoFiveCollinear P) :
    fourPointLineCount P ≤ P.points.card * (P.points.card - 1) / 12 := by
  -- Reformulate as: 12 * fourPointLineCount P ≤ P.points.card * (P.points.card - 1)
  -- which is equivalent in ℕ division.
  -- Strategy: prove 6 * fourPointLineCount P ≤ n.choose 2, then use n.choose 2 = n*(n-1)/2
  suffices h : 6 * fourPointLineCount P ≤ P.points.card.choose 2 by
    rw [Nat.choose_two_right] at h; omega
  unfold fourPointLineCount
  set n := P.points.card
  set F := P.points.powerset.filter (fun S =>
    S.card = 4 ∧
    ∃ a b : ℝ × ℝ, a ∈ S ∧ b ∈ S ∧ a ≠ b ∧
      ∀ p ∈ S, collinear a b p)
  -- Need: 6 * F.card ≤ n.choose 2
  -- Build: each S ∈ F maps to 6 pairs in P.points.powersetCard 2
  -- These are disjoint across distinct S
  -- So biUnion of pair-sets has card = 6 * |F|
  -- And it's a subset of P.points.powersetCard 2 of size n.choose 2
  -- Helpers
  have hF_sub : ∀ S ∈ F, S ⊆ P.points :=
    fun S hS => Finset.mem_powerset.mp (Finset.mem_of_mem_filter S hS)
  have hF_prop : ∀ S ∈ F, S.card = 4 ∧
      ∃ a b : ℝ × ℝ, a ∈ S ∧ b ∈ S ∧ a ≠ b ∧ ∀ p ∈ S, collinear a b p :=
    fun S hS => (Finset.mem_filter.mp hS).2
  -- The pair-set map
  let pairSet : Finset (ℝ × ℝ) → Finset (Finset (ℝ × ℝ)) := fun S =>
    S.powersetCard 2
  -- Each pairSet S has card = C(4,2) = 6
  have hpair_card : ∀ S ∈ F, (pairSet S).card = 6 := by
    intro S hS
    show (S.powersetCard 2).card = 6
    rw [Finset.card_powersetCard]
    rw [(hF_prop S hS).1]; decide
  -- Pairwise disjointness: use powersetCard2_disjoint + four_collinear_overlap_small
  have hpair_disj : ∀ S₁ ∈ F, ∀ S₂ ∈ F, S₁ ≠ S₂ →
      Disjoint (pairSet S₁) (pairSet S₂) := by
    intro S₁ hS₁ S₂ hS₂ hne
    have h₁ := hF_prop S₁ hS₁
    have h₂ := hF_prop S₂ hS₂
    obtain ⟨a₁, b₁, ha₁, hb₁, hab₁, hcol₁⟩ := h₁.2
    obtain ⟨a₂, b₂, ha₂, hb₂, hab₂, hcol₂⟩ := h₂.2
    apply powersetCard2_disjoint
    exact four_collinear_overlap_small P hP S₁ S₂
      (hF_sub S₁ hS₁) (hF_sub S₂ hS₂)
      h₁.1 h₂.1 hne a₁ b₁ hab₁ ha₁ hb₁ hcol₁ a₂ b₂ hab₂ ha₂ hb₂ hcol₂
  -- The biUnion lands in P.points.powersetCard 2
  have hbU_sub : F.biUnion pairSet ⊆ P.points.powersetCard 2 := by
    intro T hT
    rw [Finset.mem_biUnion] at hT
    obtain ⟨S, hS, hT_S⟩ := hT
    have hsub_S := (Finset.mem_powersetCard.mp hT_S).1
    have hcard_T := (Finset.mem_powersetCard.mp hT_S).2
    exact Finset.mem_powersetCard.mpr ⟨Finset.Subset.trans hsub_S (hF_sub S hS), hcard_T⟩
  -- biUnion card = sum of individual cards (disjoint)
  have hbU_card : (F.biUnion pairSet).card = F.sum (fun S => (pairSet S).card) := by
    exact Finset.card_biUnion (fun S hS T hT hne => hpair_disj S hS T hT hne)
  -- Sum = 6 * |F|
  have hsum_eq : F.sum (fun S => (pairSet S).card) = 6 * F.card := by
    rw [Finset.sum_const_nat (fun S hS => hpair_card S hS)]
    ring
  -- |biUnion| ≤ |P.points.powersetCard 2| = n.choose 2
  have hbU_le : (F.biUnion pairSet).card ≤ n.choose 2 := by
    calc (F.biUnion pairSet).card
        ≤ (P.points.powersetCard 2).card := Finset.card_le_card hbU_sub
      _ = n.choose 2 := Finset.card_powersetCard 2 P.points
  -- Combine: 6 * |F| ≤ n.choose 2
  linarith [hbU_card, hsum_eq, hbU_le]

/- ## Related Observations -/

/-- **Collinear Triples**: Burr–Grünbaum–Sloane and Füredi–Palásti constructed
    sets with ~n²/6 collinear triples but no four-point lines. -/
/-- **Szemerédi–Trotter Bound**: for any finite set of points P and finite set
    of lines L in ℝ², the number of incidences I(P,L) satisfies
    I(P,L) ≤ C · (|P|^{2/3}·|L|^{2/3} + |P| + |L|) for some absolute constant C.
    Note: stated for a given incidence count, not universally quantified. -/
/- ## The F family (for reuse across theorems) -/

open Classical in
/-- The family F of all 4-element collinear subsets of P.points. -/
noncomputable def fourCollinearFamily (P : PlanarPointSet) : Finset (Finset (ℝ × ℝ)) :=
  P.points.powerset.filter (fun S =>
    S.card = 4 ∧
    ∃ a b : ℝ × ℝ, a ∈ S ∧ b ∈ S ∧ a ≠ b ∧
      ∀ p ∈ S, collinear a b p)

open Classical in
/-- fourPointLineCount equals the cardinality of fourCollinearFamily. -/
theorem fourPointLineCount_eq_family (P : PlanarPointSet) :
    fourPointLineCount P = (fourCollinearFamily P).card := by
  unfold fourPointLineCount fourCollinearFamily; rfl

/- ## Per-Point Bound -/

open Classical in
/-- Four-collinear subsets of P containing a given point p. -/
noncomputable def fourCollinearThrough (P : PlanarPointSet) (p : ℝ × ℝ) :
    Finset (Finset (ℝ × ℝ)) :=
  P.points.powerset.filter (fun S =>
    S.card = 4 ∧ p ∈ S ∧
    ∃ a b : ℝ × ℝ, a ∈ S ∧ b ∈ S ∧ a ≠ b ∧
      ∀ q ∈ S, collinear a b q)

open Classical in
/-- **Per-Point Bound**: Under NoFiveCollinear, at most (n-1)/3 four-point lines
    pass through any single point.
    Proof: each 4-collinear subset through p contributes 3 other points.
    By overlap_small, distinct subsets share at most 1 element (namely p).
    So the "other" 3-element parts are pairwise disjoint in P \ {p}. -/
theorem fourCollinearThrough_bound (P : PlanarPointSet) (hP : NoFiveCollinear P)
    (p : ℝ × ℝ) (hp : p ∈ P.points) :
    (fourCollinearThrough P p).card ≤ (P.points.card - 1) / 3 := by
  set FP := fourCollinearThrough P p
  -- Map each S to S.erase p (3-element subset of P.points \ {p})
  let eraseMap : Finset (ℝ × ℝ) → Finset (ℝ × ℝ) := fun S => S.erase p
  -- Each eraseMap S has card 3
  have herase_card : ∀ S ∈ FP, (eraseMap S).card = 3 := by
    intro S hS
    have ⟨hcard, hp_S, _⟩ := (Finset.mem_filter.mp hS).2
    show (S.erase p).card = 3
    rw [Finset.card_erase_of_mem hp_S]; omega
  -- Each eraseMap S ⊆ P.points.erase p
  have herase_sub : ∀ S ∈ FP, eraseMap S ⊆ P.points.erase p := by
    intro S hS x hx
    have hS_sub := Finset.mem_powerset.mp (Finset.mem_of_mem_filter S hS)
    have hx_S := Finset.mem_of_mem_erase hx
    have hx_ne : x ≠ p := Finset.ne_of_mem_erase hx
    exact Finset.mem_erase.mpr ⟨hx_ne, hS_sub hx_S⟩
  -- eraseMap is injective on FP (since S = (eraseMap S) ∪ {p} for S ∈ FP)
  have herase_inj : ∀ S₁ ∈ FP, ∀ S₂ ∈ FP, eraseMap S₁ = eraseMap S₂ → S₁ = S₂ := by
    intro S₁ hS₁ S₂ hS₂ heq
    have ⟨_, hp₁, _⟩ := (Finset.mem_filter.mp hS₁).2
    have ⟨_, hp₂, _⟩ := (Finset.mem_filter.mp hS₂).2
    ext x
    by_cases hxp : x = p
    · subst hxp; exact ⟨fun _ => hp₂, fun _ => hp₁⟩
    · constructor
      · intro hx
        have hx_e : x ∈ eraseMap S₁ := Finset.mem_erase.mpr ⟨hxp, hx⟩
        have hx_e2 : x ∈ eraseMap S₂ := heq ▸ hx_e
        exact Finset.mem_of_mem_erase hx_e2
      · intro hx
        have hx_e : x ∈ eraseMap S₂ := Finset.mem_erase.mpr ⟨hxp, hx⟩
        have hx_e1 : x ∈ eraseMap S₁ := heq ▸ hx_e
        exact Finset.mem_of_mem_erase hx_e1
  -- Pairwise disjoint: from four_collinear_overlap_small
  have herase_disj : ∀ S₁ ∈ FP, ∀ S₂ ∈ FP, S₁ ≠ S₂ →
      Disjoint (eraseMap S₁) (eraseMap S₂) := by
    intro S₁ hS₁ S₂ hS₂ hne
    rw [Finset.disjoint_left]
    intro x hx₁ hx₂
    have hx_ne_p : x ≠ p := Finset.ne_of_mem_erase hx₁
    have hx_S₁ : x ∈ S₁ := Finset.mem_of_mem_erase hx₁
    have hx_S₂ : x ∈ S₂ := Finset.mem_of_mem_erase hx₂
    have ⟨hcard₁, hp₁, a₁, b₁, ha₁, hb₁, hab₁, hcol₁⟩ := (Finset.mem_filter.mp hS₁).2
    have ⟨hcard₂, hp₂, a₂, b₂, ha₂, hb₂, hab₂, hcol₂⟩ := (Finset.mem_filter.mp hS₂).2
    have hS₁_sub := Finset.mem_powerset.mp (Finset.mem_of_mem_filter S₁ hS₁)
    have hS₂_sub := Finset.mem_powerset.mp (Finset.mem_of_mem_filter S₂ hS₂)
    -- S₁ ∩ S₂ contains both p and x (with p ≠ x), so card ≥ 2
    have h_inter_ge : (S₁ ∩ S₂).card ≥ 2 := by
      have hp_inter : p ∈ S₁ ∩ S₂ := Finset.mem_inter.mpr ⟨hp₁, hp₂⟩
      have hx_inter : x ∈ S₁ ∩ S₂ := Finset.mem_inter.mpr ⟨hx_S₁, hx_S₂⟩
      have hpx : p ≠ x := Ne.symm hx_ne_p
      have : ({p, x} : Finset (ℝ × ℝ)).card = 2 := Finset.card_pair hpx
      calc (S₁ ∩ S₂).card ≥ ({p, x} : Finset (ℝ × ℝ)).card := by
            apply Finset.card_le_card
            intro y hy; simp at hy
            rcases hy with rfl | rfl
            · exact hp_inter
            · exact hx_inter
        _ = 2 := this
    -- But four_collinear_overlap_small says ≤ 1
    have h_inter_le := four_collinear_overlap_small P hP S₁ S₂
      hS₁_sub hS₂_sub hcard₁ hcard₂ hne a₁ b₁ hab₁ ha₁ hb₁ hcol₁ a₂ b₂ hab₂ ha₂ hb₂ hcol₂
    omega
  -- Count: 3 * |FP| ≤ |P.points.erase p| = n - 1
  -- via disjoint union of 3-element subsets
  have hbU_sub : FP.biUnion eraseMap ⊆ P.points.erase p := by
    intro x hx
    rw [Finset.mem_biUnion] at hx
    obtain ⟨S, hS, hxS⟩ := hx
    exact herase_sub S hS hxS
  have hbU_card : (FP.biUnion eraseMap).card = FP.sum (fun S => (eraseMap S).card) :=
    Finset.card_biUnion (fun S hS T hT hne => herase_disj S hS T hT hne)
  have hsum_eq : FP.sum (fun S => (eraseMap S).card) = 3 * FP.card := by
    rw [Finset.sum_const_nat (fun S hS => herase_card S hS)]; ring
  have herase_p_card : (P.points.erase p).card = P.points.card - 1 :=
    Finset.card_erase_of_mem hp
  have hle : 3 * FP.card ≤ P.points.card - 1 := by
    calc 3 * FP.card = (FP.biUnion eraseMap).card := by linarith [hbU_card, hsum_eq]
      _ ≤ (P.points.erase p).card := Finset.card_le_card hbU_sub
      _ = P.points.card - 1 := herase_p_card
  omega

/- ## Structural Lemmas for fourCollinearThrough -/

open Classical in
/-- fourCollinearThrough is a subset of fourCollinearFamily. -/
theorem fourCollinearThrough_sub_family (P : PlanarPointSet) (p : ℝ × ℝ) :
    fourCollinearThrough P p ⊆ fourCollinearFamily P := by
  intro S hS
  unfold fourCollinearThrough at hS
  unfold fourCollinearFamily
  rw [Finset.mem_filter] at hS ⊢
  exact ⟨hS.1, hS.2.1, hS.2.2.2⟩

open Classical in
/-- Each S in fourCollinearFamily appears in fourCollinearThrough for each of its points. -/
theorem mem_fourCollinearThrough_of_mem_family (P : PlanarPointSet)
    (S : Finset (ℝ × ℝ)) (hS : S ∈ fourCollinearFamily P) (p : ℝ × ℝ) (hp : p ∈ S) :
    S ∈ fourCollinearThrough P p := by
  unfold fourCollinearFamily at hS
  unfold fourCollinearThrough
  rw [Finset.mem_filter] at hS ⊢
  exact ⟨hS.1, hS.2.1, hp, hS.2.2⟩

/- ## Double-Counting Connection

    The per-point bound and global bound are connected by double counting:
    - Per-point: |fourCollinearThrough P p| ≤ (n-1)/3  (fourCollinearThrough_bound)
    - Global: |fourCollinearFamily P| ≤ n(n-1)/12  (improved_upper_bound)

    Each S ∈ F (with |S| = 4) appears in fourCollinearThrough(p) for exactly 4
    values of p ∈ P.points (by mem_fourCollinearThrough_of_mem_family).
    By summation interchange:
      Σ_{p ∈ P} |fourCollinearThrough(p)| = Σ_{S ∈ F} |S| = 4·|F|
    Combined with 3·|fourCollinearThrough(p)| ≤ n-1:
      12·|F| = 3·(4·|F|) = 3·Σ_p |fourCollinearThrough(p)| ≤ Σ_p (n-1) = n·(n-1)
    This reproves |F| ≤ n(n-1)/12 via double counting.

    Both the pair-packing proof (improved_upper_bound) and this per-point approach
    give the same tight bound. The bound n(n-1)/12 is optimal from pure
    combinatorial methods without geometric input.

    Closing the gap between O(n²) and o(n²) requires genuinely new ideas
    beyond what Szemerédi-Trotter or double counting can provide for k=4. -/
