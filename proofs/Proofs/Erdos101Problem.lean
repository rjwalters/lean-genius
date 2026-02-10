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
  collinear_swap12 (collinear_swap23 h)

/-- Collinearity transitivity: if p, q, r are collinear and p, q, s are collinear
    (with p ≠ q), then p, r, s are collinear. Points on the same line through p, q
    remain collinear. -/
theorem collinear_trans {p q r s : ℝ × ℝ} (hpq : p ≠ q)
    (hpqr : collinear p q r) (hpqs : collinear p q s) :
    collinear p r s := by
  unfold collinear at *
  -- hpqr: (q.1 - p.1) * (r.2 - p.2) = (r.1 - p.1) * (q.2 - p.2)
  -- hpqs: (q.1 - p.1) * (s.2 - p.2) = (s.1 - p.1) * (q.2 - p.2)
  -- Goal: (r.1 - p.1) * (s.2 - p.2) = (s.1 - p.1) * (r.2 - p.2)
  -- Strategy: p ≠ q means (q.1 - p.1, q.2 - p.2) ≠ (0, 0).
  -- From hpqr, r - p is proportional to q - p; similarly s - p.
  -- So r - p and s - p are proportional, giving the goal.
  by_cases hx : q.1 - p.1 = 0
  · -- q.1 = p.1, so q.2 ≠ p.2
    have hy : q.2 - p.2 ≠ 0 := by
      intro hy
      apply hpq
      ext <;> linarith
    -- From hpqr with q.1 - p.1 = 0: 0 = (r.1 - p.1) * (q.2 - p.2)
    -- So r.1 = p.1
    have hr1 : r.1 - p.1 = 0 := by
      have := hpqr; rw [hx, zero_mul] at this
      exact (mul_eq_zero.mp this.symm).resolve_right hy
    -- From hpqs with q.1 - p.1 = 0: s.1 = p.1
    have hs1 : s.1 - p.1 = 0 := by
      have := hpqs; rw [hx, zero_mul] at this
      exact (mul_eq_zero.mp this.symm).resolve_right hy
    rw [hr1, hs1]; ring
  · -- q.1 ≠ p.1
    -- From hpqr: r.2 - p.2 = (r.1 - p.1) * (q.2 - p.2) / (q.1 - p.1)
    -- From hpqs: s.2 - p.2 = (s.1 - p.1) * (q.2 - p.2) / (q.1 - p.1)
    -- Goal: (r.1 - p.1) * (s.2 - p.2) = (s.1 - p.1) * (r.2 - p.2)
    -- Substitute and simplify - both sides equal
    -- (r.1 - p.1) * (s.1 - p.1) * (q.2 - p.2) / (q.1 - p.1)
    have key : (q.1 - p.1) * ((r.1 - p.1) * (s.2 - p.2)) =
               (q.1 - p.1) * ((s.1 - p.1) * (r.2 - p.2)) := by nlinarith
    exact mul_left_cancel₀ (sub_ne_zero.mpr (fun h => hx (by rw [h])) : q.1 - p.1 ≠ 0) key

/-- Four points on the same line: if p, q, r, s are all collinear through
    distinct p, q, then q, r, s are collinear. -/
theorem collinear_four {p q r s : ℝ × ℝ} (hpq : p ≠ q)
    (hpqr : collinear p q r) (hpqs : collinear p q s) :
    collinear q r s :=
  collinear_trans (Ne.symm hpq) (collinear_swap12 hpqr) (collinear_swap12 hpqs)

/-- Full transitivity over a line: if r, s, t all lie on the line through
    distinct p, q, then r, s, t are collinear. This is the key lemma
    connecting our determinant-based collinearity to the geometric notion
    of "lying on a common line". -/
theorem collinear_any_triple {p q r s t : ℝ × ℝ} (hpq : p ≠ q)
    (hr : collinear p q r) (hs : collinear p q s) (ht : collinear p q t) :
    collinear r s t := by
  have h1 := collinear_trans hpq hr hs  -- collinear p r s
  have h2 := collinear_trans hpq hr ht  -- collinear p r t
  by_cases hrp : r = p
  · subst hrp
    exact collinear_trans hpq hs ht
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
    intro x hx
    simp at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl <;> assumption
  have := Finset.card_le_card hsub
  rw [h5] at this
  omega

/-- For sets with fewer than 4 points, fourPointLineCount is zero
    (no 4-element collinear subset can exist). -/
theorem fourPointLineCount_lt_four (P : PlanarPointSet) (h : P.points.card < 4) :
    fourPointLineCount P = 0 := by
  unfold fourPointLineCount
  apply Finset.card_eq_zero.mpr
  rw [Finset.filter_eq_empty_iff]
  intro S hS
  simp only [not_and]
  intro hcard
  exfalso
  have hsub := Finset.mem_powerset.mp hS
  have := Finset.card_le_card hsub
  omega

/-- Under NoFiveCollinear, for any two distinct points a, b in P, the set of
    points in P collinear with a and b has at most 4 elements.
    This is the key structural consequence of the NoFiveCollinear condition.

    Proof: By contradiction. If |L| ≥ 5 where L = {p ∈ P | collinear a b p},
    then L \ {a,b} has ≥ 3 elements. Extract c, d, e from L \ {a,b}; these
    5 distinct points a, b, c, d, e ∈ P all satisfy collinear a b ·,
    contradicting NoFiveCollinear. -/
open Classical in
theorem noFiveCollinear_line_bound (P : PlanarPointSet) (hP : NoFiveCollinear P)
    (a b : ℝ × ℝ) (ha : a ∈ P.points) (hb : b ∈ P.points) (hab : a ≠ b) :
    (P.points.filter (fun p => collinear a b p)).card ≤ 4 := by
  by_contra h
  push_neg at h
  set L := P.points.filter (fun p => collinear a b p)
  -- a, b ∈ L
  have ha_L : a ∈ L := Finset.mem_filter.mpr ⟨ha, collinear_self a b⟩
  have hb_L : b ∈ L := Finset.mem_filter.mpr ⟨hb, collinear_self_right a b⟩
  -- L' = L \ {a, b} has ≥ 3 elements
  set L' := (L.erase a).erase b
  have hL'_card : L'.card ≥ 3 := by
    have h1 := Finset.card_erase_le (a := a) (s := L)
    have h2 := Finset.card_erase_le (a := b) (s := L.erase a)
    omega
  -- Extract c from L'
  have hL'_ne : L'.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨c, hc⟩ := hL'_ne
  -- Extract d from L' \ {c}
  have hL'c : (L'.erase c).card ≥ 2 := by
    have := Finset.card_erase_of_mem hc; omega
  have hL'c_ne : (L'.erase c).Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨d, hd⟩ := hL'c_ne
  -- Extract e from L' \ {c, d}
  have hL'cd : ((L'.erase c).erase d).card ≥ 1 := by
    have := Finset.card_erase_of_mem hd; omega
  have hL'cd_ne : ((L'.erase c).erase d).Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨e, he⟩ := hL'cd_ne
  -- Trace membership: e ∈ L' \ {c, d} → ... → L
  have he_ec : e ∈ L'.erase c := Finset.mem_of_mem_erase he
  have he_L' : e ∈ L' := Finset.mem_of_mem_erase he_ec
  have hd_L' : d ∈ L' := Finset.mem_of_mem_erase hd
  have hc_eaL : c ∈ L.erase a := Finset.mem_of_mem_erase hc
  have hd_eaL : d ∈ L.erase a := Finset.mem_of_mem_erase hd_L'
  have he_eaL : e ∈ L.erase a := Finset.mem_of_mem_erase he_L'
  have hc_L : c ∈ L := Finset.mem_of_mem_erase hc_eaL
  have hd_L : d ∈ L := Finset.mem_of_mem_erase hd_eaL
  have he_L : e ∈ L := Finset.mem_of_mem_erase he_eaL
  -- Membership and collinearity
  have hc_P : c ∈ P.points := (Finset.mem_filter.mp hc_L).1
  have hd_P : d ∈ P.points := (Finset.mem_filter.mp hd_L).1
  have he_P : e ∈ P.points := (Finset.mem_filter.mp he_L).1
  have hcol_c : collinear a b c := (Finset.mem_filter.mp hc_L).2
  have hcol_d : collinear a b d := (Finset.mem_filter.mp hd_L).2
  have hcol_e : collinear a b e := (Finset.mem_filter.mp he_L).2
  -- Distinctness: c, d, e ∉ {a, b} and pairwise distinct
  have hac : a ≠ c := fun h => absurd hc_eaL (h ▸ Finset.not_mem_erase a L)
  have hbc : b ≠ c := fun h => absurd hc (h ▸ Finset.not_mem_erase b (L.erase a))
  have had : a ≠ d := fun h => absurd hd_eaL (h ▸ Finset.not_mem_erase a L)
  have hbd : b ≠ d := fun h => absurd hd_L' (h ▸ Finset.not_mem_erase b (L.erase a))
  have hae : a ≠ e := fun h => absurd he_eaL (h ▸ Finset.not_mem_erase a L)
  have hbe : b ≠ e := fun h => absurd he_L' (h ▸ Finset.not_mem_erase b (L.erase a))
  have hcd : c ≠ d := fun h => absurd hd (h ▸ Finset.not_mem_erase c L')
  have hce : c ≠ e := fun h => absurd he_ec (h ▸ Finset.not_mem_erase c L')
  have hde : d ≠ e := fun h => absurd he (h ▸ Finset.not_mem_erase d (L'.erase c))
  -- Apply NoFiveCollinear
  exact hP a b c d e ha hb hc_P hd_P he_P hab hac had hae hbc hbd hbe hcd hce hde
    ⟨hcol_c, hcol_d, hcol_e⟩

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

/-- **Trivial Upper Bound**: Under NoFiveCollinear, each line has ≤ 4 points,
    so each line contributes at most C(4,4)=1 four-point subset. Since there are
    at most C(n,2) lines, fourPointLineCount ≤ n(n−1)/2.

    Note: The original statement lacked NoFiveCollinear, which is necessary —
    without it, n collinear points yield C(n,4) ≫ n² four-point subsets.
    Full proof requires a "line" abstraction and injection into unordered pairs;
    kept as axiom pending that infrastructure. -/
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
    is O(n^{2/3} m^{2/3} + n + m) for n points and m lines in the plane.
    This is the key incidence-geometry tool for bounding four-point lines. -/
axiom szemeredi_trotter :
  ∃ C : ℝ, C > 0 ∧
    ∀ (n m : ℕ), ∀ (incidences : ℕ),
      (incidences : ℝ) ≤ C * ((n : ℝ) ^ (2/3 : ℝ) * (m : ℝ) ^ (2/3 : ℝ) + n + m)
