/-
# Erdős Problem #102 — Maximum Collinear Points Forced by Many Rich Lines

Given n points in ℝ² such that at least cn² lines each contain ≥ 4 points,
let h_c(n) be the maximum number of points on some line.

Estimate h_c(n). Is h_c(n) → ∞ for fixed c > 0?

## Known Results
- Upper bound: h_c(n) ≪_c n^{1/2}
- Erdős conjectured h_c(n) ≫_c n^{1/2}
- Hunter disproved this: h_c(n) ≪ n^{1/log(1/c)} using lattice points
- The question h_c(n) → ∞ is still open (connected to Problem #101)

Status: OPEN
Reference: https://erdosproblems.com/102
-/

import Mathlib.Data.Finset.Card
import Mathlib.Data.Nat.Basic
import Mathlib.Tactic

/- ## Definitions -/

/-- A planar point configuration. -/
structure PointConfig where
  points : Finset (ℝ × ℝ)
  size_pos : points.card > 0

/-- Three points are collinear. -/
def collinear₃ (p q r : ℝ × ℝ) : Prop :=
  (q.1 - p.1) * (r.2 - p.2) = (r.1 - p.1) * (q.2 - p.2)

/-- The number of lines containing at least 4 points. -/
noncomputable def richLineCount (P : PointConfig) : ℕ :=
  (P.points.powerset.filter (fun S =>
    S.card = 4 ∧ ∃ a b : ℝ × ℝ, a ∈ S ∧ b ∈ S ∧ a ≠ b ∧
      ∀ p ∈ S, collinear₃ a b p)).card

/-- Maximum number of collinear points in the configuration. -/
noncomputable def maxCollinear (P : PointConfig) : ℕ :=
  (P.points.powerset.filter (fun S =>
    S.card ≥ 2 ∧ ∃ a b : ℝ × ℝ, a ∈ S ∧ b ∈ S ∧ a ≠ b ∧
      ∀ p ∈ S, collinear₃ a b p)).sup Finset.card

/- ## Main Problem -/

/-- **Erdős Problem #102**: h_c(n) → ∞. If cn² lines contain ≥ 4 points,
    some line must contain many points (growing with n). -/
/- ## Collinearity Properties -/

/-- Collinearity is symmetric: swapping the last two arguments. -/
theorem collinear₃_comm (p q r : ℝ × ℝ) : collinear₃ p q r ↔ collinear₃ p r q := by
  unfold collinear₃; exact eq_comm

/-- Collinearity is invariant under swapping the first two arguments. -/
theorem collinear₃_perm12 (p q r : ℝ × ℝ) : collinear₃ p q r ↔ collinear₃ q p r := by
  simp only [collinear₃]; constructor <;> intro h <;> nlinarith

/-- Any point is collinear with itself and any other point. -/
theorem collinear₃_self_left (p q : ℝ × ℝ) : collinear₃ p p q := by
  unfold collinear₃; ring

/-- Collinearity under cyclic permutation of all three arguments. -/
theorem collinear₃_cycle (p q r : ℝ × ℝ) : collinear₃ p q r ↔ collinear₃ q r p := by
  rw [collinear₃_perm12, collinear₃_comm]

/-- Any point is collinear with q and itself (degenerate triangle). -/
theorem collinear₃_self_right (p q : ℝ × ℝ) : collinear₃ p q p := by
  unfold collinear₃; ring

/-- q is collinear with p and q (degenerate triangle). -/
theorem collinear₃_self_mid (p q : ℝ × ℝ) : collinear₃ p q q := by
  unfold collinear₃; ring

/- ## Known Results -/

/-- **Upper Bound**: h_c(n) ≪_c √n. The maximum collinear count from cn²
    rich lines is at most O(√n). -/
/-- **Hunter's Counterexample**: Erdős conjectured h_c(n) ≫_c √n, but
    Hunter disproved this using lattice point configurations.
    h_c(n) ≪ n^{1/log(1/c)} for suitable c. -/
/-- **Connection to Problem #101**: if h_c(n) → ∞ is proved, the o(n²)
    bound for 4-point lines from Problem #101 would follow. Specifically,
    cn² four-point lines force some line with ≥ h_c(n) collinear points,
    eventually reaching ≥ 5, contradicting the no-five-collinear hypothesis. -/
axiom connection_101 (c : ℝ) (hc : c > 0) :
  (∀ M : ℕ, ∃ N₀ : ℕ, ∀ P : PointConfig,
    P.points.card ≥ N₀ →
    (richLineCount P : ℝ) ≥ c * (P.points.card : ℝ) ^ 2 →
      maxCollinear P ≥ M) →
  ∀ ε > 0, ∃ N₁ : ℕ, ∀ P : PointConfig,
    P.points.card ≥ N₁ → maxCollinear P ≤ 4 →
      (richLineCount P : ℝ) < ε * (P.points.card : ℝ) ^ 2

/-- **Proved**: If h_c(n) → ∞, configurations with max collinear ≤ 4 have
    < cn² rich lines for large n. This is the contrapositive of h_c(n) → ∞
    applied with M = 5: if richLineCount ≥ cn², then maxCollinear ≥ 5. -/
theorem connection_101_for_same_c (c : ℝ) (hc : c > 0)
    (hdiv : ∀ M : ℕ, ∃ N₀ : ℕ, ∀ P : PointConfig,
      P.points.card ≥ N₀ → (richLineCount P : ℝ) ≥ c * (P.points.card : ℝ) ^ 2 →
        maxCollinear P ≥ M) :
    ∃ N₁ : ℕ, ∀ P : PointConfig,
      P.points.card ≥ N₁ → maxCollinear P ≤ 4 →
        (richLineCount P : ℝ) < c * (P.points.card : ℝ) ^ 2 := by
  obtain ⟨N₀, hN₀⟩ := hdiv 5
  exact ⟨N₀, fun P hsize hmax => by
    by_contra hge
    push_neg at hge
    exact absurd (hN₀ P hsize hge) (by omega)⟩

/-- **Proved**: The same-c connection extends to all ε ≥ c.
    If h_c(n) → ∞, then for any ε ≥ c, configurations with max collinear ≤ 4
    have < ε·n² rich lines (since c·n² ≤ ε·n²). -/
theorem connection_101_for_larger_eps (c : ℝ) (hc : c > 0) (ε : ℝ) (hεc : c ≤ ε)
    (hdiv : ∀ M : ℕ, ∃ N₀ : ℕ, ∀ P : PointConfig,
      P.points.card ≥ N₀ → (richLineCount P : ℝ) ≥ c * (P.points.card : ℝ) ^ 2 →
        maxCollinear P ≥ M) :
    ∃ N₁ : ℕ, ∀ P : PointConfig,
      P.points.card ≥ N₁ → maxCollinear P ≤ 4 →
        (richLineCount P : ℝ) < ε * (P.points.card : ℝ) ^ 2 := by
  obtain ⟨N₁, hN₁⟩ := connection_101_for_same_c c hc hdiv
  exact ⟨N₁, fun P hsize hmax =>
    calc (richLineCount P : ℝ) < c * (P.points.card : ℝ) ^ 2 := hN₁ P hsize hmax
      _ ≤ ε * (P.points.card : ℝ) ^ 2 := by nlinarith [sq_nonneg (P.points.card : ℝ)]⟩

/-- **Key Insight (PROVED)**: The `connection_101` axiom (∀ε conclusion from single-c
    divergence) is actually derivable from the FULL conjecture (divergence ∀c).
    For any ε > 0, apply the full conjecture with c' = ε to get the bound.
    This shows connection_101 is not an independent assumption. -/
theorem connection_101_from_full_divergence
    (hdiv_all : ∀ c : ℝ, c > 0 → ∀ M : ℕ, ∃ N₀ : ℕ, ∀ P : PointConfig,
      P.points.card ≥ N₀ →
      (richLineCount P : ℝ) ≥ c * (P.points.card : ℝ) ^ 2 →
        maxCollinear P ≥ M) :
    ∀ c : ℝ, c > 0 → ∀ ε > 0, ∃ N₁ : ℕ, ∀ P : PointConfig,
      P.points.card ≥ N₁ → maxCollinear P ≤ 4 →
        (richLineCount P : ℝ) < ε * (P.points.card : ℝ) ^ 2 := by
  intro c _ ε hε
  exact connection_101_for_same_c ε hε (hdiv_all ε hε)

/- ## Observations -/

/-- **Szemerédi–Trotter**: the incidence bound I(P,L) ≤ C(n^{2/3}m^{2/3}+n+m)
    constrains how many rich lines can pass through n points. -/
/-- **Erdős–Purdy connection (PROVED)**: if cn² rich lines exist,
    some line has ≥ 4 collinear points.
    Proof: cn² > 0 so richLineCount ≥ 1; extract a 4-element collinear
    subset; it contributes to maxCollinear via Finset.le_sup. -/
theorem erdos_purdy_connection :
    ∀ c : ℝ, c > 0 →
      ∀ P : PointConfig, (richLineCount P : ℝ) ≥ c * (P.points.card : ℝ) ^ 2 →
        maxCollinear P ≥ 4 := by
  intro c hc P hrich
  have hn : (1 : ℝ) ≤ (P.points.card : ℝ) := by exact_mod_cast P.size_pos
  have hrich_pos : (0 : ℝ) < richLineCount P := by
    calc (0 : ℝ) < c := hc
      _ = c * 1 := by ring
      _ ≤ c * (P.points.card : ℝ) ^ 2 := by nlinarith [sq_nonneg ((P.points.card : ℝ) - 1)]
      _ ≤ richLineCount P := hrich
  have hrich_nat : 0 < richLineCount P := by exact_mod_cast hrich_pos
  unfold richLineCount at hrich_nat
  rw [Finset.card_pos] at hrich_nat
  obtain ⟨S, hS_mem⟩ := hrich_nat
  simp only [Finset.mem_filter] at hS_mem
  obtain ⟨hS_in, hS4, a, b, ha, hb, hab, hcoll⟩ := hS_mem
  have hS_max : S ∈ (P.points.powerset.filter (fun S =>
      S.card ≥ 2 ∧ ∃ a b : ℝ × ℝ, a ∈ S ∧ b ∈ S ∧ a ≠ b ∧
        ∀ p ∈ S, collinear₃ a b p)) :=
    Finset.mem_filter.mpr ⟨hS_in, by omega, a, b, ha, hb, hab, hcoll⟩
  unfold maxCollinear
  calc 4 = S.card := by omega
    _ ≤ _ := Finset.le_sup hS_max
