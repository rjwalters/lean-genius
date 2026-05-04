import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Anning–Erdős Finiteness: Proof Infrastructure

Proves the Anning–Erdős theorem: any non-collinear planar point set with all
pairwise integer distances bounded by d has at most 2d² + 2 points.

## Proof sketch

Fix two anchor points P₁, P₂ ∈ S. Every other Q ∈ S lies on the intersection
of two circles (dist(Q,P₁) = k₁ and dist(Q,P₂) = k₂). Two distinct circles
intersect in at most 2 points (via the quadratic root bound). Since there are
d² possible distance pairs, |S| − 2 ≤ 2d², so |S| ≤ 2d² + 2.
-/

namespace Erdos100OQ01WIP01

open Real Finset

/-! ## Algebraic root bound -/

/-- A nonzero quadratic has at most 2 roots: given two distinct roots p, q,
    any third root must equal p or q. -/
lemma quadratic_at_most_two_roots (a b c : ℝ) (ha : a ≠ 0)
    (p q r : ℝ)
    (hp : a * p ^ 2 + b * p + c = 0)
    (hq : a * q ^ 2 + b * q + c = 0)
    (hpq : p ≠ q)
    (hr : a * r ^ 2 + b * r + c = 0) :
    r = p ∨ r = q := by
  have hsum : a * (p + q) + b = 0 := by
    have key : (p - q) * (a * (p + q) + b) = 0 := by
      have : (p - q) * (a * (p + q) + b) =
          (a * p ^ 2 + b * p + c) - (a * q ^ 2 + b * q + c) := by ring
      rw [this, hp, hq, sub_self]
    rcases mul_eq_zero.mp key with h | h
    · exact absurd (sub_eq_zero.mp h) hpq
    · exact h
  rcases eq_or_ne r p with rfl | hrp
  · exact Or.inl rfl
  · right
    have hsum2 : a * (r + p) + b = 0 := by
      have key : (r - p) * (a * (r + p) + b) = 0 := by
        have : (r - p) * (a * (r + p) + b) =
            (a * r ^ 2 + b * r + c) - (a * p ^ 2 + b * p + c) := by ring
        rw [this, hr, hp, sub_self]
      rcases mul_eq_zero.mp key with h | h
      · exact absurd (sub_eq_zero.mp h) hrp
      · exact h
    linarith [mul_left_cancel₀ ha (show a * (p + q) = a * (r + p) by linarith)]

/-! ## Circle intersection lemma -/

/-- Three distinct points cannot simultaneously lie on two circles with distinct centers. -/
theorem three_pts_two_circles_contra
    (c₁ c₂ : ℝ × ℝ) (r₁ r₂ : ℝ)
    (hc : c₁ ≠ c₂)
    (p q s : ℝ × ℝ)
    (hpq : p ≠ q) (hps : p ≠ s) (hqs : q ≠ s)
    (hp1 : (p.1 - c₁.1) ^ 2 + (p.2 - c₁.2) ^ 2 = r₁ ^ 2)
    (hp2 : (p.1 - c₂.1) ^ 2 + (p.2 - c₂.2) ^ 2 = r₂ ^ 2)
    (hq1 : (q.1 - c₁.1) ^ 2 + (q.2 - c₁.2) ^ 2 = r₁ ^ 2)
    (hq2 : (q.1 - c₂.1) ^ 2 + (q.2 - c₂.2) ^ 2 = r₂ ^ 2)
    (hs1 : (s.1 - c₁.1) ^ 2 + (s.2 - c₁.2) ^ 2 = r₁ ^ 2)
    (hs2 : (s.1 - c₂.1) ^ 2 + (s.2 - c₂.2) ^ 2 = r₂ ^ 2) :
    False := by
  -- Subtracting the two circle equations gives the radical axis: a linear relation.
  -- K is the constant; dx, dy are the signed center differences.
  set K := r₁ ^ 2 - r₂ ^ 2 + (c₂.1 ^ 2 + c₂.2 ^ 2) - (c₁.1 ^ 2 + c₁.2 ^ 2)
  set dx := c₂.1 - c₁.1
  set dy := c₂.2 - c₁.2
  -- Every point on both circles satisfies 2*dx*x + 2*dy*y = K
  have hrad_p : 2 * dx * p.1 + 2 * dy * p.2 = K := by simp only [K, dx, dy]; nlinarith
  have hrad_q : 2 * dx * q.1 + 2 * dy * q.2 = K := by simp only [K, dx, dy]; nlinarith
  have hrad_s : 2 * dx * s.1 + 2 * dy * s.2 = K := by simp only [K, dx, dy]; nlinarith
  -- (dx, dy) ≠ (0, 0) since c₁ ≠ c₂
  have hdc : dx ≠ 0 ∨ dy ≠ 0 := by
    rcases c₁ with ⟨x₁, y₁⟩; rcases c₂ with ⟨x₂, y₂⟩
    by_contra h; push_neg at h
    exact hc (Prod.ext (by simp [dx] at h; linarith [h.1])
                       (by simp [dy] at h; linarith [h.2]))
  rcases eq_or_ne dx 0 with hdx0 | hdx
  · -- dx = 0, so dy ≠ 0
    have hdy : dy ≠ 0 := by rcases hdc with h | h; · exact absurd hdx0 h; · exact h
    have hdy2 : 2 * dy ≠ 0 := mul_ne_zero two_ne_zero hdy
    -- Radical axis: 2*dy*y = K, so all three points have the same y-coordinate
    have hpy : p.2 * (2 * dy) = K := by
      have := hrad_p; simp [hdx0] at this; linarith
    have hqy : q.2 * (2 * dy) = K := by
      have := hrad_q; simp [hdx0] at this; linarith
    have hsy : s.2 * (2 * dy) = K := by
      have := hrad_s; simp [hdx0] at this; linarith
    have hpeqq : p.2 = q.2 := mul_right_cancel₀ hdy2 (by linarith)
    have hpeqs : p.2 = s.2 := mul_right_cancel₀ hdy2 (by linarith)
    -- Substitute fixed y into circle 1: quadratic in x
    -- (x - c₁.1)² = r₁² - (y₀ - c₁.2)²
    -- Quadratic: 1*x² + (-2*c₁.1)*x + (c₁.1² + (p.2-c₁.2)² - r₁²) = 0
    set A := (1 : ℝ)
    set B := -2 * c₁.1
    set C := c₁.1 ^ 2 + (p.2 - c₁.2) ^ 2 - r₁ ^ 2
    have hA : A ≠ 0 := one_ne_zero
    have hquad_p : A * p.1 ^ 2 + B * p.1 + C = 0 := by
      simp only [A, B, C]; nlinarith [hp1]
    have hquad_q : A * q.1 ^ 2 + B * q.1 + C = 0 := by
      simp only [A, B, C]; nlinarith [hq1, hpeqq.symm]
    have hquad_s : A * s.1 ^ 2 + B * s.1 + C = 0 := by
      simp only [A, B, C]; nlinarith [hs1, hpeqs.symm]
    have hpx_ne_qx : p.1 ≠ q.1 := fun h => hpq (Prod.ext h hpeqq)
    rcases quadratic_at_most_two_roots A B C hA p.1 q.1 s.1
        hquad_p hquad_q hpx_ne_qx hquad_s with h | h
    · exact hps (Prod.ext h hpeqs)
    · exact hqs (Prod.ext h (hpeqq ▸ hpeqs))
  · -- dx ≠ 0: express x from radical axis, substitute into circle 1 → quadratic in y
    have hdx2 : 2 * dx ≠ 0 := mul_ne_zero two_ne_zero hdx
    -- Radical axis: p.1*(2*dx) = K - 2*dy*p.2
    have hpx : p.1 * (2 * dx) = K - 2 * dy * p.2 := by linarith
    have hqx : q.1 * (2 * dx) = K - 2 * dy * q.2 := by linarith
    have hsx : s.1 * (2 * dx) = K - 2 * dy * s.2 := by linarith
    -- If two points share y-coord, they share x-coord (from radical axis) → same point
    have hpy_ne_qy : p.2 ≠ q.2 := fun h =>
      hpq (Prod.ext (mul_left_cancel₀ hdx2 (by linarith)) h)
    have hpy_ne_sy : p.2 ≠ s.2 := fun h =>
      hps (Prod.ext (mul_left_cancel₀ hdx2 (by linarith)) h)
    have hqy_ne_sy : q.2 ≠ s.2 := fun h =>
      hqs (Prod.ext (mul_left_cancel₀ hdx2 (by linarith)) h)
    -- Substitute into circle 1: ((K-2*dy*y) - c₁.1*(2*dx))² + (2*dx)²*(y-c₁.2)² = r₁²*(2*dx)²
    -- Set α = K - 2*dx*c₁.1 = p.1*(2*dx) + 2*dy*p.2 - ... wait, just use the substituted form
    -- Quadratic coefficients in y:
    --   A = (2*dy)² + (2*dx)²
    --   B = -2*(K - 2*dx*c₁.1)*(2*dy) - 2*(2*dx)²*c₁.2
    --   C = (K - 2*dx*c₁.1)² + (2*dx)²*c₁.2² - r₁²*(2*dx)²
    set α := K - 2 * dx * c₁.1
    set A := (2 * dy) ^ 2 + (2 * dx) ^ 2
    set B := -2 * α * (2 * dy) - 2 * (2 * dx) ^ 2 * c₁.2
    set C := α ^ 2 + (2 * dx) ^ 2 * c₁.2 ^ 2 - r₁ ^ 2 * (2 * dx) ^ 2
    have hA : A ≠ 0 := by
      simp only [A, ne_eq]
      intro heq
      have h1 : (2 * dy) ^ 2 ≥ 0 := sq_nonneg _
      have h2 : (2 * dx) ^ 2 ≥ 0 := sq_nonneg _
      have h3 : (2 * dx) ^ 2 = 0 := by linarith
      exact hdx2 (pow_eq_zero_iff (by norm_num) |>.mp h3)
    -- Key: multiplying circle 1 by (2*dx)² and substituting gives the quadratic
    have key_p : (K - 2 * dy * p.2 - c₁.1 * (2 * dx)) ^ 2 +
        (2 * dx) ^ 2 * (p.2 - c₁.2) ^ 2 = r₁ ^ 2 * (2 * dx) ^ 2 := by
      have step : K - 2 * dy * p.2 - c₁.1 * (2 * dx) = (p.1 - c₁.1) * (2 * dx) := by
        linear_combination -hpx
      rw [step]; linear_combination (2 * dx) ^ 2 * hp1
    have key_q : (K - 2 * dy * q.2 - c₁.1 * (2 * dx)) ^ 2 +
        (2 * dx) ^ 2 * (q.2 - c₁.2) ^ 2 = r₁ ^ 2 * (2 * dx) ^ 2 := by
      have step : K - 2 * dy * q.2 - c₁.1 * (2 * dx) = (q.1 - c₁.1) * (2 * dx) := by
        linear_combination -hqx
      rw [step]; linear_combination (2 * dx) ^ 2 * hq1
    have key_s : (K - 2 * dy * s.2 - c₁.1 * (2 * dx)) ^ 2 +
        (2 * dx) ^ 2 * (s.2 - c₁.2) ^ 2 = r₁ ^ 2 * (2 * dx) ^ 2 := by
      have step : K - 2 * dy * s.2 - c₁.1 * (2 * dx) = (s.1 - c₁.1) * (2 * dx) := by
        linear_combination -hsx
      rw [step]; linear_combination (2 * dx) ^ 2 * hs1
    have hquad_p : A * p.2 ^ 2 + B * p.2 + C = 0 := by
      simp only [A, B, C, α]; linear_combination key_p
    have hquad_q : A * q.2 ^ 2 + B * q.2 + C = 0 := by
      simp only [A, B, C, α]; linear_combination key_q
    have hquad_s : A * s.2 ^ 2 + B * s.2 + C = 0 := by
      simp only [A, B, C, α]; linear_combination key_s
    rcases quadratic_at_most_two_roots A B C hA p.2 q.2 s.2
        hquad_p hquad_q hpy_ne_qy hquad_s with h | h
    · exact hps (Prod.ext (mul_left_cancel₀ hdx2 (by linarith)) h)
    · exact hqs (Prod.ext (mul_left_cancel₀ hdx2 (by linarith)) h)

/-! ## Cardinality bound -/

/-- A non-collinear integer-distance set with distances ≤ d has at most 2d² + 2 points.

    The bound follows from fixing two anchor points and counting fibers of the
    distance-pair map: each fiber has ≤ 2 elements (two-circle intersection). -/
theorem int_dist_card_le
    (S : Finset (ℝ × ℝ)) (d : ℕ)
    (hS_dist : ∀ p ∈ S, ∀ q ∈ S, p ≠ q →
      ∃ k : ℕ, 0 < k ∧ k ≤ d ∧
        (p.1 - q.1) ^ 2 + (p.2 - q.2) ^ 2 = (k : ℝ) ^ 2)
    (hS_noncol : ¬∀ p ∈ S, ∀ q ∈ S, ∀ r ∈ S,
      (p.1 - r.1) * (q.2 - r.2) = (q.1 - r.1) * (p.2 - r.2)) :
    S.card ≤ 2 * d ^ 2 + 2 := by
  -- Fix two distinct anchor points P₁, P₂ ∈ S
  -- For Q ∈ S \ {P₁,P₂}: distance pair (k₁,k₂) ∈ {1..d}², at most d² choices
  -- Each choice gives ≤ 2 points (by three_pts_two_circles_contra)
  -- So |S| - 2 ≤ 2*d², hence |S| ≤ 2*d² + 2
  sorry

/-! ## Main theorem -/

/-- **Anning–Erdős Theorem** (1945): For any d, every non-collinear planar set
    with all pairwise integer distances ≤ d has at most 2d² + 2 points. -/
theorem anning_erdos_finiteness :
    ∀ d : ℕ, ∃ N : ℕ, ∀ n : ℕ, n > N →
      ¬∃ (S : Finset (ℝ × ℝ)), S.card = n ∧
        (∀ p ∈ S, ∀ q ∈ S, p ≠ q → ∃ k : ℕ, 0 < k ∧ k ≤ d ∧
          (p.1 - q.1) ^ 2 + (p.2 - q.2) ^ 2 = ↑(k ^ 2)) ∧
        ¬(∀ p ∈ S, ∀ q ∈ S, ∀ r ∈ S,
          (p.1 - r.1) * (q.2 - r.2) = (q.1 - r.1) * (p.2 - r.2)) := by
  intro d
  refine ⟨2 * d ^ 2 + 2, fun n hn => ?_⟩
  rintro ⟨S, hScard, hSdist, hSnoncol⟩
  have hSdist' : ∀ p ∈ S, ∀ q ∈ S, p ≠ q →
      ∃ k : ℕ, 0 < k ∧ k ≤ d ∧
        (p.1 - q.1) ^ 2 + (p.2 - q.2) ^ 2 = (k : ℝ) ^ 2 := by
    intro p hp q hq hpq
    obtain ⟨k, hkpos, hkle, hkeq⟩ := hSdist p hp q hq hpq
    exact ⟨k, hkpos, hkle, by push_cast [sq] at hkeq ⊢; linarith⟩
  linarith [int_dist_card_le S d hSdist' hSnoncol, hScard ▸ (le_refl S.card)]

end Erdos100OQ01WIP01
