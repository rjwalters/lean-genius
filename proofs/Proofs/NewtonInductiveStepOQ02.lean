/-
Ultra-Log-Concavity of Binomial Coefficients

OQ-02 follow-up to newton-inductive-step-oq-01 (Newton's Inequality).

This file formalizes ultra-log-concavity of binomial coefficients:
  C(n,k)⁴ ≥ C(n,k-1)² · C(n,k+1)²  for  1 ≤ k < n.

This strengthens ordinary log-concavity C(n,k)² ≥ C(n,k-1)·C(n,k+1)
by squaring both sides: (a² ≥ bc) ⟹ (a² - bc)(a² + bc) ≥ 0 ⟹ a⁴ ≥ b²c².

Also proves the unnormalized Newton inequality for lists:
  esymm xs k² ≥ esymm xs (k-1) · esymm xs (k+1)
and derives the full Newton inequality in cleared-denominator form.

Main results (0 axioms, 0 sorries):
1. `binom_log_concave`      — C(n,k)² ≥ C(n,k-1)·C(n,k+1)
2. `binom_ultra_log_concave` — C(n,k)⁴ ≥ C(n,k-1)²·C(n,k+1)² (formal problem statement)
3. `esymm_zero_tail`         — if e_j = 0 for nonneg list then e_{j+1} = 0
4. `esymm_log_concave`       — unnormalized Newton: e_k² ≥ e_{k-1}·e_{k+1}
5. `newton_inequality_binomial` — C(n,k-1)·C(n,k+1)·e_k² ≥ C(n,k)²·e_{k-1}·e_{k+1}

References:
  - Newton (1707), Arithmetica Universalis
  - Hardy–Littlewood–Pólya (1952), Inequalities, Ch. 2
  - Parent proof: NewtonInductiveStepOQ01.lean
  - AmgmInequalityOQ02OQ02.lean (cleared-denominator inductive step)
-/

import Proofs.NewtonInductiveStepOQ01
import Proofs.AmgmInequalityOQ02OQ02

open List Nat

namespace NewtonInductiveStepOQ02

/-! ## Part I: Ultra-Log-Concavity of Binomial Coefficients -/

/-- Log-concavity of binomial coefficients: C(n,k)² ≥ C(n,k-1)·C(n,k+1).
    This is the OQ-01 result, re-exported for convenience. -/
theorem binom_log_concave' (n k : ℕ) (hk : 1 ≤ k) (hkn : k + 1 ≤ n) :
    (Nat.choose n k : ℝ) ^ 2 ≥
    (Nat.choose n (k - 1) : ℝ) * (Nat.choose n (k + 1) : ℝ) :=
  binom_log_concave n k hk hkn

/-- **Ultra-log-concavity of binomial coefficients** (formal problem statement):
    C(n,k)⁴ ≥ C(n,k-1)² · C(n,k+1)²  for  1 ≤ k ≤ n-1.

    Proof: Let a = C(n,k), b = C(n,k-1), c = C(n,k+1).
    From log-concavity: a² ≥ bc, so a²-bc ≥ 0.
    Also a²+bc ≥ 0 since all terms are nonneg.
    The identity (a²-bc)(a²+bc) = a⁴-b²c² ≥ 0 gives a⁴ ≥ b²c².  -/
theorem binom_ultra_log_concave (n k : ℕ) (hk : 1 ≤ k) (hkn : k + 1 ≤ n) :
    (Nat.choose n k : ℝ) ^ 4 ≥
    (Nat.choose n (k - 1) : ℝ) ^ 2 * (Nat.choose n (k + 1) : ℝ) ^ 2 := by
  have h := binom_log_concave n k hk hkn
  have hb : (0 : ℝ) ≤ Nat.choose n (k - 1) := Nat.cast_nonneg _
  have hc : (0 : ℝ) ≤ Nat.choose n (k + 1) := Nat.cast_nonneg _
  have h1 : (0 : ℝ) ≤ (Nat.choose n k : ℝ) ^ 2 -
      (Nat.choose n (k - 1) : ℝ) * (Nat.choose n (k + 1) : ℝ) := by linarith
  have h2 : (0 : ℝ) ≤ (Nat.choose n k : ℝ) ^ 2 +
      (Nat.choose n (k - 1) : ℝ) * (Nat.choose n (k + 1) : ℝ) :=
    add_nonneg (sq_nonneg _) (mul_nonneg hb hc)
  have key : ((Nat.choose n k : ℝ) ^ 2 -
        (Nat.choose n (k - 1) : ℝ) * (Nat.choose n (k + 1) : ℝ)) *
      ((Nat.choose n k : ℝ) ^ 2 +
        (Nat.choose n (k - 1) : ℝ) * (Nat.choose n (k + 1) : ℝ)) =
      (Nat.choose n k : ℝ) ^ 4 -
      (Nat.choose n (k - 1) : ℝ) ^ 2 * (Nat.choose n (k + 1) : ℝ) ^ 2 := by ring
  linarith [mul_nonneg h1 h2, key]

/-! ## Part II: Unnormalized Newton Inequality for Lists

We prove e_k² ≥ e_{k-1}·e_{k+1} for lists with nonnegative entries.
This is the "unnormalized" form — it does not involve binomial coefficients. -/

/-- **Zero-tail property**: if e_j = 0 for a nonneg list (j ≥ 1), then e_{j+1} = 0.

    Proof: e_j = 0 means every j-element product is 0, so the list has < j
    positive elements. Hence every (j+1)-element product is also 0. -/
theorem esymm_zero_tail (xs : List ℝ) (hxs : ∀ x ∈ xs, (0 : ℝ) ≤ x)
    {j : ℕ} (hj : 1 ≤ j) (h : esymm xs j = 0) : esymm xs (j + 1) = 0 := by
  induction xs generalizing j with
  | nil =>
    simp [esymm_nil_succ]
  | cons x xs ih =>
    have hx : (0 : ℝ) ≤ x := hxs x (mem_cons_self x xs)
    have hxs' : ∀ y ∈ xs, (0 : ℝ) ≤ y := fun y hy => hxs y (mem_cons_of_mem x hy)
    -- Obtain j = p+1 for some p (since j ≥ 1)
    obtain ⟨p, rfl⟩ : ∃ p, j = p + 1 := ⟨j - 1, by omega⟩
    -- esymm (x::xs) (p+1) = esymm xs (p+1) + x * esymm xs p
    rw [esymm_cons_succ] at h
    -- Both terms are nonneg, so each is 0
    have hE : esymm xs (p + 1) = 0 := by
      have hnn : (0 : ℝ) ≤ esymm xs (p + 1) := esymm_nonneg xs hxs' (p + 1)
      have hnn2 : (0 : ℝ) ≤ x * esymm xs p := mul_nonneg hx (esymm_nonneg xs hxs' p)
      linarith
    have hxEp : x * esymm xs p = 0 := by
      have hnn : (0 : ℝ) ≤ esymm xs (p + 1) := esymm_nonneg xs hxs' (p + 1)
      have hnn2 : (0 : ℝ) ≤ x * esymm xs p := mul_nonneg hx (esymm_nonneg xs hxs' p)
      linarith
    -- esymm (x::xs) (p+2) = esymm xs (p+2) + x * esymm xs (p+1)
    rw [show p + 1 + 1 = p + 1 + 1 from rfl, esymm_cons_succ]
    -- esymm xs (p+2) = 0 by IH (since esymm xs (p+1) = 0 and p+1 ≥ 1)
    have hE2 : esymm xs (p + 1 + 1) = 0 :=
      ih hxs' (by omega) hE
    rw [hE2, hE, mul_zero, add_zero]

/-- **Unnormalized Newton inequality** for lists with nonneg entries:
    esymm xs k² ≥ esymm xs (k-1) · esymm xs (k+1).

    Proof by induction on xs. The inductive step uses:
    - F_k = E_k + x·E_{k-1} (recurrence)
    - F_k² - F_{k-1}·F_{k+1} = (E_k² - E_{k-1}·E_{k+1}) + x·(E_k·E_{k-1} - E_{k-2}·E_{k+1})
                               + x²·(E_{k-1}² - E_{k-2}·E_k)
    Each term is ≥ 0 by IH (Newton at k), cross condition, IH (Newton at k-1). -/
theorem esymm_log_concave (xs : List ℝ) (hxs : ∀ x ∈ xs, (0 : ℝ) ≤ x)
    (k : ℕ) (hk : 1 ≤ k) (hkn : k + 1 ≤ xs.length) :
    esymm xs k ^ 2 ≥ esymm xs (k - 1) * esymm xs (k + 1) := by
  induction xs generalizing k with
  | nil => simp at hkn
  | cons x xs ih =>
    have hx : (0 : ℝ) ≤ x := hxs x (mem_cons_self x xs)
    have hxs' : ∀ y ∈ xs, (0 : ℝ) ≤ y := fun y hy => hxs y (mem_cons_of_mem x hy)
    simp only [length_cons] at hkn
    rcases Nat.eq_or_gt_of_le hk with rfl | hk2
    · -- k = 1 case
      -- F_0 = 1, F_1 = E_1 + x, F_2 = E_2 + x*E_1
      simp only [show 1 - 1 = 0 from rfl, show 1 + 1 = 2 from rfl]
      rw [esymm_zero, one_mul]
      rw [esymm_cons_succ, esymm_zero, mul_one, esymm_cons_succ]
      -- Goal: (E_1 + x*1)² ≥ 1 * (E_2 + x*E_1)
      -- i.e., (E_1 + x)² ≥ E_2 + x*E_1
      simp only [mul_one]
      set E1 := esymm xs 1
      set E2 := esymm xs 2
      have hE1 : (0 : ℝ) ≤ E1 := esymm_nonneg xs hxs' 1
      have hE2 : (0 : ℝ) ≤ E2 := esymm_nonneg xs hxs' 2
      -- Inner inequality: E1² ≥ E2 (from IH or direct)
      have h_inner : E1 ^ 2 ≥ E2 := by
        rcases le_or_lt 2 xs.length with hm | hm
        · -- xs.length ≥ 2: apply IH at k=1
          have h := ih 1 le_rfl (by omega) hxs'
          simp only [show (1:ℕ) - 1 = 0 from rfl, show (1:ℕ) + 1 = 2 from rfl,
                     esymm_zero, one_mul] at h
          exact h
        · -- xs.length = 1: E2 = 0
          have : E2 = 0 := esymm_eq_zero_of_gt xs 2 (by omega)
          rw [this]; exact sq_nonneg _
      -- (E1 + x)² = E1² + 2x·E1 + x² ≥ E2 + x·E1 since E1² ≥ E2 and x·E1 + x² ≥ 0
      nlinarith [sq_nonneg x, mul_nonneg hx hE1, mul_nonneg hx hE1]
    · -- k ≥ 2 case
      -- Write k = p + 2 for p ≥ 0
      obtain ⟨p, rfl⟩ : ∃ p, k = p + 2 := ⟨k - 2, by omega⟩
      simp only [show p + 2 - 1 = p + 1 from by omega,
                 show p + 2 + 1 = p + 3 from by omega]
      -- Recurrences using esymm_cons_succ
      rw [show p + 2 = p + 1 + 1 from by omega, esymm_cons_succ]
      rw [show p + 1 = p + 0 + 1 from by omega, esymm_cons_succ]
      rw [show p + 3 = p + 2 + 1 from by omega, esymm_cons_succ]
      -- Set abbreviations for inner esymm values
      set ek   := esymm xs (p + 2)
      set ekm1 := esymm xs (p + 1)
      set ekp1 := esymm xs (p + 3)
      set ekm2 := esymm xs (p + 0)
      have hek   : (0 : ℝ) ≤ ek   := esymm_nonneg xs hxs' (p + 2)
      have hekm1 : (0 : ℝ) ≤ ekm1 := esymm_nonneg xs hxs' (p + 1)
      have hekp1 : (0 : ℝ) ≤ ekp1 := esymm_nonneg xs hxs' (p + 3)
      have hekm2 : (0 : ℝ) ≤ ekm2 := esymm_nonneg xs hxs' (p + 0)
      -- IH at k = p+2 for xs (Newton at k)
      have h_delta_k : ek ^ 2 ≥ ekm1 * ekp1 := by
        rcases le_or_lt (p + 3) xs.length with hkm | hkm
        · have h := ih (p + 2) (by omega) (by omega) hxs'
          simp only [show p + 2 - 1 = p + 1 from by omega,
                     show p + 2 + 1 = p + 3 from by omega] at h
          exact h
        · have : ekp1 = 0 := esymm_eq_zero_of_gt xs (p + 3) (by omega)
          rw [this, mul_zero]; exact sq_nonneg _
      -- IH at k = p+1 for xs (Newton at k-1)
      have h_delta_km1 : ekm1 ^ 2 ≥ ekm2 * ek := by
        rcases le_or_lt (p + 2) xs.length with hkm | hkm
        · have h := ih (p + 1) (by omega) (by omega) hxs'
          simp only [show p + 1 - 1 = p from by omega,
                     show p + 1 + 1 = p + 2 from by omega] at h
          exact h
        · have : ek = 0 := esymm_eq_zero_of_gt xs (p + 2) (by omega)
          rw [this, mul_zero]; exact sq_nonneg _
      -- Cross condition: ek * ekm1 ≥ ekm2 * ekp1
      -- Derived from h_delta_k and h_delta_km1 via cross_product_of_log_concave
      have h_cross : ek * ekm1 ≥ ekm2 * ekp1 := by
        apply NewtonLogConcavity.cross_product_of_log_concave hekm2 hekm1 hek hekp1
            h_delta_km1 h_delta_k
        -- h3: ekm1 = 0 → ek = 0 → ekm2 * ekp1 = 0
        intro hb0 hc0
        -- From hb0 (ekm1 = 0): esymm xs (p+2) = ek = 0 by zero_tail
        have hek_zero : ek = 0 :=
          esymm_zero_tail xs hxs' (by omega : 1 ≤ p + 1) hb0
        -- From ekm1 = 0 and j = p+1 ≥ 1: esymm xs (p+2) = 0 by zero_tail
        -- Then ekp1 = esymm xs (p+3) = 0 by zero_tail applied again
        have hekp1_zero : ekp1 = 0 :=
          esymm_zero_tail xs hxs' (by omega : 1 ≤ p + 2)
            (esymm_zero_tail xs hxs' (by omega : 1 ≤ p + 1) hb0)
        rw [hekp1_zero, mul_zero]
      -- Goal: (ek + x*ekm1)² ≥ (ekm1 + x*ekm2) * (ekp1 + x*ek)
      -- Expand: ek² + 2x·ek·ekm1 + x²·ekm1²
      --       ≥ ekm1·ekp1 + x·(ekm2·ekp1 + ekm1·ek) + x²·ekm2·ek
      -- LHS - RHS = (ek² - ekm1·ekp1) + x·(ek·ekm1 - ekm2·ekp1) + x²·(ekm1² - ekm2·ek) ≥ 0
      nlinarith [h_delta_k, h_delta_km1, h_cross,
                 mul_nonneg hx (mul_nonneg hek hekm1),
                 mul_nonneg (mul_nonneg hx hx) (mul_nonneg hekm1 hekm1),
                 sq_nonneg x, sq_nonneg ek, sq_nonneg ekm1,
                 mul_nonneg hekm2 hekp1]

/-! ## Part III: Normalized Newton Inequality (Cleared-Denominator Form)

Using the unnormalized Newton + cross condition + the inductive step from
AmgmInequalityOQ02OQ02, we prove the full normalized form. -/

/-- Helper: the cross condition for esymm from the unnormalized Newton inequality. -/
private theorem esymm_cross_condition (xs : List ℝ) (hxs : ∀ x ∈ xs, (0 : ℝ) ≤ x)
    (k : ℕ) (hk : 2 ≤ k) :
    esymm xs k * esymm xs (k - 1) ≥ esymm xs (k - 2) * esymm xs (k + 1) := by
  -- From Newton at k: ek² ≥ ekm1*ekp1
  -- From Newton at k-1: ekm1² ≥ ekm2*ek
  -- Cross product of log-concave sequence
  obtain ⟨p, rfl⟩ : ∃ p, k = p + 2 := ⟨k - 2, by omega⟩
  simp only [show p + 2 - 1 = p + 1 from by omega,
             show p + 2 - 2 = p from by omega,
             show p + 2 + 1 = p + 3 from by omega]
  apply NewtonLogConcavity.cross_product_of_log_concave
      (esymm_nonneg xs hxs p) (esymm_nonneg xs hxs (p+1))
      (esymm_nonneg xs hxs (p+2)) (esymm_nonneg xs hxs (p+3))
  · -- h1: ekm1² ≥ ekm2 * ek
    rcases Nat.lt_or_ge xs.length (p + 2) with hlt | hge
    · have : esymm xs (p + 2) = 0 := esymm_eq_zero_of_gt xs (p + 2) hlt
      rw [this, mul_zero]; exact sq_nonneg _
    · have h := esymm_log_concave xs hxs (p + 1) (by omega) (by omega)
      simp only [show p + 1 - 1 = p from by omega, show p + 1 + 1 = p + 2 from by omega] at h
      exact h
  · -- h2: ek² ≥ ekm1 * ekp1
    rcases Nat.lt_or_ge xs.length (p + 3) with hlt | hge
    · have : esymm xs (p + 3) = 0 := esymm_eq_zero_of_gt xs (p + 3) hlt
      rw [this, mul_zero]; exact sq_nonneg _
    · have h := esymm_log_concave xs hxs (p + 2) (by omega) (by omega)
      simp only [show p + 2 - 1 = p + 1 from by omega, show p + 2 + 1 = p + 3 from by omega] at h
      exact h
  · -- h3: ekm1 = 0 → ek = 0 → ekm2 * ekp1 = 0
    intro hekm1_zero hek_zero
    have hekp1_zero : esymm xs (p + 3) = 0 :=
      esymm_zero_tail xs hxs (by omega)
        (esymm_zero_tail xs hxs (by omega) hekm1_zero)
    rw [hekp1_zero, mul_zero]

/-- **Newton's inequality** (cleared-denominator form) for lists with nonneg entries:
    C(n,k-1) · C(n,k+1) · e_k² ≥ C(n,k)² · e_{k-1} · e_{k+1}

    Proof by induction on xs.
    - k = 1 base: direct quadratic argument
    - k ≥ 2 inductive: apply `newton_cleared_denom_inductive_step` from
      AmgmInequalityOQ02OQ02.lean with the computed esymm values as inputs -/
theorem newton_inequality_binomial (xs : List ℝ) (hxs : ∀ x ∈ xs, (0 : ℝ) ≤ x)
    (k : ℕ) (hk : 1 ≤ k) (hkn : k + 1 ≤ xs.length) :
    (Nat.choose xs.length (k - 1) : ℝ) * (Nat.choose xs.length (k + 1) : ℝ) *
    esymm xs k ^ 2 ≥
    (Nat.choose xs.length k : ℝ) ^ 2 *
    (esymm xs (k - 1) * esymm xs (k + 1)) := by
  induction xs generalizing k with
  | nil => simp at hkn
  | cons x xs ih =>
    have hx : (0 : ℝ) ≤ x := hxs x (mem_cons_self x xs)
    have hxs' : ∀ y ∈ xs, (0 : ℝ) ≤ y := fun y hy => hxs y (mem_cons_of_mem x hy)
    simp only [length_cons] at hkn
    -- n = xs.length
    set n := xs.length with hn_def
    rcases Nat.eq_or_gt_of_le hk with rfl | hk2
    · -- k = 1 case
      simp only [show (1:ℕ) - 1 = 0 from rfl, show (1:ℕ) + 1 = 2 from rfl,
                 Nat.choose_zero_right, Nat.cast_one, one_mul, esymm_zero]
      -- esymm (x::xs) 1 = esymm xs 1 + x
      rw [show (1:ℕ) = 0 + 1 from rfl, esymm_cons_succ, esymm_zero, mul_one]
      -- esymm (x::xs) 2 = esymm xs 2 + x * esymm xs 1
      rw [show (2:ℕ) = 1 + 1 from rfl, esymm_cons_succ]
      -- Goal: C(n+1,2) * (E_1 + x)² ≥ (n+1)² * 1 * (E_2 + x*E_1)
      simp only [one_mul]
      set E1 := esymm xs 1
      set E2 := esymm xs 2
      have hE1 : (0 : ℝ) ≤ E1 := esymm_nonneg xs hxs' 1
      have hE2 : (0 : ℝ) ≤ E2 := esymm_nonneg xs hxs' 2
      -- C(n+1, 1) = n+1
      have hC1 : (Nat.choose (n + 1) 1 : ℝ) = n + 1 := by
        simp [Nat.choose_one_right]; push_cast; ring
      rw [hC1]
      -- Use quadratic_nonneg with inner IH
      -- Target: C(n+1,2) * (E_1 + x)² ≥ (n+1)² * (E_2 + x*E_1)
      -- This is a quadratic in x: C(n+1,2)*x² - (n+1)*E_1*x + [C(n+1,2)*E_1² - (n+1)²*E_2] ≥ 0
      -- α = C(n+1,2), β = -(n+1)*E_1, γ = C(n+1,2)*E_1² - (n+1)²*E_2
      -- IH at k=1 for xs (if n ≥ 2): C(n,2)*E_1² ≥ n²*E_2
      have h_IH_k1 : (Nat.choose n 2 : ℝ) * E1 ^ 2 ≥ (n : ℝ) ^ 2 * E2 := by
        rcases le_or_lt 2 n with hm | hm
        · -- IH for xs at k=1: C(n,0)*C(n,2)*E1^2 ≥ C(n,1)^2*(esymm xs 0)*E2
          have h := ih 1 le_rfl (by omega) hxs'
          simp only [show (1:ℕ) - 1 = 0 from rfl, show (1:ℕ) + 1 = 2 from rfl,
                     Nat.choose_zero_right, Nat.cast_one, one_mul,
                     esymm_zero, mul_one] at h
          -- h: C(n,2) * E1^2 ≥ C(n,1)^2 * E2; convert C(n,1) = n
          have hc1 : (Nat.choose n 1 : ℝ) = n := by exact_mod_cast Nat.choose_one_right n
          rw [hc1] at h; exact h
        · -- n ≤ 1: E2 = 0
          have : E2 = 0 := esymm_eq_zero_of_gt xs 2 (by omega)
          rw [this, mul_zero]; positivity
      -- Compute C(n+1,2) = C(n,2) + C(n,1) via Pascal
      have hPascal2 : (Nat.choose (n + 1) 2 : ℝ) =
          (Nat.choose n 2 : ℝ) + (Nat.choose n 1 : ℝ) := by
        have h := Nat.choose_succ_succ n 1
        simp only [Nat.choose_one_right] at h
        push_cast [h]; ring
      have hCn1 : (Nat.choose n 1 : ℝ) = (n : ℝ) := by
        simp [Nat.choose_one_right]; push_cast; ring
      rw [hPascal2, hCn1]
      -- Apply quadratic_nonneg
      -- α = C(n,2) + n, β = -(n+1)*E_1, γ = (C(n,2)+n)*E_1² - (n+1)²*E_2
      apply le_of_sub_nonneg
      ring_nf
      -- Goal after ring: C(n+1,2) * (E_1+x)² - (n+1)² * (E_2+x*E_1) ≥ 0
      -- Use quadratic_nonneg
      have h_α : (0 : ℝ) ≤ (Nat.choose n 2 : ℝ) + n := by positivity
      -- Key identity: 2 * C(n,2) = n * (n-1) as real numbers
      have h2C2 : 2 * (Nat.choose n 2 : ℝ) = (n : ℝ) * ((n : ℝ) - 1) := by
        induction n with
        | zero => simp
        | succ m ih =>
          have hpas : Nat.choose (m + 1) 2 = Nat.choose m 2 + m := by
            have := Nat.choose_succ_succ m 1
            simp [Nat.choose_one_right] at this
            omega
          push_cast [hpas]; linarith
      have h_γ : (0 : ℝ) ≤ ((Nat.choose n 2 : ℝ) + n) * E1 ^ 2 - (n + 1) ^ 2 * E2 := by
        -- Using h2C2: 2*(C₂+n) = n*(n-1)+2n = n*(n+1)
        -- Goal equivalent to: n*(n+1)*E1^2 ≥ 2*(n+1)^2*E2, i.e., n*E1^2 ≥ 2*(n+1)*E2
        -- From h_IH_k1 and h2C2: n*(n-1)*E1^2 ≥ 2*n^2*E2
        rcases le_or_lt 2 n with hn2 | hn2
        · have hn_cast : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn2
          -- n*(n-1)*E1^2 ≥ 2*n^2*E2 (from h_IH_k1 and h2C2)
          have hS : (n : ℝ) * ((n : ℝ) - 1) * E1 ^ 2 ≥ 2 * (n : ℝ) ^ 2 * E2 := by
            nlinarith [h_IH_k1, h2C2]
          -- E1^2 ≥ 2*E2: by contradiction from hS
          -- If E1^2 < 2*E2 then n*(n-1)*E1^2 < 2*n*(n-1)*E2 ≤ 2*n^2*E2 contradicts hS
          have hE1sq2 : E1 ^ 2 ≥ 2 * E2 := by
            by_contra hlt
            push_neg at hlt
            have hnn_pos : (0 : ℝ) < (n : ℝ) * ((n : ℝ) - 1) := by nlinarith
            nlinarith [hS, mul_pos (show (0:ℝ) < 2*E2 - E1^2 by linarith) hnn_pos, hE2]
          nlinarith [hS, hE1sq2, h2C2,
                     mul_nonneg (Nat.cast_nonneg n) (mul_nonneg hE1 hE1)]
        · -- n = 1 (n ≥ 1 from hkn, n < 2)
          have hn1 : n = 1 := by omega
          subst hn1
          have hE2z : E2 = 0 := esymm_eq_zero_of_gt xs 2 (by simp [hn_def]; omega)
          simp [hE2z]; positivity
      -- 4*(C₂+n)^2 = (n*(n+1))^2 (via h2C2: 2*C₂ = n*(n-1), so 2*(C₂+n) = n*(n+1))
      have h4C3 : 4 * ((Nat.choose n 2 : ℝ) + ↑n) ^ 2 = ((↑n : ℝ) * (↑n + 1)) ^ 2 := by
        linear_combination (2 * ((Nat.choose n 2 : ℝ) + ↑n) + ↑n * (↑n + 1)) * h2C2
      have h_disc : 4 * ((Nat.choose n 2 : ℝ) + n) *
          (((Nat.choose n 2 : ℝ) + n) * E1 ^ 2 - (n + 1) ^ 2 * E2) ≥
          ((n + 1) * E1) ^ 2 := by
        -- Ring identity: LHS - RHS = (n+1)^2*((n^2-1)*E1^2 - 2*n*(n+1)*E2) (using h4C3, h2C2)
        have hd_key : 4 * ((↑(Nat.choose n 2) + ↑n) * ((↑(Nat.choose n 2) + ↑n) * E1 ^ 2 -
            (↑n + 1) ^ 2 * E2)) - ((↑n + 1) * E1) ^ 2 =
            (↑n + 1) ^ 2 * ((↑n ^ 2 - 1) * E1 ^ 2 - 2 * ↑n * (↑n + 1) * E2) := by
          linear_combination (E1 ^ 2) * h4C3 +
                             (-2 * (↑n + 1) ^ 2 * E2) * h2C2
        -- (n^2-1)*E1^2 - 2*n*(n+1)*E2 = (n+1)*((n-1)*E1^2-2*n*E2) ≥ 0 from IH
        have hd_fact : (↑n ^ 2 - 1) * E1 ^ 2 - 2 * ↑n * (↑n + 1) * E2 ≥ 0 := by
          -- Step 1: n*(n-1)*E1^2 ≥ 2*n^2*E2 (multiply h_IH_k1 by 2 and use h2C2)
          have hSn : (↑n : ℝ) * ((↑n : ℝ) - 1) * E1 ^ 2 ≥ 2 * (↑n : ℝ) ^ 2 * E2 := by
            nlinarith [h_IH_k1, h2C2]
          -- Step 2: (n-1)*E1^2 ≥ 2*n*E2 by contradiction (if not, multiply by n > 0)
          have hn_pos : (0 : ℝ) < ↑n := Nat.cast_pos.mpr (by omega)
          have hSbase : (↑n - 1 : ℝ) * E1 ^ 2 ≥ 2 * ↑n * E2 := by
            by_contra hlt; push_neg at hlt
            linarith [mul_pos hn_pos (show (0:ℝ) < 2*↑n*E2-(↑n-1)*E1^2 from by linarith), hSn]
          -- Step 3: (n^2-1)*E1^2 - 2*n*(n+1)*E2 = (n+1)*((n-1)*E1^2-2*n*E2) ≥ 0
          nlinarith [hSbase,
                     mul_nonneg (by positivity : (0:ℝ) ≤ ↑n + 1)
                       (show (↑n - 1) * E1 ^ 2 - 2 * ↑n * E2 ≥ 0 from by linarith [hSbase])]
        linarith [hd_key, mul_nonneg (by positivity : (0:ℝ) ≤ (↑n+1)^2) hd_fact]
      -- Apply quadratic_nonneg
      have key := quadratic_nonneg ((Nat.choose n 2 : ℝ) + ↑n) (-(↑n + 1) * E1)
          (((Nat.choose n 2 : ℝ) + ↑n) * E1 ^ 2 - (↑n + 1) ^ 2 * E2) x hx h_α h_γ
          (by nlinarith [h_disc])
      nlinarith [key]
    · -- k ≥ 2 case: use newton_cleared_denom_inductive_step
      obtain ⟨p, rfl⟩ : ∃ p, k = p + 2 := ⟨k - 2, by omega⟩
      simp only [show p + 2 - 1 = p + 1 from by omega,
                 show p + 2 + 1 = p + 3 from by omega]
      -- Recurrences
      have rec_k   : esymm (x :: xs) (p + 2) = esymm xs (p + 2) + x * esymm xs (p + 1) := by
        rw [show p + 2 = p + 1 + 1 from by omega]; exact esymm_cons_succ x xs (p + 1)
      have rec_km1 : esymm (x :: xs) (p + 1) = esymm xs (p + 1) + x * esymm xs p := by
        rw [show p + 1 = p + 0 + 1 from by omega]; exact esymm_cons_succ x xs p
      have rec_kp1 : esymm (x :: xs) (p + 3) = esymm xs (p + 3) + x * esymm xs (p + 2) := by
        rw [show p + 3 = p + 2 + 1 from by omega]; exact esymm_cons_succ x xs (p + 2)
      -- Abbreviations
      set ek   := esymm xs (p + 2)
      set ekm1 := esymm xs (p + 1)
      set ekp1 := esymm xs (p + 3)
      set ekm2 := esymm xs p
      have hek   : (0 : ℝ) ≤ ek   := esymm_nonneg xs hxs' (p + 2)
      have hekm1 : (0 : ℝ) ≤ ekm1 := esymm_nonneg xs hxs' (p + 1)
      have hekp1 : (0 : ℝ) ≤ ekp1 := esymm_nonneg xs hxs' (p + 3)
      have hekm2 : (0 : ℝ) ≤ ekm2 := esymm_nonneg xs hxs' p
      -- Unnormalized Newton for xs
      have h_unn_k : ek ^ 2 ≥ ekm1 * ekp1 := by
        rcases le_or_lt (p + 3) n with hkm | hkm
        · have h := esymm_log_concave xs hxs' (p + 2) (by omega) (by omega)
          simp only [show p + 2 - 1 = p + 1 from by omega,
                     show p + 2 + 1 = p + 3 from by omega] at h
          exact h
        · have : ekp1 = 0 := esymm_eq_zero_of_gt xs (p + 3) hkm
          rw [this, mul_zero]; exact sq_nonneg _
      have h_unn_km1 : ekm1 ^ 2 ≥ ekm2 * ek := by
        rcases le_or_lt (p + 2) n with hkm | hkm
        · have h := esymm_log_concave xs hxs' (p + 1) (by omega) (by omega)
          simp only [show p + 1 - 1 = p from by omega,
                     show p + 1 + 1 = p + 2 from by omega] at h
          exact h
        · have : ek = 0 := esymm_eq_zero_of_gt xs (p + 2) hkm
          rw [this, mul_zero]; exact sq_nonneg _
      -- Cross condition
      have h_cross : ek * ekm1 ≥ ekm2 * ekp1 := by
        apply NewtonLogConcavity.cross_product_of_log_concave
            hekm2 hekm1 hek hekp1 h_unn_km1 h_unn_k
        intro hb0 hc0
        -- hb0 : ekm1 = 0, hc0 : ek = 0 (unused)
        have hekp1_zero : ekp1 = 0 :=
          esymm_zero_tail xs hxs' (by omega)
            (esymm_zero_tail xs hxs' (by omega) hb0)
        rw [hekp1_zero, mul_zero]
      -- IH at k = p+2 for xs (normalized Newton, if p+3 ≤ n)
      have h_ih_k : ek ^ 2 * ((Nat.choose n (p + 1) : ℝ) * (Nat.choose n (p + 3) : ℝ)) ≥
          ekm1 * ekp1 * (Nat.choose n (p + 2) : ℝ) ^ 2 := by
        rcases le_or_lt (p + 3) n with hkm | hkm
        · have h := ih (p + 2) (by omega) (by omega) hxs'
          simp only [show p + 2 - 1 = p + 1 from by omega,
                     show p + 2 + 1 = p + 3 from by omega] at h
          nlinarith [h]
        · -- p+3 > n: C(n,p+3) = 0
          have hCzero : (Nat.choose n (p + 3) : ℝ) = 0 := by
            simp [Nat.choose_eq_zero_of_lt (by omega : n < p + 3)]
          rw [hCzero, mul_zero, mul_zero]; positivity
      -- IH at k = p+1 for xs (normalized Newton, if p+2 ≤ n)
      have h_ih_km1 : ekm1 ^ 2 * ((Nat.choose n p : ℝ) * (Nat.choose n (p + 2) : ℝ)) ≥
          ekm2 * ek * (Nat.choose n (p + 1) : ℝ) ^ 2 := by
        rcases le_or_lt (p + 2) n with hkm | hkm
        · have h := ih (p + 1) (by omega) (by omega) hxs'
          simp only [show p + 1 - 1 = p from by omega,
                     show p + 1 + 1 = p + 2 from by omega] at h
          nlinarith [h]
        · -- p+2 > n: C(n,p+2) = 0
          have hCzero : (Nat.choose n (p + 2) : ℝ) = 0 := by
            simp [Nat.choose_eq_zero_of_lt (by omega : n < p + 2)]
          rw [hCzero, mul_zero, mul_zero]; positivity
      -- Rewrite goal using recurrences
      rw [rec_k, rec_km1, rec_kp1]
      -- Goal: (C(n+1,p+1)*C(n+1,p+3))*(ek+x*ekm1)² ≥ C(n+1,p+2)²*(ekm1+x*ekm2)*(ekp1+x*ek)
      -- Apply newton_cleared_denom_inductive_step
      -- But first, check if p+3 ≤ n (inductive step) or p+3 > n (boundary case)
      rcases le_or_lt (p + 3) n with hbound | hbound
      · -- Inductive step: p+3 ≤ n, so p+2+1 ≤ n (i.e., k+1 ≤ n)
        have h_key := NewtonLogConcavity.newton_cleared_denom_inductive_step
          n (p + 2) (by omega) (by omega)  -- m = n, k = p+2, hk: 2 ≤ p+2, hm: p+3 ≤ n
          ek ekm1 ekp1 ekm2 x hx hek hekm1 hekp1 hekm2
          h_unn_k h_unn_km1 h_cross
          h_ih_k h_ih_km1
        -- h_key: (ek+x*ekm1)^2 * (C(n+1,p+1)*C(n+1,p+3)) ≥ (ekm1+x*ekm2)*(ekp1+x*ek)*C(n+1,p+2)^2
        -- Rewrite to match our goal form
        simp only [show p + 2 - 1 = p + 1 from by omega,
                   show p + 2 + 1 = p + 3 from by omega] at h_key
        nlinarith [h_key]
      · -- Boundary case: p+3 > n, so n = p+2 (since hkn: p+3 ≤ n+1)
        have hn_eq : n = p + 2 := by omega
        -- In this case, C(n, p+3) = 0 and ekp1 = esymm xs (p+3) = 0
        have hCkp1 : (Nat.choose n (p + 3) : ℝ) = 0 := by
          simp [Nat.choose_eq_zero_of_lt (by omega : n < p + 3)]
        have hekp1_zero : ekp1 = 0 := esymm_eq_zero_of_gt xs (p + 3) (by omega)
        -- C(n+1, p+3) = C(n+1, n+1) = 1
        have hCkp1_succ : (Nat.choose (n + 1) (p + 3) : ℝ) = 1 := by
          rw [hn_eq]; simp [Nat.choose_self]
        -- Goal simplifies significantly since ekp1 = 0
        rw [hekp1_zero]
        simp only [zero_add, mul_one]
        -- C(n+1, p+2) = C(n+1, n) = n+1
        have hCk_succ : (Nat.choose (n + 1) (p + 2) : ℝ) = (n : ℝ) + 1 := by
          rw [hn_eq]; simp
        rw [hCkp1_succ, mul_one, hCk_succ]
        -- Goal: C(n+1,p+1) * (ek+x*ekm1)^2 ≥ (n+1)^2 * (ekm1+x*ekm2) * (x*ek)
        -- Need IH at k-1 for xs (boundary case)
        -- Use a direct inequality: this is the dual of k=1 boundary
        -- From h_ih_km1 (with n = p+2, C(n,p+2) = C(p+2,p+2) = 1):
        have hCmk : (Nat.choose n (p + 2) : ℝ) = 1 := by
          rw [hn_eq]; simp [Nat.choose_self]
        -- C(n, p+1) = C(p+2, p+1) = C(p+2, 1) = p+2 = n (by symmetry C(n,k)=C(n,n-k))
        have hCmkm1 : (Nat.choose n (p + 1) : ℝ) = (n : ℝ) := by
          rw [hn_eq, Nat.choose_symm (by omega : p + 1 ≤ p + 2),
              show p + 2 - (p + 1) = 1 from by omega, Nat.choose_one_right]
        -- From h_ih_km1: ekm1^2 * (C(n,p)*C(n,p+2)) ≥ ekm2*ek*C(n,p+1)^2
        -- With hCmk: ekm1^2 * (C(n,p)*1) ≥ ekm2*ek*n^2
        -- i.e., ekm1^2 * C(n,p) ≥ ekm2*ek*n^2
        rw [hCmk, mul_one, hCmkm1] at h_ih_km1
        -- h_ih_km1: ekm1^2 * C(n,p) ≥ ekm2*ek*n^2
        -- Establish 2*C(n+1,p+1) = n*(n+1) via C(n+1,p+1)*(n-p) = C(n+1,p+2)*(p+2)
        -- i.e., C(n+1,p+1)*2 = (n+1)*n (since n-p=2, p+2=n, C(n+1,p+2)=n+1)
        have h2Ckm1 : 2 * (Nat.choose (n + 1) (p + 1) : ℝ) = (n : ℝ) * ((n : ℝ) + 1) := by
          have hmul := Nat.choose_succ_right_eq (n + 1) (p + 1)
          -- hmul: C(n+1,p+1) * ((n+1)-(p+1)) = C(n+1,p+2) * (p+2)
          have := congr_arg (Nat.cast : ℕ → ℝ) hmul
          rw [Nat.cast_mul, Nat.cast_mul, Nat.cast_sub (by omega)] at this
          rw [hCk_succ] at this
          push_cast at this ⊢
          rw [hn_eq] at this ⊢
          linarith
        -- Also: 2*C(n,p) = n*(n-1) since C(n,p) = C(n,2) and 2*C(m,2) = m*(m-1)
        have h2Cp : 2 * (Nat.choose n p : ℝ) = (n : ℝ) * ((n : ℝ) - 1) := by
          have hCnp : Nat.choose n p = Nat.choose n 2 := by
            conv_lhs => rw [hn_eq]
            exact Nat.choose_symm (by omega)
          rw [hCnp, hn_eq]
          -- 2*C(p+2,2) = (p+2)*(p+1) = n*(n-1)
          induction p with
          | zero => norm_num [Nat.choose]
          | succ q ih =>
            have hpas : Nat.choose (q + 3) 2 = Nat.choose (q + 2) 2 + (q + 2) := by
              have := Nat.choose_succ_succ (q + 2) 1
              simp [Nat.choose_one_right] at this; omega
            push_cast [hpas]; linarith
        -- Goal: C(n+1,p+1) * (ek+x*ekm1)^2 ≥ (n+1)^2 * (ekm1+x*ekm2) * (x*ek)
        -- This is a quadratic in x with:
        --   γ = C(n+1,p+1)*ek^2 ≥ 0
        --   α = C(n+1,p+1)*ekm1^2 - (n+1)^2*ekm2*ek ≥ 0 (from h_ih_km1, h2Cp, h2Ckm1)
        --   β = -(n+1)*ek*ekm1 (the cross term)
        --   disc: β^2 ≤ 4*α*γ follows from α,γ ≥ 0 and IH
        -- Establish γ ≥ 0
        set Ckm1 := (Nat.choose (n+1) (p+1) : ℝ) with hCkm1_def
        have hCkm1_nn : (0 : ℝ) ≤ Ckm1 := Nat.cast_nonneg _
        -- Key bounds from h_ih_km1 and h2Cp:
        -- n*(n-1)*ekm1^2/2 ≥ n^2*ekm2*ek ⟹ (n-1)*ekm1^2 ≥ 2*n*ekm2*ek
        have hS_bound : (n : ℝ) * ((n : ℝ) - 1) * ekm1 ^ 2 ≥ 2 * (n : ℝ) ^ 2 * (ekm2 * ek) := by
          nlinarith [h_ih_km1, h2Cp]
        -- n*(n+1)*ekm1^2 ≥ 2*(n+1)^2*ekm2*ek iff n*ekm1^2 ≥ 2*(n+1)*ekm2*ek
        have hα_bound : (n : ℝ) * ((n : ℝ) + 1) * ekm1 ^ 2 ≥ 2 * ((n : ℝ) + 1) ^ 2 * (ekm2 * ek) := by
          rcases le_or_lt 2 n with hn2 | hn2
          · have hn_cast : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn2
            have hekm1sq : ekm1 ^ 2 ≥ 2 * (ekm2 * ek) := by
              -- by contradiction: if ekm1^2 < 2*ekm2*ek then n*(n-1)*ekm1^2 < 2*n^2*ekm2*ek
              by_contra hlt
              push_neg at hlt
              have hnn2 : (0 : ℝ) < (n : ℝ) * ((n : ℝ) - 1) := by nlinarith
              nlinarith [hS_bound, mul_pos (show (0:ℝ) < 2*(ekm2*ek)-ekm1^2 by linarith) hnn2,
                         mul_nonneg hekm2 hek]
            nlinarith [hS_bound, hekm1sq]
          · -- n = 1 (since n = p+2 ≥ 2, contradiction unless p=0, n=2... check)
            -- Actually n = p+2 ≥ 2 since p ≥ 0, so n ≥ 2; but we said n < 2 here
            -- This branch is unreachable since n = p+2 ≥ 2
            omega
        -- Rewrite goal using h2Ckm1
        rw [show (Nat.choose (n+1) (p+1) : ℝ) = Ckm1 from rfl]
        -- Apply quadratic_nonneg
        -- P(x) = Ckm1*(ek+x*ekm1)^2 - (n+1)^2*(ekm1+x*ekm2)*(x*ek)
        -- = Ckm1*ekm1^2*x^2 - (n+1)*ek*ekm1*x + Ckm1*ek^2 - [(n+1)^2*ekm2*ek*x^2 + (n+1)^2*ekm1*ek*x]
        -- Wait, RHS = (n+1)^2*x*(ekm1+x*ekm2)*ek = (n+1)^2*ekm1*ek*x + (n+1)^2*ekm2*ek*x^2
        -- P(x) = (Ckm1*ekm1^2 - (n+1)^2*ekm2*ek)*x^2 + (Ckm1*ek - (n+1)^2*ekm1*ek)*2*x/2 ...
        -- Hmm, let me use quadratic_nonneg on the equivalent form
        -- Rearranged: (Ckm1*ekm1^2 - (n+1)^2*ekm2*ek)*x^2 - (n+1)*ek*ekm1*x + Ckm1*ek^2 ≥ 0
        have h_α2 : (0 : ℝ) ≤ Ckm1 * ekm1 ^ 2 - (↑n + 1) ^ 2 * (ekm2 * ek) := by
          nlinarith [h2Ckm1, hα_bound]
        have h_γ2 : (0 : ℝ) ≤ Ckm1 * ek ^ 2 := mul_nonneg hCkm1_nn (sq_nonneg _)
        -- Ring identity: LHS - RHS = α*x^2 + β*x + γ (using 2*Ckm1 = n*(n+1))
        -- Middle coeff: 2*Ckm1*ek*ekm1 - (n+1)^2*ekm1*ek = (2*Ckm1-n*(n+1))*ek*ekm1 = 0
        have h_ring2 : Ckm1 * (ek + x * ekm1) ^ 2 - (↑n + 1) ^ 2 * (ekm1 + x * ekm2) * (x * ek) =
            (Ckm1 * ekm1 ^ 2 - (↑n + 1) ^ 2 * (ekm2 * ek)) * x ^ 2 +
            (-(↑n + 1) * ek * ekm1) * x + Ckm1 * ek ^ 2 := by
          linear_combination (ek * ekm1 * x) * h2Ckm1
        -- Discriminant: 4*α*γ - β^2 = (n+1)^3*ek^2*((n-1)*ekm1^2 - 2*n*ekm2*ek) ≥ 0
        have hSn : (↑n - 1 : ℝ) * ekm1 ^ 2 ≥ 2 * ↑n * (ekm2 * ek) := by
          nlinarith [hS_bound]
        have h4C2 : 4 * Ckm1 ^ 2 = ((↑n : ℝ) * (↑n + 1)) ^ 2 := by
          linear_combination (2 * Ckm1 + ↑n * (↑n + 1)) * h2Ckm1
        have h_disc2 : ((↑n + 1) * ek * ekm1) ^ 2 ≤
            4 * (Ckm1 * ekm1 ^ 2 - (↑n + 1) ^ 2 * (ekm2 * ek)) * (Ckm1 * ek ^ 2) := by
          -- Ring identity: RHS - LHS = (n+1)^2*ek^2*((n^2-1)*ekm1^2 - 2*n*(n+1)*ekm2*ek)
          -- Using 4*Ckm1^2=(n*(n+1))^2 and 2*Ckm1=n*(n+1)
          have hkey : 4 * (Ckm1 * ekm1 ^ 2 - (↑n + 1) ^ 2 * (ekm2 * ek)) * (Ckm1 * ek ^ 2) -
              ((↑n + 1) * ek * ekm1) ^ 2 =
              (↑n + 1) ^ 2 * ek ^ 2 *
                ((↑n ^ 2 - 1) * ekm1 ^ 2 - 2 * ↑n * (↑n + 1) * (ekm2 * ek)) := by
            linear_combination (ekm1 ^ 2 * ek ^ 2) * h4C2 +
                               (-2 * (↑n + 1) ^ 2 * ekm2 * ek ^ 3) * h2Ckm1
          -- (n^2-1)*ekm1^2 - 2*n*(n+1)*ekm2*ek = (n+1)*((n-1)*ekm1^2 - 2*n*ekm2*ek) ≥ 0
          have hfact : (↑n ^ 2 - 1) * ekm1 ^ 2 - 2 * ↑n * (↑n + 1) * (ekm2 * ek) ≥ 0 := by
            nlinarith [hSn,
                       mul_nonneg (by positivity : (0:ℝ) ≤ ↑n + 1)
                         (show (↑n - 1) * ekm1 ^ 2 - 2 * ↑n * (ekm2 * ek) ≥ 0 from by linarith [hSn])]
          linarith [hkey, mul_nonneg (by positivity : (0:ℝ) ≤ (↑n+1)^2 * ek^2) hfact]
        have key2 := quadratic_nonneg
          (Ckm1 * ekm1 ^ 2 - (↑n + 1) ^ 2 * (ekm2 * ek))
          (-(↑n + 1) * ek * ekm1)
          (Ckm1 * ek ^ 2)
          x hx h_α2 h_γ2 (by nlinarith [h_disc2])
        linarith [key2, h_ring2]

end NewtonInductiveStepOQ02
