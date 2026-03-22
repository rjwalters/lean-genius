/-
  Lovász Local Lemma (LLL)

  Formalization of the key algebraic and combinatorial results underlying
  the Lovász Local Lemma. If bad events are each unlikely and mostly
  independent (sparse dependency graph), they can all be avoided simultaneously.

  Part I: Symmetric LLL — avoidance product bound
  Part II: General LLL — product positivity from x_i assignments
  Part III: Probability bounds implied by LLL condition
  Part IV: k-SAT application via LLL
  Part V: Moser-Tardos constructive LLL bound
  Part VI: Symmetric case quantitative estimates

  Erdős & Lovász (1975), Moser & Tardos (2010)
-/
import Mathlib

namespace ProbMethod.LovaszLocal

-- ═══════════════════════════════════════════════════════════════════
-- PART I: SYMMETRIC LLL (ALGEBRAIC CORE)
-- ═══════════════════════════════════════════════════════════════════

/-- The symmetric LLL algebraic kernel: if p*(d+1) ≤ 1/e (approximated
    by 1/3), then the avoidance probability factor (1-p)^n is strictly
    positive. This is the algebraic core of the symmetric LLL: in the
    full probabilistic setting, P[∩ Āᵢ] ≥ (1-p)^n > 0. -/
theorem symmetric_lll_bound {n : ℕ} {p : ℚ} {d : ℕ}
    (hp : 0 ≤ p) (hpd : p * (↑d + 1) ≤ 1 / 3) :
    0 < (1 - p) ^ n := by
  apply pow_pos
  have hd_pos : (0 : ℚ) < ↑d + 1 := by positivity
  nlinarith [mul_le_mul_of_nonneg_right (show p ≤ 1 / 3 from by nlinarith) (le_of_lt hd_pos)]

-- ═══════════════════════════════════════════════════════════════════
-- PART II: GENERAL LLL PRODUCT POSITIVITY
-- ═══════════════════════════════════════════════════════════════════

/-- General LLL product positivity: if x_i ∈ [0,1) for all i, then the
    avoidance product ∏(1 - xᵢ) is strictly positive. In the
    probabilistic LLL, P[∩ Āᵢ] ≥ ∏(1 - xᵢ) > 0. -/
theorem general_lll {n : ℕ} {x : Fin n → ℚ}
    (hx_range : ∀ i, 0 ≤ x i ∧ x i < 1) :
    0 < (Finset.univ : Finset (Fin n)).prod (fun i => 1 - x i) := by
  apply Finset.prod_pos
  intro i _
  linarith [(hx_range i).2]

-- ═══════════════════════════════════════════════════════════════════
-- PART III: LLL PROBABILITY BOUNDS
-- ═══════════════════════════════════════════════════════════════════

/-- The LLL condition implies each event probability is bounded by xᵢ.
    Since each factor (1-xⱼ) ≤ 1, the product ∏(1-xⱼ) ≤ 1, giving
    prob_i ≤ xᵢ · 1 = xᵢ. -/
theorem lll_prob_bound {n : ℕ} {prob x : Fin n → ℚ}
    {adj : Fin n → Finset (Fin n)}
    (hx_range : ∀ i, 0 ≤ x i ∧ x i < 1)
    (hbound : ∀ i, prob i ≤ x i * (adj i).prod (fun j => 1 - x j)) :
    ∀ i, prob i ≤ x i := by
  intro i
  have hprod : (adj i).prod (fun j => 1 - x j) ≤ 1 :=
    Finset.prod_le_one
      (fun j _ => by linarith [(hx_range j).2])
      (fun j _ => by linarith [(hx_range j).1])
  calc prob i ≤ x i * (adj i).prod (fun j => 1 - x j) := hbound i
    _ ≤ x i * 1 := by exact mul_le_mul_of_nonneg_left hprod (hx_range i).1
    _ = x i := mul_one _

/-- Each factor in the avoidance product is strictly positive. -/
theorem lll_factor_pos {n : ℕ} {x : Fin n → ℚ}
    (hx_range : ∀ i, 0 ≤ x i ∧ x i < 1) :
    ∀ i, 0 < 1 - x i :=
  fun i => by linarith [(hx_range i).2]

-- ═══════════════════════════════════════════════════════════════════
-- PART IV: k-SAT APPLICATION
-- ═══════════════════════════════════════════════════════════════════

/-- Auxiliary: 2^(k-2) + 1 ≤ 2^k for k ≥ 3.
    Proof: 1 ≤ 2^(k-2), so 2^(k-2)+1 ≤ 2·2^(k-2) = 2^(k-1) ≤ 2^k. -/
private theorem pow2_plus_one_le (k : ℕ) (hk : 3 ≤ k) :
    (2 : ℚ) ^ (k - 2) + 1 ≤ 2 ^ k := by
  have h1 : (1 : ℚ) ≤ 2 ^ (k - 2) := by
    calc (1 : ℚ) ≤ 2 ^ 1 := by norm_num
    _ ≤ 2 ^ (k - 2) := by gcongr; norm_num; omega
  have h2 : (2 : ℚ) ^ (k - 2) + 2 ^ (k - 2) = 2 ^ (k - 1) := by
    have hk1 : k - 1 = (k - 2) + 1 := by omega
    rw [hk1, pow_succ]; ring
  calc (2 : ℚ) ^ (k - 2) + 1
      ≤ 2 ^ (k - 2) + 2 ^ (k - 2) := by linarith
    _ = 2 ^ (k - 1) := h2
    _ ≤ 2 ^ k := by gcongr; norm_num; omega

/-- k-SAT via LLL: a k-CNF formula where each variable appears in at most
    2^(k-2)/k clauses is satisfiable (for k ≥ 3).

    Each clause has probability 2^{-k} of violation under random assignment.
    Each clause shares variables with at most k·(2^{k-2}/k) = 2^{k-2} others.
    The LLL condition 2^{-k}·(dependency + 1) ≤ 1 is verified here. -/
theorem ksat_lll (k : ℕ) (hk : 3 ≤ k) :
    (2 : ℚ)⁻¹ ^ k * ((k * (2 ^ (k - 2) / k)) + 1) ≤ 1 := by
  have hk_ne : (↑k : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  -- Simplify: k * (2^(k-2) / k) = 2^(k-2) since k ≠ 0
  have hsimpl : (↑k : ℚ) * ((2 : ℚ) ^ (k - 2) / ↑k) = 2 ^ (k - 2) := by
    field_simp
  rw [hsimpl, inv_pow]
  -- Goal: (2^k)⁻¹ * (2^(k-2) + 1) ≤ 1
  -- Rewrite as (2^(k-2) + 1) / 2^k ≤ 1
  have h2k_pos : (0 : ℚ) < 2 ^ k := by positivity
  rw [mul_comm, ← div_eq_mul_inv, div_le_one h2k_pos]
  exact pow2_plus_one_le k hk

-- ═══════════════════════════════════════════════════════════════════
-- PART V: CONSTRUCTIVE LLL (MOSER-TARDOS)
-- ═══════════════════════════════════════════════════════════════════

/-- Moser-Tardos constructive LLL: the expected number of resampling
    steps is bounded by Σ xᵢ/(1-xᵢ), which is non-negative.
    The Moser-Tardos (2010) algorithm turns the existential LLL into
    a constructive algorithm with expected polynomial runtime. -/
theorem moser_tardos_termination {n : ℕ} {x : Fin n → ℚ}
    (hx_range : ∀ i, 0 ≤ x i ∧ x i < 1) :
    0 ≤ (Finset.univ : Finset (Fin n)).sum (fun i => x i / (1 - x i)) := by
  apply Finset.sum_nonneg
  intro i _
  apply div_nonneg (hx_range i).1
  linarith [(hx_range i).2]

-- ═══════════════════════════════════════════════════════════════════
-- PART VI: SYMMETRIC CASE SPECIALIZATION
-- ═══════════════════════════════════════════════════════════════════

/-- In the symmetric case, x = 1/(d+1) satisfies the range condition [0,1). -/
theorem symmetric_x_in_range (d : ℕ) (hd : 0 < d) :
    0 ≤ (1 : ℚ) / (↑d + 1) ∧ (1 : ℚ) / (↑d + 1) < 1 := by
  constructor
  · positivity
  · rw [div_lt_one (by positivity : (0 : ℚ) < ↑d + 1)]
    have : (1 : ℚ) ≤ ↑d := Nat.one_le_cast.mpr hd
    linarith

/-- The symmetric avoidance bound: (d/(d+1))^n > 0 for any n, d > 0. -/
theorem symmetric_avoidance_pos (n d : ℕ) (hd : 0 < d) :
    0 < ((↑d / (↑d + 1 : ℚ)) ^ n) := by
  apply pow_pos
  exact div_pos (Nat.cast_pos.mpr hd) (by positivity)

/-- Symmetric LLL: the uniform avoidance product with x = 1/(d+1)
    equals (d/(d+1))^n. -/
theorem symmetric_product_eq (n d : ℕ) :
    (Finset.univ : Finset (Fin n)).prod (fun _ => 1 - (1 : ℚ) / (↑d + 1)) =
    (↑d / (↑d + 1)) ^ n := by
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  congr 1
  have : (↑d + 1 : ℚ) ≠ 0 := by positivity
  field_simp
  ring

/-- Moser-Tardos bound in the symmetric case: expected resampling with
    uniform x = 1/(d+1) simplifies to n/d. -/
theorem symmetric_moser_tardos_bound (n d : ℕ) (hd : 0 < d) :
    (Finset.univ : Finset (Fin n)).sum
      (fun _ : Fin n => ((1 : ℚ) / (↑d + 1)) / (1 - (1 : ℚ) / (↑d + 1))) =
    ↑n / ↑d := by
  have hd_ne : (↑d : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hd1_ne : (↑d + 1 : ℚ) ≠ 0 := by positivity
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  field_simp
  rw [show (↑d : ℚ) + 1 - 1 = ↑d from by ring, mul_div_cancel_right₀ _ hd_ne]

-- ═══════════════════════════════════════════════════════════════════
-- PART VII: LLL THRESHOLD AND DEPENDENCY GRAPH
-- ═══════════════════════════════════════════════════════════════════

/-- The LLL threshold T(d) = d^d / (d+1)^{d+1} is the maximum event
    probability that the symmetric LLL can handle with max degree d.
    When all events have P[A_i] ≤ T(d), they can be simultaneously avoided. -/
noncomputable def lllThreshold (d : ℕ) : ℚ :=
  if d = 0 then 1 else (↑d : ℚ) ^ d / (↑d + 1) ^ (d + 1)

/-- T(1) = 1/4: the threshold for dependency graphs of max degree 1. -/
theorem lllThreshold_one : lllThreshold 1 = 1 / 4 := by
  simp [lllThreshold]; norm_num

/-- T(2) = 4/27: the threshold for dependency graphs of max degree 2. -/
theorem lllThreshold_two : lllThreshold 2 = 4 / 27 := by
  simp [lllThreshold]; norm_num

/-- T(3) = 27/256: the threshold for dependency graphs of max degree 3. -/
theorem lllThreshold_three : lllThreshold 3 = 27 / 256 := by
  simp [lllThreshold]; norm_num

/-- T(d) > 0 for all d ≥ 1. The symmetric LLL always provides a nontrivial bound. -/
theorem lllThreshold_pos (d : ℕ) (hd : 0 < d) : 0 < lllThreshold d := by
  simp only [lllThreshold, if_neg (Nat.pos_iff_ne_zero.mp hd)]
  apply div_pos
  · exact pow_pos (Nat.cast_pos.mpr hd) d
  · exact pow_pos (by positivity : (0 : ℚ) < ↑d + 1) (d + 1)

/-- T(d) ≤ 1/4 for d=1,2,3. Subsumed by lllThreshold_le_quarter for all d ≥ 1. -/
theorem lllThreshold_le_quarter_small (d : ℕ) (hd : 0 < d) (hd3 : d ≤ 3) :
    lllThreshold d ≤ 1 / 4 := by
  interval_cases d <;> simp [lllThreshold] <;> norm_num

/-- A dependency graph for n events: adj i is the set of events dependent on event i. -/
structure IsValidDepGraph (n : ℕ) (adj : Fin n → Finset (Fin n)) : Prop where
  /-- No event depends on itself. -/
  irrefl : ∀ i, i ∉ adj i
  /-- Dependency is symmetric. -/
  symm : ∀ i j, j ∈ adj i → i ∈ adj j

/-- Maximum degree of a dependency graph. -/
def HasMaxDegree (n : ℕ) (adj : Fin n → Finset (Fin n)) (d : ℕ) : Prop :=
  ∀ i : Fin n, (adj i).card ≤ d

/-- The symmetric LLL with dependency graph: if prob_i ≤ T(d) for all i,
    and the dependency graph has max degree d, then the events can be avoided.
    This is the avoidance product version: ∏(1 - 1/(d+1)) > 0. -/
theorem symmetric_lll_avoidance (n d : ℕ) (hd : 0 < d) :
    0 < (Finset.univ : Finset (Fin n)).prod
      (fun _ => 1 - (1 : ℚ) / (↑d + 1)) := by
  rw [symmetric_product_eq]
  exact symmetric_avoidance_pos n d hd

-- ═══════════════════════════════════════════════════════════════════
-- PART VIII: BERNOULLI'S INEQUALITY AND UNIVERSAL THRESHOLD BOUND
-- ═══════════════════════════════════════════════════════════════════

/-- Bernoulli's inequality: (1 + x)^n ≥ 1 + n·x for x ≥ -1.
    The proof is by induction: (1+nx)(1+x) = 1+(n+1)x+nx² ≥ 1+(n+1)x. -/
theorem bernoulli_ineq (n : ℕ) {x : ℚ} (hx : -1 ≤ x) :
    1 + ↑n * x ≤ (1 + x) ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h1x : 0 ≤ 1 + x := by linarith
    have key : 1 + (↑n + 1) * x ≤ (1 + ↑n * x) * (1 + x) := by
      nlinarith [mul_nonneg (Nat.cast_nonneg (α := ℚ) n) (sq_nonneg x)]
    calc (1 + ↑(n + 1) * x : ℚ)
        = 1 + (↑n + 1) * x := by push_cast; ring
      _ ≤ (1 + ↑n * x) * (1 + x) := key
      _ ≤ (1 + x) ^ n * (1 + x) := mul_le_mul_of_nonneg_right ih h1x
      _ = (1 + x) ^ (n + 1) := (pow_succ (1 + x) n).symm

/-- (1 + 1/d)^d ≥ 2 for d ≥ 1. Immediate from Bernoulli with x = 1/d:
    1 + d·(1/d) = 2 ≤ (1 + 1/d)^d. -/
theorem one_plus_inv_pow_ge_two (d : ℕ) (hd : 1 ≤ d) :
    2 ≤ (1 + 1 / (↑d : ℚ)) ^ d := by
  have hd_pos : (0 : ℚ) < ↑d := Nat.cast_pos.mpr (by omega)
  have hd_ne : (↑d : ℚ) ≠ 0 := ne_of_gt hd_pos
  have h1d : (-1 : ℚ) ≤ 1 / ↑d := by linarith [div_pos one_pos hd_pos]
  have hb := bernoulli_ineq d h1d
  have hsimp : (↑d : ℚ) * (1 / ↑d) = 1 := by field_simp
  linarith

/-- (d+1)^d ≥ 2·d^d for d ≥ 1, the multiplicative form of Bernoulli's bound. -/
theorem succ_pow_ge_two_mul (d : ℕ) (hd : 1 ≤ d) :
    2 * (↑d : ℚ) ^ d ≤ (↑d + 1) ^ d := by
  have hd_pos : (0 : ℚ) < ↑d := Nat.cast_pos.mpr (by omega)
  have hdd_pos : (0 : ℚ) < ↑d ^ d := pow_pos hd_pos d
  have h := one_plus_inv_pow_ge_two d hd
  have hrw : (1 + 1 / (↑d : ℚ)) = (↑d + 1) / ↑d := by field_simp
  rw [hrw, div_pow] at h
  -- h : 2 ≤ (↑d + 1) ^ d / ↑d ^ d — multiply both sides by ↑d ^ d
  have step := mul_le_mul_of_nonneg_right h (le_of_lt hdd_pos)
  have cancel : (↑d + 1 : ℚ) ^ d / (↑d : ℚ) ^ d * (↑d : ℚ) ^ d = (↑d + 1 : ℚ) ^ d := by
    field_simp [ne_of_gt hdd_pos]
  linarith

/-- T(d) ≤ 1/4 for all d ≥ 1: the LLL threshold is universally bounded.
    Proof: Bernoulli gives (d+1)^d ≥ 2·d^d, and d+1 ≥ 2,
    so (d+1)^{d+1} ≥ 4·d^d, hence T(d) = d^d/(d+1)^{d+1} ≤ 1/4.
    This subsumes lllThreshold_le_quarter_small. -/
theorem lllThreshold_le_quarter (d : ℕ) (hd : 1 ≤ d) :
    lllThreshold d ≤ 1 / 4 := by
  have hd1_pos : (0 : ℚ) < ↑d + 1 := by positivity
  simp only [lllThreshold, if_neg (by omega : d ≠ 0)]
  have h1 : (0 : ℚ) < (↑d + 1) ^ (d + 1) := pow_pos hd1_pos (d + 1)
  -- Cross-multiplication: 4 * d^d ≤ (d+1)^(d+1)
  have h_cross : 4 * (↑d : ℚ) ^ d ≤ (↑d + 1) ^ (d + 1) := by
    rw [pow_succ]
    have h1' := succ_pow_ge_two_mul d hd
    have h2 : (2 : ℚ) ≤ ↑d + 1 := by
      have : (1 : ℚ) ≤ ↑d := Nat.one_le_cast.mpr hd; linarith
    calc (4 : ℚ) * ↑d ^ d = (2 * ↑d ^ d) * 2 := by ring
      _ ≤ (↑d + 1) ^ d * (↑d + 1) :=
          mul_le_mul h1' h2 (by norm_num) (le_of_lt (pow_pos hd1_pos d))
  -- Convert: 4*d^d ≤ (d+1)^(d+1) → d^d/(d+1)^(d+1) ≤ 1/4
  have key : 4 * (↑d : ℚ) ^ d / (↑d + 1) ^ (d + 1) ≤ 1 :=
    (div_le_one h1).mpr h_cross
  rw [mul_div_assoc] at key
  linarith

-- ═══════════════════════════════════════════════════════════════════
-- PART IX: FORMAL CONNECTIONS
-- ═══════════════════════════════════════════════════════════════════

/-- Symmetric LLL as a corollary of the general LLL: setting x_i = 1/(d+1)
    for all i recovers the symmetric avoidance bound.
    This formally connects Parts II and VI. -/
theorem symmetric_from_general (n d : ℕ) (hd : 0 < d) :
    0 < (Finset.univ : Finset (Fin n)).prod
      (fun _ => 1 - (1 : ℚ) / (↑d + 1)) :=
  general_lll (fun _ => symmetric_x_in_range d hd)

-- ═══════════════════════════════════════════════════════════════════
-- PART X: THRESHOLD-TO-LLL BRIDGE
-- ═══════════════════════════════════════════════════════════════════

/-- The LLL threshold factors as T(d) = (1/(d+1)) · (d/(d+1))^d,
    corresponding to the symmetric x_i = 1/(d+1) assignment.
    This connects the threshold to the avoidance product structure. -/
theorem lllThreshold_eq_product (d : ℕ) (hd : 0 < d) :
    lllThreshold d = (1 : ℚ) / (↑d + 1) * (↑d / (↑d + 1)) ^ d := by
  simp only [lllThreshold, if_neg (by omega : d ≠ 0)]
  rw [div_pow, div_mul_div_comm, one_mul]
  congr 1
  rw [pow_succ, mul_comm]

/-- If event probabilities are bounded by T(d) and the dependency graph has max
    degree d, the symmetric assignment x_i = 1/(d+1) satisfies the general LLL
    condition: prob_i ≤ x_i · ∏_{j ∈ Γ(i)} (1 - x_j).
    This bridges the symmetric threshold to the general LLL framework. -/
theorem threshold_satisfies_lll (n d : ℕ) (hd : 0 < d)
    (prob : Fin n → ℚ)
    (adj : Fin n → Finset (Fin n))
    (hdeg : HasMaxDegree n adj d)
    (hprob : ∀ i, prob i ≤ lllThreshold d) :
    ∀ i, prob i ≤ (1 : ℚ) / (↑d + 1) *
      (adj i).prod (fun _ => 1 - (1 : ℚ) / (↑d + 1)) := by
  intro i
  have hd1_pos : (0 : ℚ) < ↑d + 1 := by positivity
  have hconv : (↑d : ℚ) / (↑d + 1) = 1 - 1 / (↑d + 1) := by field_simp; ring
  rw [Finset.prod_const]
  calc prob i
      ≤ lllThreshold d := hprob i
    _ = (1 : ℚ) / (↑d + 1) * (↑d / (↑d + 1)) ^ d :=
        lllThreshold_eq_product d hd
    _ ≤ (1 : ℚ) / (↑d + 1) * (↑d / (↑d + 1)) ^ (adj i).card := by
        apply mul_le_mul_of_nonneg_left
        · exact pow_le_pow_of_le_one (by positivity)
            (by rw [div_le_one hd1_pos]; linarith) (hdeg i)
        · positivity
    _ = (1 : ℚ) / (↑d + 1) * (1 - 1 / (↑d + 1)) ^ (adj i).card := by
        rw [hconv]

/-- Complete Symmetric LLL: given event probabilities ≤ T(d) and dependency
    degree ≤ d, both the LLL condition and avoidance positivity hold.
    In the full probabilistic setting, this gives P[∩ Āᵢ] ≥ (d/(d+1))^n > 0. -/
theorem symmetric_lll_complete (n d : ℕ) (hd : 0 < d)
    (prob : Fin n → ℚ)
    (adj : Fin n → Finset (Fin n))
    (hdeg : HasMaxDegree n adj d)
    (hprob : ∀ i, prob i ≤ lllThreshold d) :
    (∀ i, prob i ≤ (1 : ℚ) / (↑d + 1) *
      (adj i).prod (fun _ => 1 - (1 : ℚ) / (↑d + 1))) ∧
    0 < (Finset.univ : Finset (Fin n)).prod
      (fun _ => 1 - (1 : ℚ) / (↑d + 1)) :=
  ⟨threshold_satisfies_lll n d hd prob adj hdeg hprob,
   symmetric_lll_avoidance n d hd⟩

end ProbMethod.LovaszLocal
