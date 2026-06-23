/-
Erdős Problem #1155 OQ-01-OQ-07: K_r-Removal Process Generalization

Generalization of the triangle removal process to K_r-removal:
Start with K_n, repeatedly select a random r-clique and remove all its edges,
until the graph is K_r-free. Let f_r(n) denote the remaining edges.

For r = 3 (triangles), this recovers the triangle removal process from
Erdos1155Problem.lean, where BFL (2015) showed f_3(n) = n^{3/2 + o(1)}.

The natural generalization conjectures:
  f_r(n) ≍ n^{2 - 2/(r+1)}

Key structural results proved here:
1. The K_r-removal process axiomatized for general r
2. Turán bound framework for K_r-free terminal graphs
3. Conjectured exponent 2-2/(r+1): computed for r=3,4,5, proved monotone
4. Generalized conjecture and BFL-type statements
5. Equivalence characterizations (both-bounds, ratio convergence)

Axioms: 3 (K_r-removal function, non-negativity, complete graph bound)
Sorries: 0
-/

import Proofs.Erdos1155Problem

open Filter SimpleGraph Finset

namespace Erdos1155OQ01OQ07

-- ============================================================================
-- § 1. K_r-Removal Process: Definitions
-- ============================================================================

/-- `kCliqueRemovalEdges r n` is the (expected) number of remaining edges after
running the K_r-removal process on K_n until no r-cliques remain.
This generalizes `triangleRemovalEdges` from r = 3.

The process:
1. Start with K_n (complete graph on n vertices)
2. Select a uniformly random r-clique
3. Delete all C(r,2) = r(r-1)/2 edges of this clique
4. Repeat until no r-clique remains
5. f_r(n) = expected number of remaining edges -/
axiom kCliqueRemovalEdges : ℕ → ℕ → ℝ

/-- The K_r-removal process leaves a non-negative number of edges. -/
axiom kCliqueRemovalEdges_nonneg (r n : ℕ) :
    0 ≤ kCliqueRemovalEdges r n

/-- The K_r-removal process on K_n starts with at most C(n,2) edges and
can only remove edges, so f_r(n) ≤ n(n-1)/2 ≤ n²/2. -/
axiom kCliqueRemovalEdges_le_complete (r n : ℕ) :
    kCliqueRemovalEdges r n ≤ (n : ℝ) ^ 2 / 2

-- ============================================================================
-- § 2. Turán Bound for K_r-Removal
-- ============================================================================

/-- The Turán density (1 - 1/(r-1)) for K_r-free graphs, for r ≥ 2.
For r = 3: 1/2 (Mantel). For r = 4: 2/3. -/
noncomputable def turanDensity (r : ℕ) : ℝ :=
  if r ≤ 1 then 1 else 1 - 1 / ((r : ℝ) - 1)

/-- The Turán density for r = 3 is 1/2 (Mantel's theorem). -/
theorem turanDensity_three : turanDensity 3 = 1 / 2 := by
  unfold turanDensity; simp; ring

/-- The Turán density for r = 4 is 2/3. -/
theorem turanDensity_four : turanDensity 4 = 2 / 3 := by
  unfold turanDensity; simp; ring

-- ============================================================================
-- § 3. Conjectured Exponent for General r
-- ============================================================================

/-- The conjectured exponent for the K_r-removal process.
For r ≥ 3, the expected behavior is f_r(n) ≍ n^{2 - 2/(r+1)}.

| r | exponent 2-2/(r+1) | decimal |
|---|-------------------|---------|
| 3 | 3/2               | 1.500   |
| 4 | 8/5               | 1.600   |
| 5 | 5/3               | 1.667   |
| 6 | 12/7              | 1.714   |
| → ∞ | → 2            | 2.000   | -/
noncomputable def kRemovalExponent (r : ℕ) : ℝ :=
  2 - 2 / ((r : ℝ) + 1)

/-- The exponent for r = 3 is 3/2, matching the triangle removal case. -/
theorem kRemovalExponent_three : kRemovalExponent 3 = 3 / 2 := by
  unfold kRemovalExponent; norm_num

/-- The exponent for r = 4 is 8/5. -/
theorem kRemovalExponent_four : kRemovalExponent 4 = 8 / 5 := by
  unfold kRemovalExponent; norm_num

/-- The exponent for r = 5 is 5/3. -/
theorem kRemovalExponent_five : kRemovalExponent 5 = 5 / 3 := by
  unfold kRemovalExponent; norm_num

/-- The exponent is strictly increasing in r (for r ≥ 1).
Proof: 2/(r₁+1) > 2/(r₂+1) when r₁ < r₂ (both positive denominators). -/
theorem kRemovalExponent_strictMono (r₁ r₂ : ℕ) (hr₁ : 1 ≤ r₁) (hr : r₁ < r₂) :
    kRemovalExponent r₁ < kRemovalExponent r₂ := by
  unfold kRemovalExponent
  -- Need: 2 - 2/(r₁+1) < 2 - 2/(r₂+1), i.e., 2/(r₂+1) < 2/(r₁+1)
  have h1 : (0 : ℝ) < (r₁ : ℝ) + 1 := by positivity
  have h2 : (0 : ℝ) < (r₂ : ℝ) + 1 := by positivity
  have h12 : (r₁ : ℝ) + 1 < (r₂ : ℝ) + 1 := by exact_mod_cast Nat.add_lt_add_right hr 1
  -- 2/(r₂+1) < 2/(r₁+1) since r₁+1 < r₂+1 and both positive
  have : 2 / ((r₂ : ℝ) + 1) < 2 / ((r₁ : ℝ) + 1) :=
    div_lt_div_of_pos_left (by norm_num : (0:ℝ) < 2) h1 h12
  linarith

/-- The exponent is bounded: 1 ≤ kRemovalExponent r < 2 for r ≥ 1.
The lower bound follows from r ≥ 1 ⟹ r+1 ≥ 2 ⟹ 2/(r+1) ≤ 1.
The upper bound follows from 2/(r+1) > 0. -/
theorem kRemovalExponent_bounds (r : ℕ) (hr : 1 ≤ r) :
    1 ≤ kRemovalExponent r ∧ kRemovalExponent r < 2 := by
  unfold kRemovalExponent
  have h : (0 : ℝ) < (r : ℝ) + 1 := by positivity
  constructor
  · -- 1 ≤ 2 - 2/(r+1) ⟺ 2/(r+1) ≤ 1 ⟺ 2 ≤ r+1
    have : 2 / ((r : ℝ) + 1) ≤ 1 := by
      rw [div_le_one h]
      exact_mod_cast (show 2 ≤ r + 1 from by omega)
    linarith
  · -- 2 - 2/(r+1) < 2 ⟺ 0 < 2/(r+1)
    have : 0 < 2 / ((r : ℝ) + 1) := by positivity
    linarith

/-- As r increases, the exponent gap 2 - α(r) = 2/(r+1) shrinks,
meaning the terminal graph retains more edges (closer to n² scaling).
This is expressed as: for any target gap δ > 0, eventually kRemovalExponent r > 2 - δ. -/
theorem kRemovalExponent_near_two (δ : ℝ) (hδ : 0 < δ) :
    ∃ N : ℕ, ∀ r : ℕ, N ≤ r → 2 - δ < kRemovalExponent r := by
  refine ⟨⌈2 / δ⌉₊, fun r hr => ?_⟩
  unfold kRemovalExponent
  have h_pos : (0 : ℝ) < (r : ℝ) + 1 := by positivity
  -- Need: 2 - δ < 2 - 2/(r+1), i.e., 2/(r+1) < δ
  suffices 2 / ((r : ℝ) + 1) < δ by linarith
  rw [div_lt_iff₀ h_pos]
  calc 2 ≤ δ * ⌈2 / δ⌉₊ := by
          rw [← div_le_iff₀ hδ]
          exact Nat.le_ceil (2 / δ)
    _ ≤ δ * ((r : ℝ) + 1) := by
          apply mul_le_mul_of_nonneg_left _ (le_of_lt hδ)
          exact_mod_cast (show ⌈2 / δ⌉₊ ≤ r + 1 from by omega)

-- ============================================================================
-- § 4. Generalized Conjecture
-- ============================================================================

/-- **Generalized Erdős Conjecture**: For r ≥ 3, the K_r-removal process satisfies
f_r(n) ≍ n^{2-2/(r+1)}, i.e., there exist constants 0 < c₁ ≤ c₂ such that
c₁ · n^α ≤ f_r(n) ≤ c₂ · n^α for all large n, where α = 2 - 2/(r+1). -/
def kRemoval_conjecture (r : ℕ) : Prop :=
  ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ c₁ ≤ c₂ ∧
    ∀ᶠ (n : ℕ) in atTop,
      c₁ * (n : ℝ) ^ kRemovalExponent r ≤ kCliqueRemovalEdges r n ∧
      kCliqueRemovalEdges r n ≤ c₂ * (n : ℝ) ^ kRemovalExponent r

/-- The generalized conjecture for r = 3 has exponent 3/2,
matching the original Erdős conjecture for triangle removal. -/
theorem kRemoval_conjecture_three_exponent :
    kRemovalExponent 3 = (3 : ℝ) / 2 :=
  kRemovalExponent_three

-- ============================================================================
-- § 5. Generalized BFL-type Bound
-- ============================================================================

/-- **Generalized BFL-type bound**: For r ≥ 3, f_r(n) = n^{α + o(1)} where
α = 2-2/(r+1). This means for every ε > 0, eventually n^{α-ε} ≤ f_r(n) ≤ n^{α+ε}.
For r = 3 with α = 3/2, this is exactly the BFL (2015) theorem. -/
def kRemoval_bfl_type (r : ℕ) : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∀ᶠ (n : ℕ) in atTop,
      (n : ℝ) ^ (kRemovalExponent r - ε) ≤ kCliqueRemovalEdges r n ∧
      kCliqueRemovalEdges r n ≤ (n : ℝ) ^ (kRemovalExponent r + ε)

/-- The conjecture implies the BFL-type bound.
Proof: for large n, the constants c₁, c₂ are absorbed into n^ε. -/
theorem kRemoval_conjecture_implies_bfl (r : ℕ) (hr : 1 ≤ r) :
    kRemoval_conjecture r → kRemoval_bfl_type r := by
  intro ⟨c₁, c₂, hc₁, hc₁c₂, hconj⟩ ε hε
  have hc₂_pos : 0 < c₂ := lt_of_lt_of_le hc₁ hc₁c₂
  have hge1 : ∀ᶠ (n : ℕ) in atTop, 1 ≤ n :=
    Filter.eventually_atTop.mpr ⟨1, fun n hn => hn⟩
  -- For large n: c₂ ≤ n^ε
  have hup_key : ∀ᶠ (n : ℕ) in atTop, c₂ ≤ (n : ℝ) ^ ε := by
    rw [Filter.eventually_atTop]
    refine ⟨⌈c₂ ^ (1/ε)⌉₊ + 1, fun n hn => ?_⟩
    have h1 : c₂ = (c₂ ^ (1/ε)) ^ ε := by
      rw [← Real.rpow_mul (le_of_lt hc₂_pos), one_div_mul_cancel (ne_of_gt hε),
          Real.rpow_one]
    rw [h1]
    exact Real.rpow_le_rpow (Real.rpow_nonneg (le_of_lt hc₂_pos) _)
      (le_trans (Nat.le_ceil _) (by exact_mod_cast (show ⌈c₂ ^ (1/ε)⌉₊ ≤ n by omega)))
      (le_of_lt hε)
  -- For large n: c₁⁻¹ ≤ n^ε
  have hc₁_inv_pos : 0 < c₁⁻¹ := inv_pos.mpr hc₁
  have hlo_key : ∀ᶠ (n : ℕ) in atTop, c₁⁻¹ ≤ (n : ℝ) ^ ε := by
    rw [Filter.eventually_atTop]
    refine ⟨⌈c₁⁻¹ ^ (1/ε)⌉₊ + 1, fun n hn => ?_⟩
    have h1 : c₁⁻¹ = (c₁⁻¹ ^ (1/ε)) ^ ε := by
      rw [← Real.rpow_mul (le_of_lt hc₁_inv_pos), one_div_mul_cancel (ne_of_gt hε),
          Real.rpow_one]
    rw [h1]
    exact Real.rpow_le_rpow (Real.rpow_nonneg (le_of_lt hc₁_inv_pos) _)
      (le_trans (Nat.le_ceil _) (by exact_mod_cast (show ⌈c₁⁻¹ ^ (1/ε)⌉₊ ≤ n by omega)))
      (le_of_lt hε)
  apply (((hconj.and hup_key).and hlo_key).and hge1).mono
  intro n ⟨⟨⟨⟨hlo, hup⟩, hcn⟩, hcln⟩, hn1⟩
  have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  let α := kRemovalExponent r
  constructor
  · -- Lower: n^{α-ε} ≤ f_r(n)
    calc (n : ℝ) ^ (α - ε)
        = (n : ℝ) ^ ((-ε) + α) := by congr 1; ring
      _ = (n : ℝ) ^ (-ε) * (n : ℝ) ^ α := Real.rpow_add hn_pos (-ε) α
      _ ≤ c₁ * (n : ℝ) ^ α := by
          apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (le_of_lt hn_pos) _)
          rw [Real.rpow_neg (le_of_lt hn_pos), ← one_div,
              div_le_iff₀ (Real.rpow_pos_of_pos hn_pos ε)]
          calc (1 : ℝ) = c₁ * c₁⁻¹ := (mul_inv_cancel₀ (ne_of_gt hc₁)).symm
            _ ≤ c₁ * (n : ℝ) ^ ε := mul_le_mul_of_nonneg_left hcln (le_of_lt hc₁)
      _ ≤ kCliqueRemovalEdges r n := hlo
  · -- Upper: f_r(n) ≤ n^{α+ε}
    calc kCliqueRemovalEdges r n
        ≤ c₂ * (n : ℝ) ^ α := hup
      _ ≤ (n : ℝ) ^ ε * (n : ℝ) ^ α :=
          mul_le_mul_of_nonneg_right hcn (Real.rpow_nonneg (le_of_lt hn_pos) _)
      _ = (n : ℝ) ^ (α + ε) := by
          rw [← Real.rpow_add hn_pos]; congr 1; ring

-- ============================================================================
-- § 6. Structural Comparisons Between Different r
-- ============================================================================

/-- The exponent hierarchy: larger r gives a larger exponent, meaning
more edges survive (larger cliques are rarer and harder to find). -/
theorem exponent_hierarchy (r₁ r₂ : ℕ) (hr₁ : 3 ≤ r₁) (hr : r₁ < r₂) :
    kRemovalExponent r₁ < kRemovalExponent r₂ :=
  kRemovalExponent_strictMono r₁ r₂ (by omega) hr

/-- Summary of conjectured exponents for small r. -/
theorem exponent_table :
    kRemovalExponent 3 = 3 / 2 ∧
    kRemovalExponent 4 = 8 / 5 ∧
    kRemovalExponent 5 = 5 / 3 :=
  ⟨kRemovalExponent_three, kRemovalExponent_four, kRemovalExponent_five⟩

-- ============================================================================
-- § 7. Connection to Turán Exponent
-- ============================================================================

/-- The removal exponent 2-2/(r+1) is always strictly less than 2
(the Turán exponent), reflecting that random removal is more efficient
than worst-case Turán constructions. -/
theorem removal_exponent_below_turan (r : ℕ) (hr : 1 ≤ r) :
    kRemovalExponent r < 2 :=
  (kRemovalExponent_bounds r hr).2

/-- The gap between the Turán exponent (2) and the removal exponent
equals 2/(r+1), which shrinks as r → ∞. -/
theorem turan_removal_gap (r : ℕ) :
    2 - kRemovalExponent r = 2 / ((r : ℝ) + 1) := by
  unfold kRemovalExponent; ring

-- ============================================================================
-- § 8. Equivalence Characterizations
-- ============================================================================

/-- Upper Θ-bound: f_r(n) ≤ C · n^α eventually. -/
def upper_theta_bound_r (r : ℕ) : Prop :=
  ∃ C : ℝ, 0 < C ∧
    ∀ᶠ (n : ℕ) in atTop,
      kCliqueRemovalEdges r n ≤ C * (n : ℝ) ^ kRemovalExponent r

/-- Lower Θ-bound: c · n^α ≤ f_r(n) eventually. -/
def lower_theta_bound_r (r : ℕ) : Prop :=
  ∃ c : ℝ, 0 < c ∧
    ∀ᶠ (n : ℕ) in atTop,
      c * (n : ℝ) ^ kRemovalExponent r ≤ kCliqueRemovalEdges r n

/-- The conjecture is equivalent to both one-sided Θ-bounds holding. -/
theorem conjecture_iff_both_bounds_r (r : ℕ) :
    kRemoval_conjecture r ↔ (upper_theta_bound_r r ∧ lower_theta_bound_r r) := by
  constructor
  · intro ⟨c₁, c₂, hc₁, hc₁c₂, h⟩
    exact ⟨⟨c₂, lt_of_lt_of_le hc₁ hc₁c₂, h.mono fun n hn => hn.2⟩,
           ⟨c₁, hc₁, h.mono fun n hn => hn.1⟩⟩
  · intro ⟨⟨C, hC, hup⟩, ⟨c, hc, hlo⟩⟩
    refine ⟨c, C, hc, ?_, hlo.and hup⟩
    by_contra hlt
    push_neg at hlt
    obtain ⟨n, ⟨hlon, hupn⟩, hn1⟩ := ((hlo.and hup).and
      (Filter.eventually_atTop.mpr ⟨1, fun n hn => hn⟩)).exists
    have hn_pos : (0 : ℝ) < (n : ℝ) ^ kRemovalExponent r := by
      apply Real.rpow_pos_of_pos; exact_mod_cast (show 0 < n by omega)
    linarith [le_trans hlon hupn, mul_lt_mul_of_pos_right hlt hn_pos]

-- ============================================================================
-- § 9. Limit Characterization
-- ============================================================================

/-- If the ratio f_r(n)/n^α converges to L > 0, then the conjecture holds. -/
theorem limit_implies_conjecture_r (r : ℕ) :
    (∃ L : ℝ, 0 < L ∧
      Filter.Tendsto (fun n : ℕ => kCliqueRemovalEdges r n / (n : ℝ) ^ kRemovalExponent r)
        atTop (nhds L)) →
    kRemoval_conjecture r := by
  intro ⟨L, hL, htends⟩
  refine ⟨L / 2, 3 * L / 2, by linarith, by linarith, ?_⟩
  have hIcc : Set.Icc (L / 2) (3 * L / 2) ∈ nhds L :=
    Icc_mem_nhds (by linarith) (by linarith)
  have hev := htends.eventually hIcc
  have hge1 : ∀ᶠ (n : ℕ) in atTop, 1 ≤ n :=
    Filter.eventually_atTop.mpr ⟨1, fun n hn => hn⟩
  apply (hev.and hge1).mono
  intro n ⟨hmem, hn1⟩
  have hn_pos : (0 : ℝ) < (n : ℝ) ^ kRemovalExponent r := by
    apply Real.rpow_pos_of_pos; exact_mod_cast (show 0 < n by omega)
  exact ⟨(le_div_iff₀ hn_pos).mp hmem.1, (div_le_iff₀ hn_pos).mp hmem.2⟩

-- ============================================================================
-- § 10. Exponent Arithmetic Verified
-- ============================================================================

/-- For r = 3, the Turán-removal gap is 2/4 = 1/2. -/
theorem gap_three : 2 - kRemovalExponent 3 = 1 / 2 := by
  rw [kRemovalExponent_three]; ring

/-- For r = 4, the gap is 2/5. -/
theorem gap_four : 2 - kRemovalExponent 4 = 2 / 5 := by
  rw [kRemovalExponent_four]; ring

/-- For r = 5, the gap is 1/3. -/
theorem gap_five : 2 - kRemovalExponent 5 = 1 / 3 := by
  rw [kRemovalExponent_five]; ring

/-- The exponent for r = 3 lies strictly between 1 and 2. -/
theorem exponent_three_range : 1 < kRemovalExponent 3 ∧ kRemovalExponent 3 < 2 := by
  rw [kRemovalExponent_three]; norm_num

/-- The exponents are strictly ordered: α(3) < α(4) < α(5). -/
theorem exponent_strict_order :
    kRemovalExponent 3 < kRemovalExponent 4 ∧
    kRemovalExponent 4 < kRemovalExponent 5 := by
  rw [kRemovalExponent_three, kRemovalExponent_four, kRemovalExponent_five]
  norm_num

end Erdos1155OQ01OQ07
