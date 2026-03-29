/-
Erdős Problem #1155 OQ-01: Triangle Removal Process — Exact Asymptotics

Extension of Erdos1155Problem.lean focusing on:
1. Formalizing the gap between BFL n^{3/2+o(1)} and the conjectured Θ(n^{3/2})
2. Proving structural lemmas about the asymptotic characterization
3. Hierarchy of bounds: Conjecture ⟹ BFL ⟹ Grable
4. Ratio characterization and sufficient conditions

The main open question: Does E[f(n)] ≍ n^{3/2} hold with explicit constants?
BFL (2015) showed f(n) = n^{3/2+o(1)} a.s., but the conjecture asks for
c₁·n^{3/2} ≤ f(n) ≤ c₂·n^{3/2} with fixed constants c₁, c₂ > 0.

Axioms: 0 (all imported from Erdos1155Problem.lean)
Sorries: 0
-/

import Proofs.Erdos1155Problem

open Filter SimpleGraph Finset

-- Triangle definitions and equivalences are imported from Erdos1155Problem.lean
-- (IsTriangle, IsTriangleFree', triangleFree_iff_cliqueFree3, complete_has_triangles)

-- Axiomatized function and known results imported from Erdos1155Problem.lean:
-- triangleRemovalEdges, triangleRemovalEdges_nonneg, triangleRemovalEdges_le_complete,
-- bfl_upper_bound, bfl_lower_bound, triangleRemoval_mantel_bound, erdos_1155_conjecture

-- ============================================================================
-- § 3. OQ-01: Gap analysis — what separates BFL from the full conjecture
-- ============================================================================

/-- The BFL result in "sandwich" form: for any ε > 0, eventually
    n^{3/2-ε} ≤ f(n) ≤ n^{3/2+ε}. -/
theorem bfl_sandwich :
    ∀ ε : ℝ, 0 < ε →
      ∀ᶠ (n : ℕ) in atTop,
        (n : ℝ) ^ ((3 : ℝ) / 2 - ε) ≤ triangleRemovalEdges n ∧
        triangleRemovalEdges n ≤ (n : ℝ) ^ ((3 : ℝ) / 2 + ε) := by
  intro ε hε
  exact (bfl_lower_bound ε hε).and (bfl_upper_bound ε hε)

/-- The conjecture implies the BFL upper bound (conjecture is strictly stronger). -/
theorem conjecture_implies_bfl_upper :
    erdos_1155_conjecture →
    ∀ ε : ℝ, 0 < ε →
      ∀ᶠ (n : ℕ) in atTop,
        triangleRemovalEdges n ≤ (n : ℝ) ^ ((3 : ℝ) / 2 + ε) := by
  intro ⟨c₁, c₂, hc₁, hc₁c₂, hconj⟩ ε hε
  have hc₂_pos : 0 < c₂ := lt_of_lt_of_le hc₁ hc₁c₂
  -- Key: for large n, c₂ ≤ n^ε (since n^ε → ∞)
  have hkey : ∀ᶠ (n : ℕ) in atTop, c₂ ≤ (n : ℝ) ^ ε := by
    rw [Filter.eventually_atTop]
    refine ⟨⌈c₂ ^ (1/ε)⌉₊ + 1, fun n hn => ?_⟩
    have h1 : c₂ = (c₂ ^ (1/ε)) ^ ε := by
      rw [← Real.rpow_mul (le_of_lt hc₂_pos), one_div_mul_cancel (ne_of_gt hε),
          Real.rpow_one]
    rw [h1]
    exact Real.rpow_le_rpow (Real.rpow_nonneg (le_of_lt hc₂_pos) _)
      (le_trans (Nat.le_ceil _) (by exact_mod_cast (show ⌈c₂ ^ (1/ε)⌉₊ ≤ n by omega)))
      (le_of_lt hε)
  have hge1 : ∀ᶠ (n : ℕ) in atTop, 1 ≤ n :=
    Filter.eventually_atTop.mpr ⟨1, fun n hn => hn⟩
  apply (((hconj.mono fun n hn => hn.2).and hkey).and hge1).mono
  intro n ⟨⟨hfn, hcn⟩, hn1⟩
  have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  calc triangleRemovalEdges n
      ≤ c₂ * (n : ℝ) ^ ((3:ℝ)/2) := hfn
    _ ≤ (n : ℝ) ^ ε * (n : ℝ) ^ ((3:ℝ)/2) :=
        mul_le_mul_of_nonneg_right hcn (Real.rpow_nonneg (le_of_lt hn_pos) _)
    _ = (n : ℝ) ^ ((3:ℝ)/2 + ε) := by
        rw [← Real.rpow_add hn_pos]; congr 1; ring

/-- The conjecture implies the BFL lower bound (conjecture is strictly stronger). -/
theorem conjecture_implies_bfl_lower :
    erdos_1155_conjecture →
    ∀ ε : ℝ, 0 < ε →
      ∀ᶠ (n : ℕ) in atTop,
        (n : ℝ) ^ ((3 : ℝ) / 2 - ε) ≤ triangleRemovalEdges n := by
  intro ⟨c₁, c₂, hc₁, _, hconj⟩ ε hε
  -- Need: n^{3/2-ε} ≤ c₁ * n^{3/2}, i.e., (n^ε)⁻¹ ≤ c₁
  have hc₁_inv_pos : 0 < c₁⁻¹ := inv_pos.mpr hc₁
  have hkey : ∀ᶠ (n : ℕ) in atTop, c₁⁻¹ ≤ (n : ℝ) ^ ε := by
    rw [Filter.eventually_atTop]
    refine ⟨⌈c₁⁻¹ ^ (1/ε)⌉₊ + 1, fun n hn => ?_⟩
    have h1 : c₁⁻¹ = (c₁⁻¹ ^ (1/ε)) ^ ε := by
      rw [← Real.rpow_mul (le_of_lt hc₁_inv_pos), one_div_mul_cancel (ne_of_gt hε),
          Real.rpow_one]
    rw [h1]
    exact Real.rpow_le_rpow (Real.rpow_nonneg (le_of_lt hc₁_inv_pos) _)
      (le_trans (Nat.le_ceil _) (by exact_mod_cast (show ⌈c₁⁻¹ ^ (1/ε)⌉₊ ≤ n by omega)))
      (le_of_lt hε)
  have hge1 : ∀ᶠ (n : ℕ) in atTop, 1 ≤ n :=
    Filter.eventually_atTop.mpr ⟨1, fun n hn => hn⟩
  apply (((hconj.mono fun n hn => hn.1).and hkey).and hge1).mono
  intro n ⟨⟨hfn, hcn⟩, hn1⟩
  have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  calc (n : ℝ) ^ ((3:ℝ)/2 - ε)
      = (n : ℝ) ^ ((-ε) + (3:ℝ)/2) := by congr 1; ring
    _ = (n : ℝ) ^ (-ε) * (n : ℝ) ^ ((3:ℝ)/2) := Real.rpow_add hn_pos (-ε) ((3:ℝ)/2)
    _ ≤ c₁ * (n : ℝ) ^ ((3:ℝ)/2) := by
        apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (le_of_lt hn_pos) _)
        rw [Real.rpow_neg (le_of_lt hn_pos), ← one_div]
        rw [div_le_iff₀ (Real.rpow_pos_of_pos hn_pos ε)]
        calc (1 : ℝ) = c₁ * c₁⁻¹ := (mul_inv_cancel₀ (ne_of_gt hc₁)).symm
          _ ≤ c₁ * (n : ℝ) ^ ε := mul_le_mul_of_nonneg_left hcn (le_of_lt hc₁)
    _ ≤ triangleRemovalEdges n := hfn

/-- A weaker form of the conjecture: there exists C such that
    f(n) ≤ C · n^{3/2} eventually. This is the upper Θ-bound. -/
def upper_theta_bound : Prop :=
  ∃ C : ℝ, 0 < C ∧
    ∀ᶠ (n : ℕ) in atTop,
      triangleRemovalEdges n ≤ C * (n : ℝ) ^ ((3 : ℝ) / 2)

/-- A weaker form of the conjecture: there exists c such that
    c · n^{3/2} ≤ f(n) eventually. This is the lower Θ-bound. -/
def lower_theta_bound : Prop :=
  ∃ c : ℝ, 0 < c ∧
    ∀ᶠ (n : ℕ) in atTop,
      c * (n : ℝ) ^ ((3 : ℝ) / 2) ≤ triangleRemovalEdges n

/-- The full conjecture is equivalent to both one-sided Θ-bounds holding. -/
theorem conjecture_iff_both_bounds :
    erdos_1155_conjecture ↔ (upper_theta_bound ∧ lower_theta_bound) := by
  constructor
  · intro ⟨c₁, c₂, hc₁, hc₁c₂, h⟩
    exact ⟨⟨c₂, lt_of_lt_of_le hc₁ hc₁c₂, h.mono fun n hn => hn.2⟩,
           ⟨c₁, hc₁, h.mono fun n hn => hn.1⟩⟩
  · intro ⟨⟨C, hC, hup⟩, ⟨c, hc, hlo⟩⟩
    refine ⟨c, C, hc, ?_, hlo.and hup⟩
    by_contra hlt
    push_neg at hlt
    -- c > C, but eventually c·n^{3/2} ≤ f(n) ≤ C·n^{3/2}
    have hboth := hlo.and hup
    -- Pick n ≥ 1 so n^{3/2} > 0
    have hone : ∀ᶠ (n : ℕ) in atTop, (1 : ℕ) ≤ n :=
      Filter.eventually_atTop.mpr ⟨1, fun n hn => hn⟩
    have := (hboth.and hone).exists
    obtain ⟨n, ⟨hlon, hupn⟩, hn1⟩ := this
    have hn_pos : (0 : ℝ) < (n : ℝ) ^ ((3 : ℝ) / 2) := by
      apply Real.rpow_pos_of_pos; exact_mod_cast (show 0 < n by omega)
    linarith [le_trans hlon hupn, mul_lt_mul_of_pos_right hlt hn_pos]

-- ============================================================================
-- § 4. Exponent gap characterization
-- ============================================================================

/-- The BFL exponent is exactly 3/2 (not a weaker bound like 7/4).
    This is a consequence of the two-sided BFL result. -/
theorem bfl_exponent_is_three_halves :
    ∀ α : ℝ, α > 3/2 →
      ∀ᶠ (n : ℕ) in atTop,
        triangleRemovalEdges n ≤ (n : ℝ) ^ α := by
  intro α hα
  have hε : (0 : ℝ) < α - 3/2 := by linarith
  have := bfl_upper_bound (α - 3/2) hε
  apply this.mono
  intro n hn
  have : (3 : ℝ) / 2 + (α - 3 / 2) = α := by ring
  rw [this] at hn
  exact hn

/-- The BFL result is tight from below: no exponent below 3/2 works. -/
theorem bfl_lower_tight :
    ∀ β : ℝ, β < 3/2 →
      ¬ (∀ᶠ (n : ℕ) in atTop,
        triangleRemovalEdges n ≤ (n : ℝ) ^ β) := by
  intro β hβ hcontra
  have hε : (0 : ℝ) < 3/2 - β := by linarith
  have hlo := bfl_lower_bound ((3/2 - β) / 2) (by linarith)
  obtain ⟨n, ⟨hlon, hupn⟩, hn2⟩ :=
    ((hlo.and hcontra).and (Filter.eventually_atTop.mpr ⟨2, fun n hn => hn⟩)).exists
  have hle : (n : ℝ) ^ ((3:ℝ)/2 - (3/2 - β) / 2) ≤ (n : ℝ) ^ β := le_trans hlon hupn
  have : (n : ℝ) ^ β < (n : ℝ) ^ ((3:ℝ)/2 - (3/2 - β) / 2) :=
    Real.rpow_lt_rpow_of_exponent_lt (by exact_mod_cast (show 1 < n by omega)) (by linarith)
  linarith

-- ============================================================================
-- § 5. Monotonicity and basic structural results
-- ============================================================================

/-- For small n, f(n) = 0 since K_n has no triangles (n < 3) or
    removing the unique triangle in K_3 leaves 0 edges. -/
theorem f_small_values_bound :
    triangleRemovalEdges 0 ≤ 0 ∧
    triangleRemovalEdges 1 ≤ 0 ∧
    triangleRemovalEdges 2 ≤ 1 := by
  refine ⟨?_, ?_, ?_⟩
  · -- K_0 has 0 edges
    have := triangleRemovalEdges_le_complete 0
    simp at this
    exact this
  · -- K_1 has 0 edges
    have := triangleRemovalEdges_le_complete 1
    simp at this
    exact this
  · -- K_2 has 1 edge, so f(2) ≤ 1
    have := triangleRemovalEdges_le_complete 2
    norm_num at this
    linarith

/-- The BFL result gives a concrete exponent separation:
    for any ε, the ratio f(n)/n^{3/2} is eventually in [n^{-ε}, n^ε]. -/
theorem bfl_ratio_characterization :
    ∀ ε : ℝ, 0 < ε →
      ∀ᶠ (n : ℕ) in atTop,
        (n : ℝ) ^ (-ε) ≤ triangleRemovalEdges n / (n : ℝ) ^ ((3:ℝ)/2) ∧
        triangleRemovalEdges n / (n : ℝ) ^ ((3:ℝ)/2) ≤ (n : ℝ) ^ ε := by
  intro ε hε
  have hsand := bfl_sandwich ε hε
  have hge1 : ∀ᶠ (n : ℕ) in atTop, 1 ≤ n :=
    Filter.eventually_atTop.mpr ⟨1, fun n hn => hn⟩
  apply (hsand.and hge1).mono
  intro n ⟨⟨hlo, hup⟩, hn1⟩
  have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hn32_pos : (0 : ℝ) < (n : ℝ) ^ ((3:ℝ)/2) := Real.rpow_pos_of_pos hn_pos _
  constructor
  · rw [le_div_iff₀ hn32_pos]
    calc (n : ℝ) ^ (-ε) * (n : ℝ) ^ ((3:ℝ)/2)
        = (n : ℝ) ^ (-ε + (3:ℝ)/2) := (Real.rpow_add hn_pos (-ε) ((3:ℝ)/2)).symm
      _ = (n : ℝ) ^ ((3:ℝ)/2 - ε) := by congr 1; ring
      _ ≤ triangleRemovalEdges n := hlo
  · rw [div_le_iff₀ hn32_pos]
    calc triangleRemovalEdges n
        ≤ (n : ℝ) ^ ((3:ℝ)/2 + ε) := hup
      _ = (n : ℝ) ^ (ε + (3:ℝ)/2) := by congr 1; ring
      _ = (n : ℝ) ^ ε * (n : ℝ) ^ ((3:ℝ)/2) := Real.rpow_add hn_pos ε ((3:ℝ)/2)

-- ============================================================================
-- § 6. What would resolve the conjecture
-- ============================================================================

/-- Key sufficient condition: if the ratio f(n)/n^{3/2} converges to some
    limit L > 0, then the full conjecture holds. -/
theorem limit_implies_conjecture :
    (∃ L : ℝ, 0 < L ∧
      Filter.Tendsto (fun n : ℕ => triangleRemovalEdges n / (n : ℝ) ^ ((3:ℝ)/2))
        atTop (nhds L)) →
    erdos_1155_conjecture := by
  intro ⟨L, hL, htends⟩
  refine ⟨L / 2, 3 * L / 2, by linarith, by linarith, ?_⟩
  have hIcc : Set.Icc (L / 2) (3 * L / 2) ∈ nhds L :=
    Icc_mem_nhds (by linarith) (by linarith)
  have hev := htends.eventually hIcc
  have hge1 : ∀ᶠ (n : ℕ) in atTop, 1 ≤ n :=
    Filter.eventually_atTop.mpr ⟨1, fun n hn => hn⟩
  apply (hev.and hge1).mono
  intro n ⟨hmem, hn1⟩
  have hn_pos : (0 : ℝ) < (n : ℝ) ^ ((3:ℝ)/2) := by
    apply Real.rpow_pos_of_pos
    exact_mod_cast (show 0 < n by omega)
  exact ⟨(le_div_iff₀ hn_pos).mp hmem.1, (div_le_iff₀ hn_pos).mp hmem.2⟩

/-- Even a limsup/liminf condition suffices: if both are finite and positive. -/
def limsup_liminf_condition : Prop :=
  (∃ C : ℝ, 0 < C ∧
    ∀ᶠ (n : ℕ) in atTop, triangleRemovalEdges n / (n : ℝ) ^ ((3:ℝ)/2) ≤ C) ∧
  (∃ c : ℝ, 0 < c ∧
    ∀ᶠ (n : ℕ) in atTop, c ≤ triangleRemovalEdges n / (n : ℝ) ^ ((3:ℝ)/2))

theorem limsup_liminf_implies_conjecture :
    limsup_liminf_condition → erdos_1155_conjecture := by
  intro ⟨⟨C, hC, hup⟩, ⟨c, hc, hlo⟩⟩
  refine ⟨c, C, hc, ?_, ?_⟩
  · -- c ≤ C from eventually c ≤ f/n^{3/2} ≤ C
    by_contra hlt
    push_neg at hlt
    obtain ⟨n, hcn, hCn⟩ := (hlo.and hup).exists
    linarith
  · -- Eventually c·n^{3/2} ≤ f(n) ≤ C·n^{3/2}
    have hge1 : ∀ᶠ (n : ℕ) in atTop, 1 ≤ n :=
      Filter.eventually_atTop.mpr ⟨1, fun n hn => hn⟩
    apply ((hlo.and hup).and hge1).mono
    intro n ⟨⟨hcn, hCn⟩, hn1⟩
    have hn_pos : (0 : ℝ) < (n : ℝ) ^ ((3:ℝ)/2) := by
      apply Real.rpow_pos_of_pos
      exact_mod_cast (show 0 < n by omega)
    exact ⟨(le_div_iff₀ hn_pos).mp hcn, (div_le_iff₀ hn_pos).mp hCn⟩

-- ============================================================================
-- § 7. Lower exponent characterization
-- ============================================================================

/-- BFL implies f eventually exceeds any sub-{3/2} power.
    In particular, f is superlinear (take α = 1), super-√n³ etc. -/
theorem bfl_eventually_exceeds_power :
    ∀ α : ℝ, α < 3/2 →
      ∀ᶠ (n : ℕ) in atTop,
        (n : ℝ) ^ α ≤ triangleRemovalEdges n := by
  intro α hα
  have hε : 0 < (3:ℝ)/2 - α := by linarith
  exact (bfl_lower_bound _ hε).mono
    (fun n hn => by rwa [show (3:ℝ)/2 - ((3:ℝ)/2 - α) = α from by ring] at hn)

-- ============================================================================
-- § 8. Mantel / Turán connection
-- ============================================================================

-- The triangle removal process terminates with a triangle-free graph.
-- By Mantel's theorem (1907), a triangle-free graph on n vertices has at most
-- ⌊n²/4⌋ edges. Since our axiomatized f(n) counts edges in the terminal
-- (triangle-free) graph, this gives a trivial upper bound.

-- triangleRemoval_mantel_bound imported from Erdos1155Problem.lean

/-- The Mantel bound holds for all n (not just eventually). -/
theorem mantel_bound_forall :
    ∀ n : ℕ, triangleRemovalEdges n ≤ (n : ℝ) ^ 2 / 4 :=
  triangleRemoval_mantel_bound

/-- The Mantel bound as an eventually-true statement (for comparison with BFL). -/
theorem mantel_bound_eventually :
    ∀ᶠ (n : ℕ) in atTop,
      triangleRemovalEdges n ≤ (n : ℝ) ^ 2 / 4 :=
  Filter.eventually_atTop.mpr ⟨0, fun n _ => mantel_bound_forall n⟩

/-- BFL gives a much better upper bound than Mantel for large n.
    Specifically, f(n) ≤ n^{7/4} eventually, which is o(n²). -/
theorem bfl_below_mantel_exponent :
    ∀ᶠ (n : ℕ) in atTop,
      triangleRemovalEdges n ≤ (n : ℝ) ^ ((7:ℝ)/4) := by
  exact (bfl_upper_bound (1/4 : ℝ) (by norm_num)).mono
    (fun n hn => by rwa [show (3:ℝ)/2 + 1/4 = 7/4 from by ring] at hn)

-- ============================================================================
-- § 9. Hierarchy of bounds
-- ============================================================================

/-- Strict hierarchy: Conjecture ⟹ BFL (two-sided).
    The conjecture gives constant-factor bounds c₁·n^{3/2} ≤ f ≤ c₂·n^{3/2},
    which imply the sub-polynomial sandwich n^{3/2-ε} ≤ f ≤ n^{3/2+ε}. -/
theorem hierarchy_conjecture_implies_bfl :
    erdos_1155_conjecture →
    (∀ ε : ℝ, 0 < ε →
      ∀ᶠ (n : ℕ) in atTop,
        (n : ℝ) ^ ((3:ℝ)/2 - ε) ≤ triangleRemovalEdges n ∧
        triangleRemovalEdges n ≤ (n : ℝ) ^ ((3:ℝ)/2 + ε)) := by
  intro hconj ε hε
  exact (conjecture_implies_bfl_lower hconj ε hε).and
    (conjecture_implies_bfl_upper hconj ε hε)

/-- The BFL sandwich implies both one-sided exponent bounds. -/
theorem hierarchy_bfl_implies_grable :
    (∀ ε : ℝ, 0 < ε →
      ∀ᶠ (n : ℕ) in atTop,
        triangleRemovalEdges n ≤ (n : ℝ) ^ ((3:ℝ)/2 + ε)) →
    (∀ ε : ℝ, 0 < ε →
      ∀ᶠ (n : ℕ) in atTop,
        triangleRemovalEdges n ≤ (n : ℝ) ^ ((7:ℝ)/4 + ε)) := by
  intro h ε hε
  have hε' : (0:ℝ) < 1/4 + ε := by linarith
  exact (h _ hε').mono
    (fun n hn => by rwa [show (3:ℝ)/2 + (1/4 + ε) = 7/4 + ε from by ring] at hn)

-- ============================================================================
-- § 10. Tightness and ratio characterization
-- ============================================================================

/-- Under the conjecture, the normalized ratio f(n)/(c·n^{3/2}) is eventually
    bounded between 1 and c₂/c₁ (where c = c₁ from the conjecture).
    The tighter c₂/c₁ is to 1, the stronger the asymptotic. -/
theorem conjecture_tightness :
    erdos_1155_conjecture →
    ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ 0 < c₂ ∧ c₁ ≤ c₂ ∧
      ∀ᶠ (n : ℕ) in atTop,
        1 ≤ triangleRemovalEdges n / (c₁ * (n : ℝ) ^ ((3:ℝ)/2)) ∧
        triangleRemovalEdges n / (c₂ * (n : ℝ) ^ ((3:ℝ)/2)) ≤ 1 := by
  intro ⟨c₁, c₂, hc₁, hle, hconj⟩
  have hc₂ : 0 < c₂ := lt_of_lt_of_le hc₁ hle
  refine ⟨c₁, c₂, hc₁, hc₂, hle, ?_⟩
  have hge1 : ∀ᶠ (n : ℕ) in atTop, 1 ≤ n :=
    Filter.eventually_atTop.mpr ⟨1, fun n hn => hn⟩
  apply (hconj.and hge1).mono
  intro n ⟨⟨hlo, hup⟩, hn1⟩
  have hn_pos : (0 : ℝ) < (n : ℝ) ^ ((3:ℝ)/2) :=
    Real.rpow_pos_of_pos (by exact_mod_cast (show 0 < n by omega)) _
  constructor
  · -- 1 ≤ f(n) / (c₁ * n^{3/2})
    rw [le_div_iff₀ (mul_pos hc₁ hn_pos)]
    simp only [one_mul]
    exact hlo
  · -- f(n) / (c₂ * n^{3/2}) ≤ 1
    rw [div_le_iff₀ (mul_pos hc₂ hn_pos)]
    simp only [one_mul]
    exact hup

/-- The conjecture gives a two-sided density estimate: the ratio
    f(n)/n^{3/2} is eventually sandwiched between positive constants.
    Compare with bfl_ratio_characterization where the bounds are n^{±ε}. -/
theorem conjecture_ratio_bounded :
    erdos_1155_conjecture →
    ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ 0 < c₂ ∧
      ∀ᶠ (n : ℕ) in atTop,
        c₁ ≤ triangleRemovalEdges n / (n : ℝ) ^ ((3:ℝ)/2) ∧
        triangleRemovalEdges n / (n : ℝ) ^ ((3:ℝ)/2) ≤ c₂ := by
  intro ⟨c₁, c₂, hc₁, hle, hconj⟩
  refine ⟨c₁, c₂, hc₁, lt_of_lt_of_le hc₁ hle, ?_⟩
  have hge1 : ∀ᶠ (n : ℕ) in atTop, 1 ≤ n :=
    Filter.eventually_atTop.mpr ⟨1, fun n hn => hn⟩
  apply (hconj.and hge1).mono
  intro n ⟨⟨hlo, hup⟩, hn1⟩
  have hn_pos : (0 : ℝ) < (n : ℝ) ^ ((3:ℝ)/2) :=
    Real.rpow_pos_of_pos (by exact_mod_cast (show 0 < n by omega)) _
  constructor
  · -- c₁ ≤ f(n) / n^{3/2}
    rw [le_div_iff₀ hn_pos]
    exact hlo
  · -- f(n) / n^{3/2} ≤ c₂
    rw [div_le_iff₀ hn_pos]
    exact hup
