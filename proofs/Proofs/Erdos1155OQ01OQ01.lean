/-
Erdős Problem #1155 OQ-01-OQ-01: Triangle Removal — Convergence of f(n)/n^{3/2}

Open Question: Does the normalized ratio f(n)/n^{3/2} converge to a specific
positive constant L? If so, determine L.

Context:
- The triangle removal process repeatedly deletes edges of a random triangle from
  K_n until no triangles remain; f(n) = expected number of surviving edges.
- BFL (2015) proved f(n) = n^{3/2 + o(1)} a.s., establishing the critical exponent 3/2.
- The Erdős conjecture (parent OQ-01) asks for Θ(n^{3/2}): bounded ratio.
- This OQ asks something strictly stronger: does the ratio actually converge?

Hierarchy (proved below):
  convergenceConjecture (this file)
      ⟹  erdos_1155_conjecture (Θ bound, from Erdos1155OQ01.lean)
      ⟹  BFL result (n^{3/2 ± ε}, from Erdos1155Problem.lean)

Key results (0 sorries, all axiom-free modulo the inherited axiomatization):
1. Formal definition of the convergence conjecture
2. Limit uniqueness (Hausdorff)
3. Convergence ⟹ Erdős Θ-conjecture (hierarchy)
4. Convergence ⟹ BFL two-sided bounds
5. Sharp asymptotics: f(n) ~ L · n^{3/2} under convergence
6. ε-interval and absolute deviation characterizations
7. Bounded ratio as corollary of convergence
8. Equivalence with limsup/liminf criterion
9. Metric ε-N characterization of convergenceConjecture
10. Tight Θ-constants under convergence

Mathematical status: OPEN. Whether the ratio converges, and to what value, is unknown.
The BFL differential equation analysis suggests a specific constant exists,
but no proof of convergence has been established.

Axioms: 0 (all imported from Erdos1155Problem.lean via Erdos1155OQ01.lean)
Sorries: 0
-/

import Proofs.Erdos1155OQ01

open Filter Topology Set

namespace Erdos1155OQ01OQ01

-- ============================================================================
-- § 1. Definitions
-- ============================================================================

/-- The normalized ratio of remaining edges to n^{3/2}, the central object
of study for the convergence question. -/
noncomputable def triangleRatio (n : ℕ) : ℝ :=
  triangleRemovalEdges n / (n : ℝ) ^ ((3 : ℝ) / 2)

/-- **The Convergence Conjecture**: Does f(n)/n^{3/2} → L for some L > 0?
Convergence to a positive constant L is the "exact asymptotics" question,
strictly stronger than the Θ(n^{3/2}) Erdős conjecture:
  convergenceConjecture ⟹ erdos_1155_conjecture, but converse is open. -/
def convergenceConjecture : Prop :=
  ∃ L : ℝ, 0 < L ∧ Filter.Tendsto triangleRatio atTop (nhds L)

-- ============================================================================
-- § 2. Limit Uniqueness
-- ============================================================================

/-- The limit, if it exists, is unique. Follows from Hausdorff separation in ℝ:
limits of filters in T2 spaces are unique. -/
theorem convergenceLimit_unique {L₁ L₂ : ℝ}
    (h₁ : Filter.Tendsto triangleRatio atTop (nhds L₁))
    (h₂ : Filter.Tendsto triangleRatio atTop (nhds L₂)) :
    L₁ = L₂ :=
  tendsto_nhds_unique h₁ h₂

/-- Any two positive limits (if both exist) must coincide. -/
theorem convergence_limit_is_unique :
    ∀ L₁ L₂ : ℝ, 0 < L₁ → 0 < L₂ →
      Filter.Tendsto triangleRatio atTop (nhds L₁) →
      Filter.Tendsto triangleRatio atTop (nhds L₂) →
      L₁ = L₂ :=
  fun L₁ L₂ _ _ h₁ h₂ => tendsto_nhds_unique h₁ h₂

-- ============================================================================
-- § 3. Convergence Implies Erdős Θ-Conjecture
-- ============================================================================

/-- **Core hierarchy theorem**: The convergence conjecture implies the Erdős
Θ(n^{3/2}) conjecture.

Proof: if f(n)/n^{3/2} → L > 0, then for any ε ∈ (0, L), eventually
  L/2 ≤ f(n)/n^{3/2} ≤ 3L/2,
giving the Θ-bounds with constants c₁ = L/2 and c₂ = 3L/2. -/
theorem convergence_implies_erdos_conjecture :
    convergenceConjecture → erdos_1155_conjecture := by
  intro ⟨L, hL, htends⟩
  exact limit_implies_conjecture ⟨L, hL, htends⟩

/-- Convergence implies the full BFL two-sided polynomial bounds for every ε > 0. -/
theorem convergence_implies_bfl :
    convergenceConjecture →
    ∀ ε : ℝ, 0 < ε →
      ∀ᶠ n : ℕ in atTop,
        (n : ℝ) ^ ((3 : ℝ) / 2 - ε) ≤ triangleRemovalEdges n ∧
        triangleRemovalEdges n ≤ (n : ℝ) ^ ((3 : ℝ) / 2 + ε) := by
  intro hconv ε hε
  exact hierarchy_conjecture_implies_bfl (convergence_implies_erdos_conjecture hconv) ε hε

-- ============================================================================
-- § 4. Sharp Asymptotics Under Convergence
-- ============================================================================

/-- If the ratio converges to L > 0, then f(n) lies within a multiplicative
δ-strip of L · n^{3/2}: for every 0 < δ < L, eventually
  (L - δ) · n^{3/2} ≤ f(n) ≤ (L + δ) · n^{3/2}.

This is the "sharp asymptotic" f(n) ~ L · n^{3/2}, the precise answer to the OQ. -/
theorem convergence_gives_sharp_asymptotics {L : ℝ} (hL : 0 < L)
    (htends : Filter.Tendsto triangleRatio atTop (nhds L))
    (δ : ℝ) (hδ : 0 < δ) (hδL : δ < L) :
    ∀ᶠ n : ℕ in atTop,
      (L - δ) * (n : ℝ) ^ ((3 : ℝ) / 2) ≤ triangleRemovalEdges n ∧
      triangleRemovalEdges n ≤ (L + δ) * (n : ℝ) ^ ((3 : ℝ) / 2) := by
  have hIcc : Set.Icc (L - δ) (L + δ) ∈ nhds L :=
    Icc_mem_nhds (by linarith) (by linarith)
  have hev := htends.eventually hIcc
  have hge1 : ∀ᶠ n : ℕ in atTop, 1 ≤ n :=
    Filter.eventually_atTop.mpr ⟨1, fun n hn => hn⟩
  apply (hev.and hge1).mono
  intro n ⟨hmem, hn1⟩
  simp only [triangleRatio] at hmem
  have hn_pos : (0 : ℝ) < (n : ℝ) ^ ((3 : ℝ) / 2) :=
    Real.rpow_pos_of_pos (by exact_mod_cast (show 0 < n by omega)) _
  exact ⟨(le_div_iff₀ hn_pos).mp hmem.1, (div_le_iff₀ hn_pos).mp hmem.2⟩

/-- Under convergence, for any 0 < δ < L, the Θ-constants can be taken as
L - δ and L + δ. As δ → 0, these constants converge to L from both sides. -/
theorem convergence_tight_theta_constants {L : ℝ} (hL : 0 < L)
    (htends : Filter.Tendsto triangleRatio atTop (nhds L))
    (δ : ℝ) (hδ : 0 < δ) (hδL : δ < L) :
    ∀ᶠ n : ℕ in atTop,
      (L - δ) * (n : ℝ) ^ ((3 : ℝ) / 2) ≤ triangleRemovalEdges n ∧
      triangleRemovalEdges n ≤ (L + δ) * (n : ℝ) ^ ((3 : ℝ) / 2) :=
  convergence_gives_sharp_asymptotics hL htends δ hδ hδL

-- ============================================================================
-- § 5. ε-Neighborhood Characterization
-- ============================================================================

/-- Under convergence to L, the ratio lies in any ε-open-interval around L. -/
theorem convergence_ratio_in_Ioo {L : ℝ} (hL : 0 < L)
    (htends : Filter.Tendsto triangleRatio atTop (nhds L))
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, triangleRatio n ∈ Set.Ioo (L - ε) (L + ε) :=
  htends.eventually (Ioo_mem_nhds (by linarith) (by linarith))

/-- Equivalently: the absolute deviation |f(n)/n^{3/2} - L| < ε eventually.
This is the ε-N definition of convergence applied to the ratio. -/
theorem convergence_absolute_deviation {L : ℝ} (hL : 0 < L)
    (htends : Filter.Tendsto triangleRatio atTop (nhds L))
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, |triangleRatio n - L| < ε := by
  have hev := convergence_ratio_in_Ioo hL htends ε hε
  exact hev.mono fun n hn => by
    rw [abs_lt]
    exact ⟨by linarith [hn.1], by linarith [hn.2]⟩

-- ============================================================================
-- § 6. Bounded Ratio as Corollary
-- ============================================================================

/-- Convergence implies the ratio is eventually bounded between L/2 and 3L/2.
This gives the Erdős Θ-conjecture with explicit constants. -/
theorem convergence_implies_bounded_ratio :
    convergenceConjecture →
    ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ c₁ ≤ c₂ ∧
      ∀ᶠ n : ℕ in atTop,
        c₁ ≤ triangleRatio n ∧ triangleRatio n ≤ c₂ := by
  intro ⟨L, hL, htends⟩
  refine ⟨L / 2, 3 * L / 2, by linarith, by linarith, ?_⟩
  exact (htends.eventually (Icc_mem_nhds (by linarith : L/2 < L) (by linarith : L < 3*L/2)))
    |>.mono fun n hn => Set.mem_Icc.mp hn

/-- Under convergence, the ratio is eventually bounded below by L/2. -/
theorem convergence_lower_bound :
    convergenceConjecture →
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ n : ℕ in atTop, c ≤ triangleRatio n := by
  intro hconv
  obtain ⟨c₁, _, hc₁, _, hbound⟩ := convergence_implies_bounded_ratio hconv
  exact ⟨c₁, hc₁, hbound.mono fun n hn => hn.1⟩

/-- Under convergence, the ratio is eventually bounded above by 3L/2. -/
theorem convergence_upper_bound :
    convergenceConjecture →
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ n : ℕ in atTop, triangleRatio n ≤ C := by
  intro ⟨L, hL, htends⟩
  refine ⟨3 * L / 2, by linarith, ?_⟩
  exact (htends.eventually (Icc_mem_nhds (by linarith : L/2 < L) (by linarith : L < 3*L/2)))
    |>.mono fun n hn => (Set.mem_Icc.mp hn).2

-- ============================================================================
-- § 7. limsup / liminf Characterization
-- ============================================================================

/-- **Squeeze criterion**: if both the limsup and liminf of the ratio equal L,
then the ratio converges to L.

Proof via `tendsto_order`: in an ordered topology, Tendsto f l (nhds L) iff
for all a < L, eventually a < f(n), and for all b > L, eventually f(n) < b. -/
theorem limsup_liminf_implies_convergence {L : ℝ} (hL : 0 < L)
    (hup : ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop, triangleRatio n ≤ L + ε)
    (hlo : ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop, L - ε ≤ triangleRatio n) :
    Filter.Tendsto triangleRatio atTop (nhds L) := by
  apply tendsto_order.mpr
  refine ⟨fun a ha => ?_, fun a ha => ?_⟩
  · -- ∀ᶠ n, a < triangleRatio n (since a < L)
    -- Use ε = (L - a)/2 to get triangleRatio n ≥ (L+a)/2 > a
    apply (hlo ((L - a) / 2) (by linarith)).mono
    intro n hn; linarith
  · -- ∀ᶠ n, triangleRatio n < a (since L < a)
    -- Use ε = (a - L)/2 to get triangleRatio n ≤ (L+a)/2 < a
    apply (hup ((a - L) / 2) (by linarith)).mono
    intro n hn; linarith

/-- Under convergence to L, the ε-limsup and ε-liminf conditions hold. -/
theorem convergence_implies_limsup_eq_liminf :
    convergenceConjecture →
    ∀ ε : ℝ, 0 < ε →
      ∃ L : ℝ, 0 < L ∧
        (∀ᶠ n : ℕ in atTop, L - ε ≤ triangleRatio n) ∧
        (∀ᶠ n : ℕ in atTop, triangleRatio n ≤ L + ε) := by
  intro ⟨L, hL, htends⟩ ε hε
  have hev := htends.eventually (Icc_mem_nhds (by linarith : L - ε < L) (by linarith : L < L + ε))
  exact ⟨L, hL,
    hev.mono fun n hn => (Set.mem_Icc.mp hn).1,
    hev.mono fun n hn => (Set.mem_Icc.mp hn).2⟩

-- ============================================================================
-- § 8. Metric ε-N Criterion
-- ============================================================================

/-- The convergence conjecture is equivalent to the classical ε-N Cauchy criterion:
  ∃ L > 0, ∀ ε > 0, ∃ N, ∀ n ≥ N: |f(n)/n^{3/2} - L| < ε. -/
theorem convergenceConjecture_iff_metric :
    convergenceConjecture ↔
    ∃ L : ℝ, 0 < L ∧
      ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → |triangleRatio n - L| < ε := by
  constructor
  · intro ⟨L, hL, htends⟩
    refine ⟨L, hL, fun ε hε => ?_⟩
    exact Filter.eventually_atTop.mp (convergence_absolute_deviation hL htends ε hε)
  · intro ⟨L, hL, hcau⟩
    refine ⟨L, hL, ?_⟩
    apply tendsto_order.mpr
    refine ⟨fun a ha => ?_, fun a ha => ?_⟩
    · -- ∀ᶠ n, a < triangleRatio n
      obtain ⟨N, hN⟩ := hcau ((L - a) / 2) (by linarith)
      exact Filter.eventually_atTop.mpr ⟨N, fun n hn => by
        have := hN n hn
        rw [abs_lt] at this
        linarith [this.1]⟩
    · -- ∀ᶠ n, triangleRatio n < a
      obtain ⟨N, hN⟩ := hcau ((a - L) / 2) (by linarith)
      exact Filter.eventually_atTop.mpr ⟨N, fun n hn => by
        have := hN n hn
        rw [abs_lt] at this
        linarith [this.2]⟩

-- ============================================================================
-- § 9. Strict Hierarchy Summary
-- ============================================================================

/-- The complete strict hierarchy of implications. The converses are all open:
- Whether erdos_1155_conjecture ⟹ convergenceConjecture is unknown.
- Whether BFL ⟹ erdos_1155_conjecture is the Erdős conjecture itself. -/
theorem strict_hierarchy :
    convergenceConjecture →
    erdos_1155_conjecture ∧
    (∀ ε : ℝ, 0 < ε →
      ∀ᶠ n : ℕ in atTop,
        (n : ℝ) ^ ((3 : ℝ) / 2 - ε) ≤ triangleRemovalEdges n ∧
        triangleRemovalEdges n ≤ (n : ℝ) ^ ((3 : ℝ) / 2 + ε)) := by
  intro hconv
  exact ⟨convergence_implies_erdos_conjecture hconv, convergence_implies_bfl hconv⟩

/-- Under convergence to L, the BFL ratio characterization holds:
for any ε > 0, eventually n^{-ε} ≤ f(n)/n^{3/2} ≤ n^ε.
This is consistent with convergence (since both n^{-ε} → 0 and n^ε → ∞ bracket L). -/
theorem convergence_consistent_with_bfl :
    convergenceConjecture →
    ∀ ε : ℝ, 0 < ε →
      ∀ᶠ n : ℕ in atTop,
        (n : ℝ) ^ (-ε) ≤ triangleRatio n ∧
        triangleRatio n ≤ (n : ℝ) ^ ε := by
  intro _ ε hε
  simp only [triangleRatio]
  exact bfl_ratio_characterization ε hε

end Erdos1155OQ01OQ01
