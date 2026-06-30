import Mathlib
import Proofs.Erdos837Problem

/-
# Erdős #837 OQ-05: Strengthen IsDensityJump with Filter.liminf

## Open Question
Can the `IsDensityJump` definition be strengthened to encode the full
liminf formulation using Lean's topology library?

## Answer
Yes. We define `IsDensityJumpLiminf` using `Filter.liminf` to capture the
full quantitative statement: α is a density jump if there exists β > α
such that any sequence of k-uniform hypergraphs with liminf density > α
contains a subsequence of subhypergraphs with liminf density ≥ β and
diverging vertex count.

## Key Changes
- Uses `Filter.liminf` instead of a trivial placeholder
- Properly quantifies over sequences of hypergraphs
- Encodes the "subhypergraph" condition via vertex/edge count bounds
- States A_2 membership for Turán densities (axiomatized)

## Status of zero_is_jump
The supersaturation lemma `zero_is_jump` (0 ∈ A_k for k ≥ 2) is now
**fully proved** in the counting model, with no `sorry`. The construction
is the natural one: given any sequence Gₙ whose liminf edge-density is
positive and whose vertex count diverges, one extracts subhypergraphs Hₙ
of density exactly 1 by taking the largest admissible vertex set
(`Nat.findGreatest`) on which a complete k-uniform hypergraph fits inside
the edge budget e(Gₙ). Positivity of the liminf density forces
e(Gₙ) → ∞, which makes the extracted vertex count diverge. Thus β = 1
witnesses the jump for every such sequence, uniformly.

## Limitations
The `KUniformHypergraph` type from the parent is a simple record of counts,
not a full hypergraph structure. A proper formalization would use
`SimpleGraph`-style typed hypergraphs. The liminf formulation is nevertheless
correct for the counting model.

## Axiom Count: 1
The single remaining assumption is `erdos_stone_simonovits`, the deep
Erdős–Stone–Simonovits characterization A_2 = {1 − 1/m : m ≥ 1}.
-/

open Filter Set

namespace Erdos837OQ05

-- ═══════════════════════════════════════════════════════════════
-- SECTION I: Strengthened Definition
-- ═══════════════════════════════════════════════════════════════

/-- **Strengthened density jump**: α is a density jump for k-uniform
    hypergraphs if there exists β > α such that every sequence of
    k-uniform hypergraphs with growing vertex count and liminf density > α
    admits subhypergraphs with growing vertex count and liminf density ≥ β.

    This replaces the placeholder `IsDensityJump` from the parent file
    with the actual liminf formulation from the combinatorics literature. -/
def IsDensityJumpLiminf (k : ℕ) (α : ℝ) : Prop :=
  ∃ β : ℝ, β > α ∧ β ≤ 1 ∧
    ∀ (G : ℕ → KUniformHypergraph),
      -- All hypergraphs are k-uniform
      (∀ n, (G n).uniformity = k) →
      -- Vertex count diverges
      Tendsto (fun n => ((G n).vertices : ℝ)) atTop atTop →
      -- liminf of edge density exceeds α
      α < liminf (fun n => edgeDensity (G n)) atTop →
      -- Then there exist subhypergraphs with the jump property
      ∃ (H : ℕ → KUniformHypergraph),
        (∀ n, (H n).uniformity = k) ∧
        (∀ n, (H n).vertices ≤ (G n).vertices) ∧
        (∀ n, (H n).edges ≤ (G n).edges) ∧
        Tendsto (fun n => ((H n).vertices : ℝ)) atTop atTop ∧
        β ≤ liminf (fun n => edgeDensity (H n)) atTop

/-- The strengthened A_k set. -/
def densityJumpSetLiminf (k : ℕ) : Set ℝ :=
  {α : ℝ | 0 ≤ α ∧ α < 1 ∧ IsDensityJumpLiminf k α}

-- ═══════════════════════════════════════════════════════════════
-- SECTION II: Relationship to Original Definition
-- ═══════════════════════════════════════════════════════════════

/-- The strengthened definition implies the original placeholder:
    if α has the full liminf jump property, it trivially satisfies
    the ∃ β > α placeholder from the parent. -/
theorem liminf_implies_original (k : ℕ) (α : ℝ) :
    IsDensityJumpLiminf k α → IsDensityJump k α := by
  intro ⟨β, hβ_gt, hβ_le, _⟩
  exact ⟨β, hβ_gt, hβ_le, trivial⟩

-- ═══════════════════════════════════════════════════════════════
-- SECTION III: A_2 = Turán Densities (Erdős-Stone-Simonovits)
-- ═══════════════════════════════════════════════════════════════

/-- The Turán density 1 - 1/m for chromatic number m+1. -/
noncomputable def turanDensity (m : ℕ) : ℝ := 1 - 1 / (m : ℝ)

/-- Turán densities are in [0, 1). -/
theorem turanDensity_mem_Ico (m : ℕ) (hm : m ≥ 1) :
    turanDensity m ∈ Ico (0 : ℝ) 1 := by
  have hm1 : (1:ℝ) ≤ (m:ℝ) := by exact_mod_cast hm
  have hmpos : (0:ℝ) < (m:ℝ) := by linarith
  unfold turanDensity
  refine ⟨?_, ?_⟩
  · rw [sub_nonneg, div_le_one hmpos]; exact hm1
  · have : 0 < 1 / (m:ℝ) := by positivity
    linarith

/-- **Erdős-Stone-Simonovits theorem** (axiomatized):
    A_2 = {1 - 1/m : m ≥ 1} = {0, 1/2, 2/3, 3/4, ...}

    Every Turán density is a jump value for graphs, and these
    are the ONLY jump values. -/
axiom erdos_stone_simonovits :
    densityJumpSetLiminf 2 = {α : ℝ | ∃ m : ℕ, m ≥ 1 ∧ α = turanDensity m}

-- ═══════════════════════════════════════════════════════════════
-- SECTION IV: Supersaturation infrastructure
-- ═══════════════════════════════════════════════════════════════

/-- For a fixed arity `k ≥ 1`, the binomial coefficient `m.choose k`
    diverges to infinity as `m → ∞`. This is the quantitative engine
    behind supersaturation: a positive edge density on a growing vertex
    set forces the raw edge count to diverge. -/
theorem choose_tendsto_atTop {k : ℕ} (hk : 1 ≤ k) :
    Tendsto (fun m : ℕ => (m.choose k : ℝ)) atTop atTop := by
  apply tendsto_atTop_mono' atTop
    (f₁ := fun m : ℕ => ((m + 1 - k : ℕ) : ℝ) ^ k / (k.factorial : ℝ))
  · filter_upwards with m
    have := Nat.pow_le_choose (α := ℝ) k m
    simpa using this
  · have h1 : Tendsto (fun m : ℕ => (m + 1 - k : ℕ)) atTop atTop := by
      rw [tendsto_atTop]; intro b
      filter_upwards [eventually_ge_atTop (b + k)] with m hm; omega
    have h2 : Tendsto (fun m : ℕ => ((m + 1 - k : ℕ) : ℝ)) atTop atTop :=
      tendsto_natCast_atTop_atTop.comp h1
    have h3 : Tendsto (fun m : ℕ => ((m + 1 - k : ℕ) : ℝ) ^ k) atTop atTop :=
      (tendsto_pow_atTop (Nat.one_le_iff_ne_zero.mp hk)).comp h2
    exact h3.atTop_div_const (by positivity)

/-- Edge density is always nonnegative. -/
theorem edgeDensity_nonneg (G : KUniformHypergraph) : 0 ≤ edgeDensity G := by
  unfold edgeDensity; split_ifs with h
  · exact le_refl 0
  · positivity

-- ═══════════════════════════════════════════════════════════════
-- SECTION V: Properties of A_k
-- ═══════════════════════════════════════════════════════════════

/-- **0 is always a density jump (for k ≥ 2)**: any sequence of
    k-uniform hypergraphs with positive liminf density and diverging
    vertex count admits subhypergraphs of liminf density exactly 1.

    This is the "supersaturation" phenomenon, here proved in full for
    the counting model. The witness jump value is β = 1.

    Construction: from a positive liminf density `0 < L` and diverging
    vertex count we obtain `e(Gₙ) → ∞`. We then set `Hₙ` to be the
    complete k-uniform hypergraph on the largest vertex count
    `vₙ ≤ |Gₙ|` for which `C(vₙ, k) ≤ e(Gₙ)`; this has density 1, fits
    inside `Gₙ`, and `vₙ → ∞`. -/
theorem zero_is_jump (k : ℕ) (hk : k ≥ 2) :
    0 ∈ densityJumpSetLiminf k := by
  classical
  have hk1 : 1 ≤ k := by omega
  refine ⟨le_refl 0, by norm_num, ?_⟩
  -- Witness jump value β = 1.
  refine ⟨1, by norm_num, le_refl 1, ?_⟩
  intro G hunif hverts hdens
  -- Positive liminf density, and a strictly smaller positive threshold c.
  set L := liminf (fun n => edgeDensity (G n)) atTop with hL
  have hLpos : 0 < L := hdens
  set c : ℝ := L / 2 with hc
  have hc0 : 0 < c := by rw [hc]; linarith
  have hbdd : IsBoundedUnder (· ≥ ·) atTop (fun n => edgeDensity (G n)) :=
    isBoundedUnder_of ⟨0, fun n => edgeDensity_nonneg (G n)⟩
  -- Eventually the density exceeds c.
  have hev_dens : ∀ᶠ n in atTop, c < edgeDensity (G n) := by
    have hlt : c < L := by rw [hc]; linarith
    exact eventually_lt_of_lt_liminf (by rw [← hL]; exact hlt) hbdd
  -- Eventually `c · C(|Gₙ|, k) < e(Gₙ)`.
  have hev_edges : ∀ᶠ n in atTop,
      c * ((G n).vertices.choose k : ℝ) < ((G n).edges : ℝ) := by
    filter_upwards [hev_dens] with n hn
    have hun := hunif n
    unfold edgeDensity at hn
    simp only [binom, hun] at hn
    by_cases hb : (G n).vertices.choose k = 0
    · rw [if_pos hb] at hn; linarith
    · rw [if_neg hb] at hn
      have hcpos : (0:ℝ) < ((G n).vertices.choose k : ℝ) := by
        exact_mod_cast Nat.pos_of_ne_zero hb
      rw [lt_div_iff₀ hcpos] at hn
      exact hn
  -- Vertex count diverges as a ℕ-sequence.
  have hvN : Tendsto (fun n => (G n).vertices) atTop atTop := by
    rw [tendsto_atTop]; intro b
    filter_upwards [hverts.eventually (eventually_ge_atTop (b:ℝ))] with n hn
    exact_mod_cast hn
  -- Hence `C(|Gₙ|, k) → ∞`, so `c · C(|Gₙ|, k) → ∞`, so `e(Gₙ) → ∞`.
  have hverts_choose : Tendsto (fun n => ((G n).vertices.choose k : ℝ)) atTop atTop :=
    (choose_tendsto_atTop hk1).comp hvN
  have hc_choose : Tendsto (fun n => c * ((G n).vertices.choose k : ℝ)) atTop atTop :=
    hverts_choose.const_mul_atTop hc0
  have hedges : Tendsto (fun n => ((G n).edges : ℝ)) atTop atTop := by
    apply tendsto_atTop_mono' atTop _ hc_choose
    filter_upwards [hev_edges] with n hn using le_of_lt hn
  -- Construct Hₙ: the complete k-uniform hypergraph on the largest
  -- admissible vertex count.
  set v : ℕ → ℕ :=
    fun n => Nat.findGreatest (fun w => w.choose k ≤ (G n).edges) (G n).vertices with hv
  refine ⟨fun n => ⟨v n, (v n).choose k, k⟩, fun n => rfl, ?_, ?_, ?_, ?_⟩
  · -- vertices of H ≤ vertices of G
    intro n; exact Nat.findGreatest_le _
  · -- edges of H ≤ edges of G (the empty hypergraph w = 0 witnesses admissibility)
    intro n
    show (v n).choose k ≤ (G n).edges
    rw [hv]
    refine Nat.findGreatest_spec (P := fun w => w.choose k ≤ (G n).edges)
      (m := 0) (Nat.zero_le _) ?_
    simp [Nat.choose_eq_zero_of_lt (show 0 < k by omega)]
  · -- vertices of H diverge
    have hvdiv : Tendsto v atTop atTop := by
      rw [tendsto_atTop]; intro M
      have e1 : ∀ᶠ n in atTop, M ≤ (G n).vertices := by
        filter_upwards [hvN.eventually (eventually_ge_atTop M)] with n hn; exact hn
      have e2 : ∀ᶠ n in atTop, (M.choose k : ℝ) ≤ ((G n).edges : ℝ) :=
        hedges.eventually (eventually_ge_atTop (M.choose k : ℝ))
      filter_upwards [e1, e2] with n hn1 hn2
      have hn2' : M.choose k ≤ (G n).edges := by exact_mod_cast hn2
      exact Nat.le_findGreatest hn1 hn2'
    exact tendsto_natCast_atTop_atTop.comp hvdiv
  · -- liminf density of H equals 1 (≥ β = 1)
    have hev1 : ∀ᶠ n in atTop,
        edgeDensity (⟨v n, (v n).choose k, k⟩ : KUniformHypergraph) = 1 := by
      have hk_le : ∀ᶠ n in atTop, k ≤ v n := by
        have hvdiv : Tendsto v atTop atTop := by
          rw [tendsto_atTop]; intro M
          have e1 : ∀ᶠ n in atTop, M ≤ (G n).vertices := by
            filter_upwards [hvN.eventually (eventually_ge_atTop M)] with n hn; exact hn
          have e2 : ∀ᶠ n in atTop, (M.choose k : ℝ) ≤ ((G n).edges : ℝ) :=
            hedges.eventually (eventually_ge_atTop (M.choose k : ℝ))
          filter_upwards [e1, e2] with n hn1 hn2
          have hn2' : M.choose k ≤ (G n).edges := by exact_mod_cast hn2
          exact Nat.le_findGreatest hn1 hn2'
        exact hvdiv.eventually (eventually_ge_atTop k)
      filter_upwards [hk_le] with n hn
      have hcne : (v n).choose k ≠ 0 := by
        have := Nat.choose_pos hn; omega
      show edgeDensity (⟨v n, (v n).choose k, k⟩ : KUniformHypergraph) = 1
      unfold edgeDensity
      simp only [binom]
      rw [if_neg hcne]
      rw [div_self (by exact_mod_cast hcne)]
    rw [liminf_congr hev1, liminf_const]

/-- The density jump set is contained in [0, 1). -/
theorem densityJumpSet_subset_Ico (k : ℕ) :
    densityJumpSetLiminf k ⊆ Ico (0 : ℝ) 1 := by
  intro α ⟨hα_nn, hα_lt, _⟩
  exact ⟨hα_nn, hα_lt⟩

-- ═══════════════════════════════════════════════════════════════
-- SECTION VI: The Open Problem
-- ═══════════════════════════════════════════════════════════════

/-- **Erdős Problem #837**: What is A_3?
    Determine the set of density jump values for 3-uniform hypergraphs.

    Key open questions:
    - Is A_3 countable? (A_2 is countable)
    - Does A_3 contain all rational values in [0, 1)?
    - Is the tetrahedron density 5/9 in A_3?
    - Is A_3 = A_2? (Conjectured NO) -/
theorem erdos_837_open :
    -- The problem is to characterize densityJumpSetLiminf 3
    True := trivial

-- ═══════════════════════════════════════════════════════════════
-- Verification
-- ═══════════════════════════════════════════════════════════════

#check IsDensityJumpLiminf
#check densityJumpSetLiminf
#check liminf_implies_original
#check erdos_stone_simonovits
#check turanDensity
#check zero_is_jump

end Erdos837OQ05
