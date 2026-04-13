import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic

/-
  Erdős #1022 OQ-03: Lovász Local Lemma for Property B

  The Lovász Local Lemma (LLL) provides a stronger guarantee for
  Property B than the first-moment (union) bound proved in
  Erdős1022Problem.lean.

  **First-moment bound**: |F| < 2^{t-1} and all sets have size ≥ t → Property B.
  **LLL bound**: max intersection degree d with monoProb(t) ≤ T(d) → Property B.

  The LLL condition depends on local dependency structure, not the
  absolute family size. A family with 2^{100} sets can satisfy the
  LLL condition if each set intersects few others.

  Part I: Intersection dependency graph for set families (0 sorries)
  Part II: Element frequency bounds intersection degree (0 sorries)
  Part III: LLL threshold and monochromaticity probability (0 sorries)
  Part IV: LLL → Property B bridge (1 axiom: probabilistic step)
  Part V: Concrete examples and comparison (0 sorries)

  References:
  - Erdős & Lovász, "Problems and results on 3-chromatic hypergraphs" (1975)
  - Spencer, "Ten Lectures on the Probabilistic Method" (1994)
  - Alon & Spencer, "The Probabilistic Method" (2015), Chapter 5
-/

open Finset

namespace Erdos1022OQ03

variable {α : Type*} [DecidableEq α]

-- ══════════════════════════════════════════════════════════════════
-- § 1: Property B and Size Conditions (from Erdős 1022)
-- ══════════════════════════════════════════════════════════════════

/-- Property B: ∃ 2-coloring with no monochromatic set. -/
def HasPropertyB [Fintype α] (F : Finset (Finset α)) : Prop :=
  ∃ S : Finset α, ∀ f ∈ F, (f ∩ S).Nonempty ∧ (f \ S).Nonempty

/-- All sets in F have cardinality ≥ t. -/
def AllSizeAtLeast (F : Finset (Finset α)) (t : ℕ) : Prop :=
  ∀ f ∈ F, t ≤ f.card

-- ══════════════════════════════════════════════════════════════════
-- § 2: Intersection Dependency Graph
-- ══════════════════════════════════════════════════════════════════

/-- The intersection neighbors of set f in family F:
    all other members sharing at least one element with f.

    In the LLL framework, two "bad events" (set i monochromatic,
    set j monochromatic) are dependent iff the underlying sets
    share elements, because element colorings are independent. -/
def intNeighbors (F : Finset (Finset α)) (f : Finset α) : Finset (Finset α) :=
  (F.erase f).filter (fun g => 0 < (f ∩ g).card)

/-- Intersection degree: number of other members sharing elements with f. -/
def intDegree (F : Finset (Finset α)) (f : Finset α) : ℕ :=
  (intNeighbors F f).card

/-- Bounded intersection degree: every member intersects ≤ d others. -/
def HasBoundedIntDeg (F : Finset (Finset α)) (d : ℕ) : Prop :=
  ∀ f ∈ F, intDegree F f ≤ d

/-- Disjoint sets are not intersection neighbors. -/
theorem not_mem_intNeighbors_of_disjoint
    (F : Finset (Finset α)) (f g : Finset α)
    (hdisj : Disjoint f g) : g ∉ intNeighbors F f := by
  simp only [intNeighbors, mem_filter, not_and, mem_erase]
  intro _
  rw [Finset.disjoint_iff_inter_eq_empty.mp hdisj, card_empty]
  omega

/-- Intersection neighbors are members of F. -/
theorem intNeighbors_subset_family
    (F : Finset (Finset α)) (f : Finset α) :
    intNeighbors F f ⊆ F := by
  intro g hg
  simp only [intNeighbors, mem_filter, mem_erase] at hg
  exact hg.1.2

/-- Intersection degree is at most |F| - 1. -/
theorem intDegree_le_card_sub_one
    (F : Finset (Finset α)) (f : Finset α) (hf : f ∈ F) :
    intDegree F f ≤ F.card - 1 := by
  unfold intDegree intNeighbors
  calc (filter (fun g => 0 < (f ∩ g).card) (F.erase f)).card
      ≤ (F.erase f).card := card_filter_le _ _
    _ = F.card - 1 := card_erase_of_mem hf

-- ══════════════════════════════════════════════════════════════════
-- § 3: Element Frequency Bounds Intersection Degree
-- ══════════════════════════════════════════════════════════════════

/-- Element degree: number of members of F containing element a. -/
def elemDegree (F : Finset (Finset α)) (a : α) : ℕ :=
  (F.filter (a ∈ ·)).card

/-- **Key Combinatorial Lemma**: Element frequency bounds intersection degree.

    If every element appears in ≤ Δ members of F and f ∈ F, then f
    shares elements with at most |f| · (Δ - 1) other members.

    Proof idea: Each x ∈ f appears in ≤ Δ members total, so in ≤ Δ-1
    members besides f. Group neighbors by their shared element; each
    neighbor appears in at least one group. The total group sizes sum
    to at most |f| · (Δ - 1).

    This is useful because the LLL condition involves max INTERSECTION
    degree, which is bounded by |f| · (max ELEMENT degree - 1). -/
theorem intDegree_le_card_mul
    (F : Finset (Finset α)) (f : Finset α) (hf : f ∈ F) (Δ : ℕ)
    (hΔ1 : 1 ≤ Δ)
    (hΔ : ∀ a : α, elemDegree F a ≤ Δ) :
    intDegree F f ≤ f.card * (Δ - 1) := by
  unfold intDegree
  -- Step 1: Each neighbor shares some element with f, so neighbors ⊆ ⋃_{x ∈ f} ...
  have hsub : intNeighbors F f ⊆
      f.biUnion (fun x => (F.filter (x ∈ ·)).erase f) := by
    intro g hg
    simp only [intNeighbors, mem_filter, mem_erase] at hg
    obtain ⟨⟨hgne, hgF⟩, hcard⟩ := hg
    obtain ⟨x, hx⟩ := card_pos.mp hcard
    rw [mem_inter] at hx
    rw [mem_biUnion]
    exact ⟨x, hx.1, mem_erase.mpr ⟨hgne, mem_filter.mpr ⟨hgF, hx.2⟩⟩⟩
  -- Step 2: Bound by sum of per-element contributions
  calc (intNeighbors F f).card
      ≤ (f.biUnion (fun x => (F.filter (x ∈ ·)).erase f)).card :=
        card_le_card hsub
    _ ≤ f.sum (fun x => ((F.filter (x ∈ ·)).erase f).card) :=
        card_biUnion_le
    -- Step 3: Each element contributes ≤ Δ - 1 neighbors
    _ ≤ f.sum (fun _ => Δ - 1) := by
        apply Finset.sum_le_sum; intro x hx
        have hfmem : f ∈ F.filter (x ∈ ·) := mem_filter.mpr ⟨hf, hx⟩
        rw [card_erase_of_mem hfmem]
        exact Nat.sub_le_sub_right (hΔ x) 1
    -- Step 4: Sum of constant = |f| · (Δ - 1)
    _ = f.card * (Δ - 1) := by simp [Finset.sum_const, smul_eq_mul]

-- ══════════════════════════════════════════════════════════════════
-- § 4: LLL Threshold and Monochromaticity Probability
-- ══════════════════════════════════════════════════════════════════

/-- The LLL threshold T(d) = d^d / (d+1)^{d+1}.
    Maximum event probability the symmetric LLL can handle at degree d.
    Self-contained definition; see also LovaszLocalLemma.lean Part VII. -/
noncomputable def lllThreshold (d : ℕ) : ℚ :=
  if d = 0 then 1 else (↑d : ℚ) ^ d / (↑d + 1) ^ (d + 1)

/-- Monochromaticity probability under uniform random 2-coloring:
    a set of size s is monochromatic with probability 2 · (1/2)^s = 2/2^s.
    For sets of size ≥ t, this is at most monoProb t. -/
def monoProb (t : ℕ) : ℚ := 2 / 2 ^ t

/-- T(1) = 1/4. -/
theorem lllThreshold_one : lllThreshold 1 = 1 / 4 := by
  simp [lllThreshold]; norm_num

/-- T(3) = 27/256. -/
theorem lllThreshold_three : lllThreshold 3 = 27 / 256 := by
  simp [lllThreshold]; norm_num

/-- monoProb(3) = 1/4. -/
theorem monoProb_three : monoProb 3 = 1 / 4 := by
  simp [monoProb]; norm_num

/-- monoProb(5) = 1/16. -/
theorem monoProb_five : monoProb 5 = 1 / 16 := by
  simp [monoProb]; norm_num

/-- monoProb(8) = 1/128. -/
theorem monoProb_eight : monoProb 8 = 1 / 128 := by
  simp [monoProb]; norm_num

/-- monoProb is positive for all t. -/
theorem monoProb_pos (t : ℕ) : 0 < monoProb t := by
  unfold monoProb
  apply div_pos (by norm_num : (0 : ℚ) < 2) (by positivity)

/-- monoProb decreases with t (larger sets are less likely monochromatic). -/
theorem monoProb_anti {s t : ℕ} (hst : s ≤ t) : monoProb t ≤ monoProb s := by
  simp only [monoProb]
  have hs_pos : (0 : ℚ) < 2 ^ s := by positivity
  have ht_pos : (0 : ℚ) < 2 ^ t := by positivity
  rw [div_le_div_iff ht_pos hs_pos]
  have : (2 : ℚ) ^ s ≤ 2 ^ t := by
    exact_mod_cast Nat.pow_le_pow_right (by norm_num : 1 ≤ 2) hst
  linarith

-- ══════════════════════════════════════════════════════════════════
-- § 5: LLL Condition Satisfied for Property B
-- ══════════════════════════════════════════════════════════════════

/-- **LLL condition for t=3, d=1**: monoProb(3) ≤ T(1).
    For 3-uniform hypergraphs with max intersection degree 1
    (matching structure), the LLL condition is satisfied with equality. -/
theorem lll_condition_t3_d1 : monoProb 3 ≤ lllThreshold 1 := by
  rw [monoProb_three, lllThreshold_one]

/-- **LLL condition for t=5, d=3**: monoProb(5) ≤ T(3).
    For sets of size ≥ 5 with max intersection degree ≤ 3,
    the LLL guarantees Property B — regardless of family size.
    Compare: first-moment requires |F| < 2^4 = 16. -/
theorem lll_condition_t5_d3 : monoProb 5 ≤ lllThreshold 3 := by
  rw [monoProb_five, lllThreshold_three]; norm_num

/-- **LLL condition for t=8, d=10**: monoProb(8) ≤ T(10).
    For sets of size ≥ 8, up to 10 pairwise intersections allowed.
    First-moment would require |F| < 2^7 = 128. -/
theorem lll_condition_t8_d10 : monoProb 8 ≤ lllThreshold 10 := by
  simp [monoProb, lllThreshold]; norm_num

-- ══════════════════════════════════════════════════════════════════
-- § 6: LLL → Property B Bridge
-- ══════════════════════════════════════════════════════════════════

/-- **Lovász Local Lemma for Property B**: If every set has size ≥ t,
    the intersection dependency graph has max degree ≤ d, and the
    monochromaticity probability satisfies the LLL threshold,
    then Property B holds.

    Proof sketch: Consider uniform random 2-coloring χ : α → Bool.
    For each set Aᵢ ∈ F, let Bᵢ = "Aᵢ is monochromatic under χ".
    • P(Bᵢ) = 2 · 2^{-|Aᵢ|} ≤ monoProb(t)
    • Bᵢ, Bⱼ are mutually independent when Aᵢ ∩ Aⱼ = ∅
    • The intersection graph is the dependency graph
    • monoProb(t) ≤ T(d) satisfies the symmetric LLL condition
    • LLL ⟹ P(∩ B̄ᵢ) ≥ ∏(1 - 1/(d+1)) > 0
    • Therefore ∃ χ avoiding all Bᵢ, i.e., Property B holds.

    The algebraic core of the LLL is proved in LovaszLocalLemma.lean.
    This axiom captures the probability-space construction step,
    connecting the algebraic bound to the combinatorial conclusion.
    When finite probability space infrastructure matures in Mathlib,
    this can be proved similarly to erdos_first_moment_bound in
    Erdos1022Problem.lean but with the LLL replacing the union bound. -/
axiom lll_propertyB [Fintype α] (F : Finset (Finset α)) (t d : ℕ)
    (ht : 2 ≤ t) (hsize : AllSizeAtLeast F t)
    (hdeg : HasBoundedIntDeg F d)
    (hlll : monoProb t ≤ lllThreshold d) :
    HasPropertyB F

-- ══════════════════════════════════════════════════════════════════
-- § 7: Applications and Comparison with First-Moment
-- ══════════════════════════════════════════════════════════════════

/-- The first-moment bound at t = 5 allows at most 15 sets. -/
theorem first_moment_threshold_t5 : 2 ^ (5 - 1) = (16 : ℕ) := by norm_num

/-- The LLL at t = 5, d = 3 allows ARBITRARILY MANY sets, as long as
    each intersects ≤ 3 others. This is the fundamental improvement:
    the LLL decouples family size from the Property B guarantee.

    Example: Take 10000 sets of size 5 on a ground set of 50000 elements,
    arranged so each set shares elements with ≤ 3 others (e.g., by
    distributing elements sparsely). The LLL gives Property B; the
    first-moment bound is useless since 10000 ≥ 16. -/
theorem lll_propertyB_t5_d3 [Fintype α] (F : Finset (Finset α))
    (hsize : AllSizeAtLeast F 5) (hdeg : HasBoundedIntDeg F 3) :
    HasPropertyB F :=
  lll_propertyB F 5 3 (by norm_num) hsize hdeg lll_condition_t5_d3

/-- Combined bound: element frequency → LLL → Property B.

    If every element appears in ≤ Δ sets, sets have size ≥ t,
    and |f| · (Δ - 1) ≤ d with monoProb(t) ≤ T(d), then Property B.

    This gives a concrete recipe: control element frequency to ensure
    the intersection degree condition, then apply the LLL.

    For t = 5 and uniform 5-element sets: need 5·(Δ-1) ≤ 3,
    so Δ ≤ 1 (each element in at most 1 set — a matching).
    For t = 8 and 8-element sets: need 8·(Δ-1) ≤ 10,
    so Δ ≤ 2 (each element in at most 2 sets). -/
theorem lll_via_frequency [Fintype α] (F : Finset (Finset α)) (t d Δ : ℕ)
    (ht : 2 ≤ t) (hΔ1 : 1 ≤ Δ)
    (hsize : AllSizeAtLeast F t)
    (hsizeup : ∀ f ∈ F, f.card ≤ t)  -- uniform t-sets
    (hfreq : ∀ a : α, elemDegree F a ≤ Δ)
    (hdeg_bound : t * (Δ - 1) ≤ d)
    (hlll : monoProb t ≤ lllThreshold d) :
    HasPropertyB F := by
  apply lll_propertyB F t d ht hsize _ hlll
  intro f hf
  calc intDegree F f
      ≤ f.card * (Δ - 1) := intDegree_le_card_mul F f hf Δ hΔ1 hfreq
    _ ≤ t * (Δ - 1) := Nat.mul_le_mul_right _ (hsizeup f hf)
    _ ≤ d := hdeg_bound

-- ══════════════════════════════════════════════════════════════════
-- § 8: Structure of the Improvement
-- ══════════════════════════════════════════════════════════════════

/-- The LLL threshold T(d) is positive for d ≥ 1. -/
theorem lllThreshold_pos (d : ℕ) (hd : 1 ≤ d) : 0 < lllThreshold d := by
  simp only [lllThreshold, if_neg (by omega : d ≠ 0)]
  apply div_pos
  · exact pow_pos (Nat.cast_pos.mpr (by omega)) d
  · exact pow_pos (by positivity : (0 : ℚ) < ↑d + 1) (d + 1)

/-- For any t ≥ 2, monoProb(t) ≤ 1/2, showing that the probability
    is in the range where the LLL can potentially help. -/
theorem monoProb_le_half (t : ℕ) (ht : 2 ≤ t) : monoProb t ≤ 1 / 2 := by
  simp only [monoProb]
  rw [div_le_div_iff (by positivity : (0 : ℚ) < 2 ^ t) (by norm_num : (0 : ℚ) < 2)]
  have h2t : (4 : ℚ) ≤ 2 ^ t := by
    calc (4 : ℚ) = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ t := by
        exact_mod_cast Nat.pow_le_pow_right (by norm_num : 1 ≤ 2) ht
  linarith

/-- The empty family trivially has Property B (no sets to violate). -/
theorem hasPropertyB_empty [Fintype α] :
    HasPropertyB (∅ : Finset (Finset α)) :=
  ⟨∅, fun _ hf => absurd hf (not_mem_empty _)⟩

/-- Any family with all sets having size ≥ 2 and intersection degree 0
    (all sets pairwise disjoint) has Property B. Each set can be
    independently split. This is the d=0 base case. -/
theorem propertyB_of_disjoint [Fintype α] (F : Finset (Finset α))
    (hsize : AllSizeAtLeast F 2)
    (hdisj : HasBoundedIntDeg F 0) :
    HasPropertyB F := by
  -- With intersection degree 0, every pair of sets is disjoint.
  -- Use induction on F.
  induction F using Finset.induction_on with
  | empty => exact hasPropertyB_empty
  | @insert f₀ F' hna ih =>
    -- Transfer hypotheses
    have hF'_size : AllSizeAtLeast F' 2 :=
      fun f hf => hsize f (mem_insert_of_mem hf)
    have hF'_disj : HasBoundedIntDeg F' 0 := by
      intro f hf
      have hsub : intNeighbors F' f ⊆ intNeighbors (insert f₀ F') f := by
        intro g hg
        simp only [intNeighbors, mem_filter, mem_erase] at hg ⊢
        exact ⟨⟨hg.1.1, mem_insert_of_mem hg.1.2⟩, hg.2⟩
      calc intDegree F' f = (intNeighbors F' f).card := rfl
        _ ≤ (intNeighbors (insert f₀ F') f).card := card_le_card hsub
        _ = intDegree (insert f₀ F') f := rfl
        _ ≤ 0 := hdisj f (mem_insert_of_mem hf)
    obtain ⟨S', hS'⟩ := ih hF'_size hF'_disj
    -- f₀ has size ≥ 2, pick two elements
    have hf₀_card : 2 ≤ f₀.card := hsize f₀ (mem_insert_self f₀ F')
    have hne : f₀.Nonempty := card_pos.mp (by omega)
    obtain ⟨a, ha⟩ := hne
    have hera_ne : (f₀.erase a).Nonempty := by
      rw [Finset.nonempty_iff_ne_empty]; intro h
      have := card_erase_of_mem ha; rw [h, card_empty] at this; omega
    obtain ⟨b, hb_era⟩ := hera_ne
    have hb : b ∈ f₀ := mem_of_mem_erase hb_era
    have hba : b ≠ a := ne_of_mem_erase hb_era
    -- f₀ is disjoint from all of F' (degree 0)
    have hf₀_disj : ∀ g ∈ F', Disjoint f₀ g := by
      intro g hg
      rw [Finset.disjoint_iff_inter_eq_empty]
      by_contra hint
      -- If f₀ ∩ g ≠ ∅, then g is an intersection neighbor of f₀
      have : g ∈ intNeighbors (insert f₀ F') f₀ := by
        simp only [intNeighbors, mem_filter, mem_erase]
        refine ⟨⟨fun h => hna (h ▸ hg), mem_insert_of_mem hg⟩, ?_⟩
        exact Nat.pos_of_ne_zero (fun h => hint (card_eq_zero.mp h))
      have : 1 ≤ intDegree (insert f₀ F') f₀ :=
        Nat.one_le_iff_ne_zero.mpr (fun h =>
          not_mem_empty g (h ▸ this : g ∈ intNeighbors (insert f₀ F') f₀))
      linarith [hdisj f₀ (mem_insert_self f₀ F')]
    -- Since f₀ is disjoint from F', elements of f₀ don't appear in F' sets
    -- So modifying S' on f₀ doesn't affect F' coloring
    by_cases h_inter : (f₀ ∩ S').Nonempty
    · by_cases h_diff : (f₀ \ S').Nonempty
      · exact ⟨S', fun f hf => by
          rcases mem_insert.mp hf with rfl | hf
          · exact ⟨h_inter, h_diff⟩
          · exact hS' f hf⟩
      · -- f₀ ⊆ S': remove a from S'
        have hf₀_sub : ∀ x ∈ f₀, x ∈ S' := by
          intro x hx; by_contra hxn
          exact h_diff ⟨x, mem_sdiff.mpr ⟨hx, hxn⟩⟩
        refine ⟨S'.erase a, fun f hf => ?_⟩
        rcases mem_insert.mp hf with rfl | hf
        · exact ⟨⟨b, mem_inter.mpr ⟨hb, mem_erase.mpr ⟨hba, hf₀_sub b hb⟩⟩⟩,
                 ⟨a, mem_sdiff.mpr ⟨ha, not_mem_erase a S'⟩⟩⟩
        · have ha_not : a ∉ f := Finset.disjoint_left.mp (hf₀_disj f hf) ha
          constructor
          · obtain ⟨c, hc⟩ := (hS' f hf).1
            rw [mem_inter] at hc
            exact ⟨c, mem_inter.mpr ⟨hc.1, mem_erase.mpr
              ⟨fun hca => ha_not (hca ▸ hc.1), hc.2⟩⟩⟩
          · obtain ⟨c, hc⟩ := (hS' f hf).2
            rw [mem_sdiff] at hc
            exact ⟨c, mem_sdiff.mpr ⟨hc.1, fun h =>
              hc.2 (erase_subset a S' h)⟩⟩
    · -- f₀ ∩ S' = ∅: add a to S'
      have hf₀_disj_S : ∀ x ∈ f₀, x ∉ S' := by
        intro x hx hxS; exact h_inter ⟨x, mem_inter.mpr ⟨hx, hxS⟩⟩
      refine ⟨insert a S', fun f hf => ?_⟩
      rcases mem_insert.mp hf with rfl | hf
      · exact ⟨⟨a, mem_inter.mpr ⟨ha, mem_insert_self a S'⟩⟩,
               ⟨b, mem_sdiff.mpr ⟨hb, fun h =>
                (mem_insert.mp h).elim (fun heq => hba heq)
                  (hf₀_disj_S b hb)⟩⟩⟩
      · have ha_not : a ∉ f := Finset.disjoint_left.mp (hf₀_disj f hf) ha
        constructor
        · obtain ⟨c, hc⟩ := (hS' f hf).1
          rw [mem_inter] at hc
          exact ⟨c, mem_inter.mpr ⟨hc.1, mem_insert_of_mem hc.2⟩⟩
        · obtain ⟨c, hc⟩ := (hS' f hf).2
          rw [mem_sdiff] at hc
          exact ⟨c, mem_sdiff.mpr ⟨hc.1, fun h =>
            hc.2 ((mem_insert.mp h).elim (fun hca => absurd (hca ▸ hc.1) ha_not) id)⟩⟩

end Erdos1022OQ03
