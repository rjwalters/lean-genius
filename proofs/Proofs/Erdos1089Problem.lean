/-
  Erdős Problem #1089: Distinct Distances in Higher Dimensions

  Source: https://erdosproblems.com/1089
  Status: OPEN

  Statement:
  Let g_d(n) be minimal such that every collection of g_d(n) points in ℝ^d
  determines at least n distinct distances. Estimate g_d(n). In particular,
  does lim_{d→∞} g_d(n)/d^{n-1} exist?

  Background:
  This is the higher-dimensional generalization of the distinct distances
  problem. In ℝ^d, we ask: how many points guarantee n distinct pairwise
  distances? The function g_d(n) captures this threshold.

  Known results:
  • g_1(3) = 4 (4 points on a line give 3 distances)
  • g_2(3) = 6 (6 points in plane guarantee 3 distinct distances)
  • g_3(3) = 7 (Croft 1962)
  • Lower bound: g_d(n) ≫ d^{n-1} (Erdős, "easy")
  • Upper bound: g_d(n) ≤ c^{d^{1-b_n}} for some constants (Erdős-Straus)
  • Cube bound: g_d(d+1) > 2^d (vertices of d-cube have ≤ d distances)

  The main question: does g_d(n)/d^{n-1} converge as d → ∞?

  References:
  [Er75f] Erdős, "Problems and results in combinatorial geometry" (1975)
  [Cr62] Croft, "On a claim of Erdős" (1962)

  Tags: discrete-geometry, distinct-distances, high-dimensions, open-problem
-/

import Mathlib

open Set Finset

/-
## Points and Distances

Points in d-dimensional Euclidean space and their pairwise distances.
-/

/-- A point in d-dimensional Euclidean space -/
abbrev Point (d : ℕ) := EuclideanSpace ℝ (Fin d)

/-- Euclidean distance between two points -/
noncomputable def eucDist {d : ℕ} (p q : Point d) : ℝ :=
  ‖p - q‖

/-- The set of distinct distances determined by a point set -/
noncomputable def distinctDistances {d : ℕ} (P : Finset (Point d)) : Finset ℝ :=
  (P.product P).image (fun (p, q) => eucDist p q) |>.filter (· > 0)

/-- Number of distinct distances -/
noncomputable def numDistinctDistances {d : ℕ} (P : Finset (Point d)) : ℕ :=
  (distinctDistances P).card

/-
## The Function g_d(n)

g_d(n) is the minimal number of points guaranteeing n distinct distances.
-/

/-- A point set determines at least n distinct distances -/
def determinesNDistances {d : ℕ} (P : Finset (Point d)) (n : ℕ) : Prop :=
  numDistinctDistances P ≥ n

/-- g_d(n): minimal m such that every m-point set determines ≥ n distances -/
noncomputable def g (d n : ℕ) : ℕ :=
  sInf {m : ℕ | ∀ P : Finset (Point d), P.card = m → determinesNDistances P n}

/-- g is well-defined for n ≥ 1 -/
axiom g_well_defined :
  ∀ d n : ℕ, n ≥ 1 → ∃ m : ℕ, ∀ P : Finset (Point d), P.card = m → determinesNDistances P n

/-
## Small Cases

Known exact values of g_d(n).
-/

/-- g_1(3) = 4: four points on a line give 3 distinct distances -/
/-- g_2(3) = 6: six points in the plane guarantee 3 distinct distances -/
/-- g_3(3) = 7 (Croft 1962) -/
/-- Trivial: g_d(1) = 2 (any two distinct points give 1 distance) -/
theorem g_d_1 (d : ℕ) (hd : d ≥ 1) : g d 1 = 2 := by
  apply le_antisymm
  · -- g d 1 ≤ 2: every 2-element set has ≥ 1 positive distance
    apply Nat.sInf_le
    intro P hP
    obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.mp hP
    unfold determinesNDistances numDistinctDistances
    have hmem : eucDist a b ∈ distinctDistances ({a, b} : Finset (Point d)) := by
      unfold distinctDistances eucDist
      rw [Finset.mem_filter]
      refine ⟨Finset.mem_image.mpr ⟨(a, b), ?_, rfl⟩,
        norm_pos_iff.mpr (sub_ne_zero.mpr hab)⟩
      exact Finset.mk_mem_product (Finset.mem_insert_self a _)
        (Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton_self b)))
    exact Finset.card_pos.mpr ⟨_, hmem⟩
  · -- 2 ≤ g d 1: 0 and 1 are not in the threshold set
    obtain ⟨M, hM⟩ := g_well_defined d 1 (by omega)
    refine le_csInf ⟨M, ?_⟩ ?_
    · exact hM
    · intro m hm
      by_contra hlt
      push_neg at hlt
      interval_cases m
      · -- m = 0: empty set has 0 distances
        have := hm (∅ : Finset (Point d)) (by simp)
        simp [determinesNDistances, numDistinctDistances, distinctDistances] at this
      · -- m = 1: singleton {0} has 0 distances
        have := hm ({(0 : Point d)} : Finset _) (by simp)
        unfold determinesNDistances numDistinctDistances at this
        have hempty : distinctDistances ({(0 : Point d)} : Finset _) = ∅ := by
          rw [Finset.eq_empty_iff_forall_notMem]
          intro r hr
          unfold distinctDistances at hr
          rw [Finset.mem_filter] at hr
          obtain ⟨hr_mem, hr_pos⟩ := hr
          rw [Finset.mem_image] at hr_mem
          obtain ⟨⟨p, q⟩, hpq_mem, rfl⟩ := hr_mem
          have ⟨hp, hq⟩ := Finset.mem_product.mp hpq_mem
          simp only [Finset.mem_singleton] at hp hq
          subst hp; subst hq
          dsimp only at hr_pos
          simp [eucDist] at hr_pos
        rw [hempty, Finset.card_empty] at this
        omega

/-- NOTE: The previous axiom `g_d_2 : ∀ d ≥ 1, g d 2 = 3` was INCORRECT.
    In ℝ^d, d+1 points can be mutually equidistant (regular d-simplex), giving only 1
    distinct distance. So g_d(2) = d + 2, not 3. The correct values: g_1(2) = 3
    (on a line, 3 points always have ≥ 2 distinct distances since equidistant triples
    are impossible), but g_2(2) = 4 (equilateral triangle has 1 distance),
    g_3(2) = 5 (regular tetrahedron), and generally g_d(2) = d + 2.
    Removed as it was unused and mathematically incorrect. -/

/-
## Lower Bound

g_d(n) ≫ d^{n-1} via cube construction.
-/

/-- The vertices of the d-dimensional unit cube: all points with coordinates in {0, 1}.
    Constructed by mapping each function Fin d → Fin 2 to a point in ℝ^d. -/
noncomputable def cubeVertices (d : ℕ) : Finset (Point d) :=
  Finset.univ.image (fun (f : Fin d → Fin 2) =>
    (EuclideanSpace.equiv (Fin d) ℝ).symm (fun i => ((f i : ℕ) : ℝ)))

private lemma cubeVertices_injective (d : ℕ) :
    Function.Injective (fun (f : Fin d → Fin 2) =>
      (EuclideanSpace.equiv (Fin d) ℝ).symm (fun i => ((f i : ℕ) : ℝ))) := by
  intro f₁ f₂ hf
  have h : (fun i => ((f₁ i : ℕ) : ℝ)) = (fun i => ((f₂ i : ℕ) : ℝ)) :=
    (EuclideanSpace.equiv (Fin d) ℝ).symm.injective hf
  funext i
  have hi := congr_fun h i
  exact Fin.ext (Nat.cast_inj.mp hi)

/-- Cube has 2^d vertices -/
theorem cube_card (d : ℕ) : (cubeVertices d).card = 2 ^ d := by
  simp only [cubeVertices, Finset.card_image_of_injective _ (cubeVertices_injective d),
             Finset.card_univ, Fintype.card_fun, Fintype.card_fin]

/-- Cube vertices determine at most d distinct distances -/
axiom cube_distances :
  ∀ d : ℕ, numDistinctDistances (cubeVertices d) ≤ d

/-- Distinct distances are monotone under subset: P ⊆ Q → distances(P) ⊆ distances(Q) -/
private lemma distinctDistances_mono {d : ℕ} {P Q : Finset (Point d)} (h : P ⊆ Q) :
    distinctDistances P ⊆ distinctDistances Q := by
  intro r hr
  unfold distinctDistances at hr ⊢
  rw [Finset.mem_filter] at hr ⊢
  obtain ⟨hr_mem, hr_pos⟩ := hr
  refine ⟨?_, hr_pos⟩
  rw [Finset.mem_image] at hr_mem ⊢
  obtain ⟨⟨p, q⟩, hpq_mem, rfl⟩ := hr_mem
  refine ⟨(p, q), ?_, rfl⟩
  have ⟨hp, hq⟩ := Finset.mem_product.mp hpq_mem
  exact Finset.mk_mem_product (h hp) (h hq)

/-- Cube gives lower bound: g_d(d+1) > 2^d -/
theorem cube_lower_bound (d : ℕ) : g d (d + 1) > 2^d := by
  by_contra hle
  push_neg at hle
  obtain ⟨M, hM⟩ := g_well_defined d (d + 1) (by omega)
  have hne : Set.Nonempty {m : ℕ | ∀ P : Finset (Point d), P.card = m →
      determinesNDistances P (d + 1)} := ⟨M, hM⟩
  have hmem := Nat.sInf_mem hne
  have hsz : g d (d + 1) ≤ (cubeVertices d).card := by rw [cube_card]; exact hle
  obtain ⟨P, hPsub, hPcard⟩ := Finset.exists_subset_card_eq hsz
  have h_many := hmem P hPcard
  have h_few : numDistinctDistances P ≤ d :=
    le_trans (Finset.card_le_card (distinctDistances_mono hPsub)) (cube_distances d)
  unfold determinesNDistances at h_many
  omega

/-- General lower bound: g_d(n) ≥ c·d^{n-1} for some constant c -/
axiom erdos_lower_bound :
  ∀ n ≥ 2, ∃ c : ℝ, c > 0 ∧ ∀ d ≥ 1, (g d n : ℝ) ≥ c * d^(n - 1 : ℕ)

/-
## Upper Bound

Erdős-Straus upper bound.
-/

/-- Erdős-Straus bound: g_d(n) ≤ c^{d^{1-b_n}} -/
axiom erdos_straus_upper_bound :
  ∀ n ≥ 2, ∃ c b : ℝ, c > 1 ∧ b > 0 ∧
    ∀ d ≥ 1, (g d n : ℝ) ≤ c^(d^(1 - b) : ℝ)

/-
## The Main Conjecture

Does g_d(n)/d^{n-1} converge as d → ∞?
-/

/-- The normalized ratio g_d(n)/d^{n-1} -/
noncomputable def gRatio (d n : ℕ) : ℝ :=
  (g d n : ℝ) / d^(n - 1 : ℕ)

/-- Conjecture: the limit exists for each fixed n -/
def erdos1089Conjecture (n : ℕ) : Prop :=
  ∃ L : ℝ, Filter.Tendsto (fun d => gRatio d n) Filter.atTop (nhds L)

/-- Weaker: is the ratio bounded? -/
def ratioIsBounded (n : ℕ) : Prop :=
  ∃ C : ℝ, C > 0 ∧ ∀ d ≥ 1, gRatio d n ≤ C

/-- Lower bound implies ratio is bounded below -/
theorem ratio_bounded_below (n : ℕ) (hn : n ≥ 2) :
    ∃ c : ℝ, c > 0 ∧ ∀ d ≥ 1, gRatio d n ≥ c := by
  obtain ⟨c, hc, h⟩ := erdos_lower_bound n hn
  exact ⟨c, hc, fun d hd => by
    simp only [gRatio]
    rw [ge_iff_le, le_div_iff₀ (by positivity : (d : ℝ) ^ (n - 1) > 0)]
    linarith [h d hd]⟩

/-
## Monotonicity Properties

How g_d(n) changes with d and n.
-/

/-- g_d(n) is increasing in n.
    Proof: If every m-point set has ≥ n₂ distances, it has ≥ n₁ distances (for n₁ ≤ n₂).
    So the threshold set for n₂ is a subset of the threshold set for n₁,
    and sInf of the superset ≤ sInf of the subset. -/
theorem g_mono_n :
    ∀ d n₁ n₂ : ℕ, n₁ ≤ n₂ → g d n₁ ≤ g d n₂ := by
  intro d n₁ n₂ hn
  by_cases hn2 : n₂ = 0
  · have hn1 : n₁ = 0 := by omega
    subst hn1; subst hn2
    exact le_refl _
  · -- n₂ ≥ 1, so g_well_defined gives nonemptiness of the n₂ threshold set
    obtain ⟨m, hm⟩ := g_well_defined d n₂ (by omega)
    -- The threshold set for n₂ is nonempty
    have hne : Set.Nonempty {m : ℕ | ∀ P : Finset (Point d), P.card = m → determinesNDistances P n₂} :=
      ⟨m, hm⟩
    -- g d n₂ is in the n₂ threshold set (Nat.sInf_mem for nonempty sets)
    have hmem_n2 : ∀ P : Finset (Point d), P.card = g d n₂ → determinesNDistances P n₂ :=
      Nat.sInf_mem hne
    -- g d n₂ is also in the n₁ threshold set (since n₁ ≤ n₂)
    have hmem_n1 : g d n₂ ∈ {m : ℕ | ∀ P : Finset (Point d), P.card = m → determinesNDistances P n₁} :=
      fun P hP => le_trans hn (hmem_n2 P hP)
    -- sInf of n₁ set ≤ g d n₂ = sInf of n₂ set
    exact Nat.sInf_le hmem_n1

/-- Isometric embedding of ℝ^{d₁} into ℝ^{d₂} (pad with zeros).
    Preserves distances: ‖embed(p) - embed(q)‖ = ‖p - q‖. -/
private noncomputable def embedPoint {d₁ d₂ : ℕ} (hd : d₁ ≤ d₂)
    (p : Point d₁) : Point d₂ :=
  (EuclideanSpace.equiv (Fin d₂) ℝ).symm (fun j =>
    if hj : j.val < d₁ then
      (EuclideanSpace.equiv (Fin d₁) ℝ) p ⟨j.val, hj⟩
    else 0)

/-- embedPoint is injective -/
private lemma embedPoint_injective {d₁ d₂ : ℕ} (hd : d₁ ≤ d₂) :
    Function.Injective (embedPoint hd : Point d₁ → Point d₂) := by
  intro p q hpq
  have h := congr_arg (EuclideanSpace.equiv (Fin d₂) ℝ) hpq
  simp only [embedPoint, Equiv.apply_symm_apply] at h
  ext ⟨i, hi⟩
  have := congr_fun h ⟨i, by omega⟩
  simp only [dif_pos hi] at this
  exact this

/-- embedPoint preserves Euclidean distance -/
private lemma embedPoint_dist {d₁ d₂ : ℕ} (hd : d₁ ≤ d₂)
    (p q : Point d₁) : eucDist (embedPoint hd p) (embedPoint hd q) = eucDist p q := by
  simp only [eucDist]
  -- Express both norms using EuclideanSpace.norm_eq: ‖v‖ = √(∑ i, ‖v i‖²)
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
  congr 1
  -- Goal: ∑ i, ‖(embedPoint hd p - embedPoint hd q) i‖² = ∑ i, ‖(p - q) i‖²
  -- Step 1: Simplify LHS coordinates using the zero-padding structure
  have hcoord : ∀ j : Fin d₂,
      ‖(embedPoint hd p - embedPoint hd q) j‖ ^ 2 =
        if j.val < d₁ then ‖(p - q) (⟨j.val, by omega⟩ : Fin d₁)‖ ^ 2 else 0 := by
    intro j
    simp only [embedPoint, Pi.sub_apply, EuclideanSpace.equiv, PiLp.equiv_symm_apply]
    split_ifs with h <;> simp
  simp_rw [hcoord]
  -- Step 2: Convert to range sums and decompose
  rw [Fin.sum_univ_eq_sum_range, Fin.sum_univ_eq_sum_range]
  -- LHS: ∑ k ∈ range d₂, (if k < d₁ then ‖(p-q) ⟨k, _⟩‖² else 0)
  -- RHS: ∑ k ∈ range d₁, ‖(p-q) ⟨k, _⟩‖²
  -- Split range d₂ = range d₁ + range [d₁, d₂)
  conv_lhs => rw [show d₂ = d₁ + (d₂ - d₁) from by omega, Finset.sum_range_add]
  -- Second part is 0 (all indices ≥ d₁)
  have hzero : ∀ k ∈ Finset.range (d₂ - d₁),
      (if (d₁ + k) < d₁ then ‖(p - q) ⟨d₁ + k, by omega⟩‖ ^ 2 else 0) = 0 := by
    intro k _; simp [show ¬(d₁ + k < d₁) from by omega]
  rw [Finset.sum_eq_zero hzero, add_zero]
  -- First part matches: both sum the same values over range d₁
  apply Finset.sum_congr rfl
  intro k hk
  simp only [Finset.mem_range] at hk
  simp [hk]

/-- g_d(n) is non-decreasing in d: more dimensions → more equidistant configurations →
    more points needed to guarantee n distinct distances.
    Proved via isometric embedding ℝ^{d₁} ↪ ℝ^{d₂}. -/
theorem g_mono_d :
    ∀ d₁ d₂ n : ℕ, d₁ ≤ d₂ → n ≥ 2 → g d₁ n ≤ g d₂ n := by
  intro d₁ d₂ n hd hn
  by_cases hn2 : n = 0
  · omega
  · obtain ⟨m, hm⟩ := g_well_defined d₂ n (by omega)
    have hne : Set.Nonempty {m | ∀ P : Finset (Point d₂), P.card = m →
        determinesNDistances P n} := ⟨m, hm⟩
    have hmem := Nat.sInf_mem hne
    -- g d₂ n is in the d₁ threshold set (embed any d₁ config into d₂)
    suffices h : g d₂ n ∈ {m | ∀ P : Finset (Point d₁), P.card = m →
        determinesNDistances P n} from Nat.sInf_le h
    intro P hP
    -- Embed P into ℝ^{d₂}
    let P' := P.image (embedPoint hd)
    have hP'card : P'.card = P.card :=
      Finset.card_image_of_injective _ (embedPoint_injective hd)
    -- P' determines ≥ n distances by g d₂ n property
    have hP'det := hmem P' (hP'card.trans hP)
    -- Distances are preserved by embedding
    unfold determinesNDistances numDistinctDistances at hP'det ⊢
    -- distinctDistances P' contains same values as distinctDistances P
    suffices hcard : (distinctDistances P').card ≥ (distinctDistances P).card by
      omega
    apply Finset.card_le_card
    intro r hr
    simp only [distinctDistances, Finset.mem_filter, Finset.mem_image,
      Finset.mem_product] at hr ⊢
    obtain ⟨⟨⟨p, q⟩, ⟨hp, hq⟩, rfl⟩, hr_pos⟩ := hr
    refine ⟨⟨(embedPoint hd p, embedPoint hd q),
      ⟨Finset.mem_image_of_mem _ hp, Finset.mem_image_of_mem _ hq⟩, ?_⟩, ?_⟩
    · exact (embedPoint_dist hd p q).symm
    · rw [embedPoint_dist hd]; exact hr_pos

/-
## Connection to f_d(n)

The inverse function from problem #1083.
-/

/-- f_d(n) = max distinct distances from n points in ℝ^d -/
noncomputable def f (d n : ℕ) : ℕ :=
  sSup {k : ℕ | ∃ P : Finset (Point d), P.card = n ∧ numDistinctDistances P = k}

/-- Relationship: g_d(n) = min{m : f_d(m) ≥ n} -/
/-
## The Open Problem

The limit question remains unresolved.
-/

/-- The main open question -/
def erdos1089OpenProblem : Prop :=
  ∀ n ≥ 2, erdos1089Conjecture n

#check g
#check gRatio
#check erdos1089Conjecture
#check erdos_lower_bound
#check erdos_straus_upper_bound
