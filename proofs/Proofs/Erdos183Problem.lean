/-
Erdős Problem #183: Multicolor Triangle Ramsey Numbers

**Problem Statement (OPEN)**

Determine the limit of R(3;k)^{1/k} as k → ∞, where R(3;k) is the minimal n
such that any k-coloring of the edges of the complete graph K_n must contain
a monochromatic triangle.

**Reward:** $250 ($100 for proving the limit is finite)

**Known Bounds:**
- Upper: R(3;k) ≤ ⌈e·k!⌉ (pigeonhole argument)
- Lower: R(3;k) ≥ 380^{k/5} - O(1) (Ageron et al., 2021)

**Status:** OPEN

**Proved in this file:**
- forcing_set_nonempty: Ramsey's theorem for triangles (pigeonhole induction)
- R(3;1) = 3 (trivial: 1 color)
- R(3;2) = 6 (classical R(3,3): pigeonhole upper bound + C₅ lower bound)
- Monotonicity: k₁ ≤ k₂ → R(3;k₁) ≤ R(3;k₂)
- R(3;k) ≥ 3 for all k ≥ 1

**Reference:** [Er61], [ACPPRT21]

Adapted from erdosproblems.com (Apache 2.0 License)
-/

import Mathlib

open Finset SimpleGraph
open scoped Classical

namespace Erdos183

/-
# Part 1: Basic Definitions

The multicolor Ramsey number R(3;k) is the minimum n such that any k-coloring
of edges of K_n contains a monochromatic triangle.
-/

/-- A k-coloring of edges assigns each edge to one of k colors (0 to k-1) -/
def EdgeColoring (n k : ℕ) := Fin n × Fin n → Fin k

/-- A coloring is symmetric if c(i,j) = c(j,i) -/
def IsSymmetric {n k : ℕ} (c : EdgeColoring n k) : Prop :=
  ∀ i j : Fin n, c (i, j) = c (j, i)

/-- A monochromatic triangle in color `color` -/
def HasMonochromaticTriangle {n k : ℕ} (c : EdgeColoring n k) (color : Fin k) : Prop :=
  ∃ i j l : Fin n, i ≠ j ∧ j ≠ l ∧ i ≠ l ∧
    c (i, j) = color ∧ c (j, l) = color ∧ c (i, l) = color

/-- A coloring has some monochromatic triangle -/
def HasSomeMonochromaticTriangle {n k : ℕ} (c : EdgeColoring n k) : Prop :=
  ∃ color : Fin k, HasMonochromaticTriangle c color

/-- A coloring avoids all monochromatic triangles -/
def AvoidsMonochromaticTriangles {n k : ℕ} (c : EdgeColoring n k) : Prop :=
  ¬HasSomeMonochromaticTriangle c

/-
# Part 2: The Ramsey Number R(3;k)

R(3;k) is the minimum n such that every k-coloring of K_n has a monochromatic triangle.
-/

/-- n forces a monochromatic triangle in any k-coloring -/
def ForcesMonochromaticTriangle (n k : ℕ) : Prop :=
  k ≥ 1 → ∀ c : EdgeColoring n k, IsSymmetric c → HasSomeMonochromaticTriangle c

/-! ### Proof of forcing_set_nonempty (Ramsey's theorem for triangles)

By induction on k: base case k=1 uses K₃, inductive step uses pigeonhole
to find ≥ m same-colored neighbors of a fixed vertex, then either an edge
among them completes a triangle or the remaining k-1 colors force one.
-/

/-- Map Fin (k+1) to Fin k by collapsing color c₀.
    Injective on values ≠ c₀. Used for color relabeling in the inductive step. -/
private def mapColor {k : ℕ} (hk : k ≥ 1) (c₀ x : Fin (k + 1)) : Fin k :=
  if h : x = c₀ then ⟨0, by omega⟩
  else ⟨if x.val < c₀.val then x.val else x.val - 1, by
    have := x.isLt; have := c₀.isLt; have : x.val ≠ c₀.val := Fin.val_ne_of_ne h
    split <;> omega⟩

/-- mapColor is injective on arguments ≠ c₀ -/
private lemma mapColor_injective_ne {k : ℕ} (hk : k ≥ 1) {c₀ x y : Fin (k + 1)}
    (hx : x ≠ c₀) (hy : y ≠ c₀) (heq : mapColor hk c₀ x = mapColor hk c₀ y) : x = y := by
  simp only [mapColor, dif_neg hx, dif_neg hy, Fin.mk.injEq] at heq
  have : x.val ≠ c₀.val := Fin.val_ne_of_ne hx
  have : y.val ≠ c₀.val := Fin.val_ne_of_ne hy
  ext; split_ifs at heq <;> omega

/-- ForcesMonochromaticTriangle m k with k ≥ 1 requires m ≥ 3 (need 3 distinct vertices) -/
private lemma forces_imp_ge_three {m k : ℕ} (hk : k ≥ 1)
    (hf : ForcesMonochromaticTriangle m k) : m ≥ 3 := by
  by_contra hlt; push_neg at hlt
  obtain ⟨_, i, j, l, hij, hjl, hil, _, _, _⟩ :=
    hf hk (fun _ => ⟨0, by omega⟩) (fun _ _ => rfl)
  interval_cases m
  · exact i.elim0
  · exact hij (Fin.ext (by omega))
  · have : i = j ∨ i = l ∨ j = l := by
      rcases i with ⟨i, hi⟩; rcases j with ⟨j, hj⟩; rcases l with ⟨l, hl⟩
      simp only [Fin.mk.injEq]; omega
    rcases this with rfl | rfl | rfl <;> contradiction

/-- The forcing set is nonempty for all k ≥ 1 (Ramsey's theorem for triangles).
    Proved by induction on k using the pigeonhole principle. -/
theorem forcing_set_nonempty (k : ℕ) (hk : k ≥ 1) :
    ∃ n : ℕ, ForcesMonochromaticTriangle n k := by
  induction k with
  | zero => omega
  | succ k' ih =>
    by_cases hk' : k' = 0
    · -- Base: k=1, K₃ suffices (1 color means all edges monochromatic)
      subst hk'
      refine ⟨3, fun _ c _ => ?_⟩
      refine ⟨⟨0, by omega⟩, ⟨0, by omega⟩, ⟨1, by omega⟩, ⟨2, by omega⟩,
        by decide, by decide, by decide, ?_, ?_, ?_⟩
      all_goals exact Fin.ext (by omega)
    · -- Inductive step: k'+1 ≥ 2 colors
      have hk'1 : k' ≥ 1 := by omega
      obtain ⟨m, hm⟩ := ih hk'1
      have hm3 : m ≥ 3 := forces_imp_ge_three hk'1 hm
      -- N = (k'+1)·(m-1)+2 suffices: v₀ has N-1 = (k'+1)·(m-1)+1 neighbors,
      -- pigeonhole gives ≥ m same-colored neighbors
      refine ⟨(k' + 1) * (m - 1) + 2, fun hk1 c hsym => ?_⟩
      -- Fix vertex v₀
      let v₀ : Fin ((k' + 1) * (m - 1) + 2) := ⟨0, by omega⟩
      let others := (Finset.univ : Finset (Fin ((k' + 1) * (m - 1) + 2))).erase v₀
      have hoc : others.card = (k' + 1) * (m - 1) + 1 := by
        simp [others, Finset.card_erase_of_mem (Finset.mem_univ v₀), Fintype.card_fin]
      -- Pigeonhole: some color c₀ appears on ≥ m edges from v₀
      have h_pig : (Finset.univ : Finset (Fin (k' + 1))).card * (m - 1) < others.card := by
        rw [Finset.card_univ, Fintype.card_fin, hoc]; omega
      obtain ⟨c₀, _, h_fib⟩ := Finset.exists_lt_card_fiber_of_mul_lt_card_of_maps_to
        (f := fun u => c (v₀, u)) (fun _ _ => Finset.mem_univ _) h_pig
      -- The fiber: vertices connected to v₀ by color c₀
      let S := others.filter (fun u => c (v₀, u) = c₀)
      have hSm : S.card ≥ m := by change m - 1 < S.card at h_fib; omega
      -- Embed Fin m into the fiber (following RamseyR4k pattern)
      obtain ⟨T, hTsub, hTcard⟩ := Finset.exists_subset_card_eq hSm
      let iso := T.orderIsoOfFin hTcard
      let e : Fin m → Fin ((k' + 1) * (m - 1) + 2) := fun i => (iso i).val
      have e_inj : Function.Injective e :=
        fun a b h => iso.injective (Subtype.val_injective h)
      have e_in_S : ∀ i, e i ∈ S := fun i => hTsub (iso i).prop
      have e_ne : ∀ i, e i ≠ v₀ := fun i => by
        have := e_in_S i
        simp only [S, others, Finset.mem_filter, Finset.mem_erase] at this
        exact this.1.1
      have e_col : ∀ i, c (v₀, e i) = c₀ := fun i => by
        have := e_in_S i
        simp only [S, Finset.mem_filter] at this; exact this.2
      -- Case: does any edge among embedded vertices have color c₀?
      by_cases h_c₀ : ∃ i j : Fin m, i ≠ j ∧ c (e i, e j) = c₀
      · -- Triangle with v₀
        obtain ⟨i, j, hij, hcij⟩ := h_c₀
        exact ⟨c₀, v₀, e i, e j, (e_ne i).symm, e_inj.ne hij, (e_ne j).symm,
          e_col i, hcij, e_col j⟩
      · -- No c₀-edge among embedded vertices: relabel to k'-coloring
        push_neg at h_c₀
        let g : EdgeColoring m k' := fun p => mapColor hk'1 c₀ (c (e p.1, e p.2))
        have g_sym : IsSymmetric g := fun i j =>
          show mapColor hk'1 c₀ (c (e i, e j)) = mapColor hk'1 c₀ (c (e j, e i)) from
            congr_arg (mapColor hk'1 c₀) (hsym (e i) (e j))
        -- Apply inductive hypothesis: k'-coloring of K_m has a monochromatic triangle
        obtain ⟨color', i, j, l, hij, hjl, hil, hcij', hcjl', hcil'⟩ :=
          hm hk'1 g g_sym
        -- All three edges have the same original color (mapColor injective on ≠ c₀)
        have h_ij_jl := mapColor_injective_ne hk'1 (h_c₀ i j hij) (h_c₀ j l hjl)
          (hcij'.trans hcjl'.symm)
        have h_ij_il := mapColor_injective_ne hk'1 (h_c₀ i j hij) (h_c₀ i l hil)
          (hcij'.trans hcil'.symm)
        exact ⟨c (e i, e j), e i, e j, e l,
          e_inj.ne hij, e_inj.ne hjl, e_inj.ne hil,
          rfl, h_ij_jl.symm, h_ij_il.symm⟩

/-- Definition of R(3;k) as the minimum n forcing a monochromatic triangle -/
noncomputable def R3k (k : ℕ) : ℕ :=
  if hk : k ≥ 1 then
    Nat.find (forcing_set_nonempty k hk)
  else 0

/-
# Part 3: Known Small Values

Some values of R(3;k) are known exactly for small k.
-/

/-- R(3;1) = 3 (any coloring of K_3 has a monochromatic triangle).
    Proof: Upper bound — with 1 color, every triangle is monochromatic.
    Lower bound — Fin 2 has only 2 elements, so no triangle exists. -/
theorem R3k_one : R3k 1 = 3 := by
  unfold R3k
  rw [dif_pos (show (1 : ℕ) ≥ 1 from le_refl 1)]
  apply Nat.le_antisymm
  · -- Nat.find h ≤ 3: ForcesMonochromaticTriangle 3 1
    apply Nat.find_min'
    intro _ c _
    refine ⟨⟨0, by omega⟩, ⟨0, by omega⟩, ⟨1, by omega⟩, ⟨2, by omega⟩,
      by decide, by decide, by decide, ?_, ?_, ?_⟩
    all_goals exact Fin.ext (by omega)
  · -- 3 ≤ Nat.find h: all m < 3 fail to force
    by_contra hlt
    push_neg at hlt
    set n := Nat.find (forcing_set_nonempty 1 (le_refl 1)) with hn_def
    have hn_lt : n < 3 := hlt
    have h_spec : ForcesMonochromaticTriangle n 1 := Nat.find_spec (forcing_set_nonempty 1 (le_refl 1))
    have h_bad := h_spec (le_refl 1) (fun _ => ⟨0, by omega⟩) (fun _ _ => rfl)
    obtain ⟨_, i, j, l, hij, hjl, hil, _, _, _⟩ := h_bad
    interval_cases n
    · exact i.elim0
    · exact hij (Fin.ext (by omega))
    · have : i = j ∨ i = l ∨ j = l := by
        rcases i with ⟨i, hi⟩; rcases j with ⟨j, hj⟩; rcases l with ⟨l, hl⟩
        simp only [Fin.mk.injEq]; omega
      rcases this with rfl | rfl | rfl <;> contradiction

/-- Pigeonhole for 5 items in 2 bins: at least 3 share a value.
    Used to find 3 same-colored edges from a vertex in K_6. -/
private lemma pigeonhole_five_two (f : Fin 5 → Fin 2) :
    ∃ (color : Fin 2) (i j k : Fin 5), i ≠ j ∧ j ≠ k ∧ i ≠ k ∧
      f i = color ∧ f j = color ∧ f k = color := by
  have h_pig : (Finset.univ : Finset (Fin 2)).card * 2 < (Finset.univ : Finset (Fin 5)).card := by
    simp
  obtain ⟨color, _, h_fib⟩ := Finset.exists_lt_card_fiber_of_mul_lt_card_of_maps_to
    (s := Finset.univ) (t := Finset.univ) (f := f) (fun _ _ => Finset.mem_univ _) h_pig
  have h3 : 3 ≤ (Finset.univ.filter (f · = color)).card := by omega
  obtain ⟨T, hTsub, hTcard⟩ := Finset.exists_subset_card_eq h3
  let iso := T.orderIsoOfFin hTcard
  refine ⟨color, (iso ⟨0, by omega⟩).val, (iso ⟨1, by omega⟩).val, (iso ⟨2, by omega⟩).val,
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro h
    have key : (0 : ℕ) = 1 := congrArg Fin.val (iso.injective (Subtype.val_injective h))
    omega
  · intro h
    have key : (1 : ℕ) = 2 := congrArg Fin.val (iso.injective (Subtype.val_injective h))
    omega
  · intro h
    have key : (0 : ℕ) = 2 := congrArg Fin.val (iso.injective (Subtype.val_injective h))
    omega
  · exact (Finset.mem_filter.mp (hTsub (iso ⟨0, by omega⟩).prop)).2
  · exact (Finset.mem_filter.mp (hTsub (iso ⟨1, by omega⟩).prop)).2
  · exact (Finset.mem_filter.mp (hTsub (iso ⟨2, by omega⟩).prop)).2

/-- In Fin 2, if x ≠ c then x equals the other value. -/
private lemma fin2_other {x c : Fin 2} (h : x ≠ c) : x = (1 : Fin 2) - c := by
  fin_cases x <;> fin_cases c <;> simp_all

/-- Given vertex v₀ and three neighbors u₁,u₂,u₃ all connected to v₀ by the same color,
    there must be a monochromatic triangle (either with v₀ or among u₁,u₂,u₃).
    This is the key step in proving R(3,3) = 6. -/
private lemma triangle_from_three_neighbors {n : ℕ} (c : EdgeColoring n 2)
    (v₀ u₁ u₂ u₃ : Fin n)
    (h01 : v₀ ≠ u₁) (h02 : v₀ ≠ u₂) (h03 : v₀ ≠ u₃)
    (h12 : u₁ ≠ u₂) (h23 : u₂ ≠ u₃) (h13 : u₁ ≠ u₃)
    (color : Fin 2)
    (hc1 : c (v₀, u₁) = color) (hc2 : c (v₀, u₂) = color) (hc3 : c (v₀, u₃) = color) :
    HasSomeMonochromaticTriangle c := by
  -- Check edges among u₁,u₂,u₃. If any has `color`, we get a triangle with v₀.
  -- If none does, all three have the other color → monochromatic triangle {u₁,u₂,u₃}.
  by_cases h_e12 : c (u₁, u₂) = color
  · exact ⟨color, v₀, u₁, u₂, h01, h12, h02, hc1, h_e12, hc2⟩
  by_cases h_e23 : c (u₂, u₃) = color
  · exact ⟨color, v₀, u₂, u₃, h02, h23, h03, hc2, h_e23, hc3⟩
  by_cases h_e13 : c (u₁, u₃) = color
  · exact ⟨color, v₀, u₁, u₃, h01, h13, h03, hc1, h_e13, hc3⟩
  · -- All three edges have the other color
    exact ⟨(1 : Fin 2) - color, u₁, u₂, u₃, h12, h23, h13,
      fin2_other h_e12, fin2_other h_e23, fin2_other h_e13⟩

/-- Helper: no three distinct elements exist in Fin m for m < 3. -/
private lemma no_three_distinct_lt3 {m : ℕ} (hm : m < 3) (i j l : Fin m)
    (hij : i ≠ j) (hjl : j ≠ l) (hil : i ≠ l) : False := by
  interval_cases m
  · exact i.elim0
  · exact hij (Fin.ext (by omega))
  · have : i = j ∨ i = l ∨ j = l := by
      rcases i with ⟨i, hi⟩; rcases j with ⟨j, hj⟩; rcases l with ⟨l, hl⟩
      simp only [Fin.mk.injEq]; omega
    rcases this with rfl | rfl | rfl <;> contradiction

set_option maxHeartbeats 800000 in
/-- R(3;2) = 6 is the classical Ramsey number R(3,3).
    Proof: Upper bound by pigeonhole (vertex with 5 edges → 3 same color → forced triangle).
    Lower bound: exhibit triangle-free 2-colorings for K₃, K₄, K₅. -/
theorem R3k_two : R3k 2 = 6 := by
  unfold R3k
  rw [dif_pos (show (2 : ℕ) ≥ 1 from by omega)]
  apply Nat.le_antisymm
  · -- Nat.find h ≤ 6: ForcesMonochromaticTriangle 6 2
    apply Nat.find_min'
    -- UPPER BOUND: ForcesMonochromaticTriangle 6 2
    intro _ c _hsym
    -- Consider edges from vertex 0 to the 5 other vertices
    let f : Fin 5 → Fin 2 := fun i => c (⟨0, by omega⟩, ⟨i.val + 1, by omega⟩)
    -- Pigeonhole: some color appears on ≥ 3 of these 5 edges
    obtain ⟨color, i, j, k, hij, hjk, hik, hci, hcj, hck⟩ := pigeonhole_five_two f
    -- Apply the triangle lemma to vertex 0 and the three same-colored neighbors
    exact triangle_from_three_neighbors c
      ⟨0, by omega⟩ ⟨i.val + 1, by omega⟩ ⟨j.val + 1, by omega⟩ ⟨k.val + 1, by omega⟩
      (fun h => absurd (congrArg Fin.val h).symm (Nat.succ_ne_zero i.val))
      (fun h => absurd (congrArg Fin.val h).symm (Nat.succ_ne_zero j.val))
      (fun h => absurd (congrArg Fin.val h).symm (Nat.succ_ne_zero k.val))
      (fun h => hij (Fin.ext (Nat.succ.inj (congrArg Fin.val h))))
      (fun h => hjk (Fin.ext (Nat.succ.inj (congrArg Fin.val h))))
      (fun h => hik (Fin.ext (Nat.succ.inj (congrArg Fin.val h))))
      color hci hcj hck
  · -- 6 ≤ Nat.find h: for all m < 6, ¬ForcesMonochromaticTriangle m 2
    by_contra hlt
    push_neg at hlt
    set n := Nat.find (forcing_set_nonempty 2 (by omega)) with hn_def
    have hn_lt : n < 6 := hlt
    have h_spec : ForcesMonochromaticTriangle n 2 := Nat.find_spec (forcing_set_nonempty 2 (by omega))
    interval_cases n
    · obtain ⟨_, i, _, _, _, _, _, _, _, _⟩ :=
        h_spec (by omega) (fun _ => ⟨0, by omega⟩) (fun _ _ => rfl)
      exact i.elim0
    · obtain ⟨_, i, j, _, hij, _, _, _, _, _⟩ :=
        h_spec (by omega) (fun _ => ⟨0, by omega⟩) (fun _ _ => rfl)
      exact hij (Fin.ext (by omega))
    · obtain ⟨_, i, j, l, hij, hjl, hil, _, _, _⟩ :=
        h_spec (by omega) (fun _ => ⟨0, by omega⟩) (fun _ _ => rfl)
      exact no_three_distinct_lt3 (by omega) i j l hij hjl hil
    · let c₃ : EdgeColoring 3 2 := fun p =>
        if (p.1.val = 0 ∧ p.2.val = 1) ∨ (p.1.val = 1 ∧ p.2.val = 0) then 0 else 1
      have hsym₃ : IsSymmetric c₃ := by
        intro i j; simp only [c₃]; fin_cases i <;> fin_cases j <;> simp
      have h_avoid₃ : AvoidsMonochromaticTriangles c₃ := by decide
      exact h_avoid₃ (h_spec (by omega) c₃ hsym₃)
    · let c₄ : EdgeColoring 4 2 := fun p =>
        if (p.1.val = 0 ∧ p.2.val = 1) ∨ (p.1.val = 1 ∧ p.2.val = 0) ∨
           (p.1.val = 2 ∧ p.2.val = 3) ∨ (p.1.val = 3 ∧ p.2.val = 2) then 0 else 1
      have hsym₄ : IsSymmetric c₄ := by decide
      have h_avoid₄ : AvoidsMonochromaticTriangles c₄ := by decide
      exact h_avoid₄ (h_spec (by omega) c₄ hsym₄)
    · let c₅ : EdgeColoring 5 2 := fun p =>
        if (p.1.val + 5 - p.2.val) % 5 = 1 ∨ (p.1.val + 5 - p.2.val) % 5 = 4 then 0 else 1
      have hsym₅ : IsSymmetric c₅ := by decide
      have h_avoid₅ : AvoidsMonochromaticTriangles c₅ := by decide
      exact h_avoid₅ (h_spec (by omega) c₅ hsym₅)

/-- Monotonicity: more colors requires more vertices to force a monochromatic triangle.
    Proof: embed a k₁-coloring into a k₂-coloring via Fin.castLE; any monochromatic
    triangle for the k₂-coloring is also monochromatic for the k₁-coloring (injectivity). -/
theorem R3k_mono {k₁ k₂ : ℕ} (h : k₁ ≤ k₂) : R3k k₁ ≤ R3k k₂ := by
  by_cases hk₁ : k₁ ≥ 1
  · -- k₁ ≥ 1 implies k₂ ≥ 1
    have hk₂ : k₂ ≥ 1 := le_trans hk₁ h
    -- Unfold R3k to Nat.find and use minimality
    show R3k k₁ ≤ R3k k₂
    unfold R3k
    rw [dif_pos hk₁, dif_pos hk₂]
    apply Nat.find_min'
    -- Need: ForcesMonochromaticTriangle (Nat.find ...) k₁
    have hforce := Nat.find_spec (forcing_set_nonempty k₂ hk₂)
    -- hforce : ForcesMonochromaticTriangle (Nat.find ...) k₂
    intro _ c₁ hc₁_sym
    -- Embed k₁-coloring as k₂-coloring via Fin.castLE
    let c₂ : EdgeColoring _ k₂ := fun p => Fin.castLE h (c₁ p)
    have hc₂_sym : IsSymmetric c₂ := by
      intro i j; show Fin.castLE h (c₁ (i, j)) = Fin.castLE h (c₁ (j, i))
      congr 1; exact hc₁_sym i j
    -- c₂ has a monochromatic triangle (from forcing property)
    obtain ⟨color₂, i, j, l, hij, hjl, hil, hcij, hcjl, hcil⟩ :=
      hforce hk₂ c₂ hc₂_sym
    -- Extract triangle for c₁ using Fin.castLE injectivity
    have hinj : Function.Injective (Fin.castLE h) := by
      intro a b hab
      ext
      have := congr_arg Fin.val hab
      simpa [Fin.castLE] using this
    exact ⟨c₁ (i, j), i, j, l, hij, hjl, hil, rfl,
      hinj (hcjl.trans hcij.symm), hinj (hcil.trans hcij.symm)⟩
  · -- k₁ = 0: R3k 0 = 0 ≤ R3k k₂
    have : k₁ = 0 := by omega
    subst this
    unfold R3k
    simp only [show ¬((0 : ℕ) ≥ 1) from by omega, dite_false]
    exact Nat.zero_le _

/-- R(3;k) ≥ 3 for all k ≥ 1 (from R3k_one and monotonicity). -/
theorem R3k_ge_three (k : ℕ) (hk : k ≥ 1) : R3k k ≥ 3 := by
  calc R3k k ≥ R3k 1 := R3k_mono hk
    _ = 3 := R3k_one

/-
# Part 4: Upper Bound via Pigeonhole

The inductive bound: R(3;k) ≤ 2 + k(R(3;k-1) - 1)
This yields R(3;k) ≤ ⌈e·k!⌉.
-/

/-- The pigeonhole step extracted from forcing_set_nonempty:
    if m vertices force a triangle with k colors, then
    (k+1)*(m-1)+2 vertices force a triangle with k+1 colors. -/
private lemma forcing_step (k m : ℕ) (hk : k ≥ 1) (hm : ForcesMonochromaticTriangle m k) :
    ForcesMonochromaticTriangle ((k + 1) * (m - 1) + 2) (k + 1) := by
  have hm3 : m ≥ 3 := forces_imp_ge_three hk hm
  intro hk1 c hsym
  let v₀ : Fin ((k + 1) * (m - 1) + 2) := ⟨0, by omega⟩
  let others := (Finset.univ : Finset (Fin ((k + 1) * (m - 1) + 2))).erase v₀
  have hoc : others.card = (k + 1) * (m - 1) + 1 := by
    simp [others, Finset.card_erase_of_mem (Finset.mem_univ v₀), Fintype.card_fin]
  have h_pig : (Finset.univ : Finset (Fin (k + 1))).card * (m - 1) < others.card := by
    rw [Finset.card_univ, Fintype.card_fin, hoc]; omega
  obtain ⟨c₀, _, h_fib⟩ := Finset.exists_lt_card_fiber_of_mul_lt_card_of_maps_to
    (f := fun u => c (v₀, u)) (fun _ _ => Finset.mem_univ _) h_pig
  let S := others.filter (fun u => c (v₀, u) = c₀)
  have hSm : S.card ≥ m := by change m - 1 < S.card at h_fib; omega
  obtain ⟨T, hTsub, hTcard⟩ := Finset.exists_subset_card_eq hSm
  let iso := T.orderIsoOfFin hTcard
  let e : Fin m → Fin ((k + 1) * (m - 1) + 2) := fun i => (iso i).val
  have e_inj : Function.Injective e :=
    fun a b h => iso.injective (Subtype.val_injective h)
  have e_in_S : ∀ i, e i ∈ S := fun i => hTsub (iso i).prop
  have e_ne : ∀ i, e i ≠ v₀ := fun i => by
    have := e_in_S i
    simp only [S, others, Finset.mem_filter, Finset.mem_erase] at this
    exact this.1.1
  have e_col : ∀ i, c (v₀, e i) = c₀ := fun i => by
    have := e_in_S i
    simp only [S, Finset.mem_filter] at this; exact this.2
  by_cases h_c₀ : ∃ i j : Fin m, i ≠ j ∧ c (e i, e j) = c₀
  · obtain ⟨i, j, hij, hcij⟩ := h_c₀
    exact ⟨c₀, v₀, e i, e j, (e_ne i).symm, e_inj.ne hij, (e_ne j).symm,
      e_col i, hcij, e_col j⟩
  · push_neg at h_c₀
    let g : EdgeColoring m k := fun p => mapColor hk c₀ (c (e p.1, e p.2))
    have g_sym : IsSymmetric g := fun i j =>
      show mapColor hk c₀ (c (e i, e j)) = mapColor hk c₀ (c (e j, e i)) from
        congr_arg (mapColor hk c₀) (hsym (e i) (e j))
    obtain ⟨color', i, j, l, hij, hjl, hil, hcij', hcjl', hcil'⟩ :=
      hm hk g g_sym
    have h_ij_jl := mapColor_injective_ne hk (h_c₀ i j hij) (h_c₀ j l hjl)
      (hcij'.trans hcjl'.symm)
    have h_ij_il := mapColor_injective_ne hk (h_c₀ i j hij) (h_c₀ i l hil)
      (hcij'.trans hcil'.symm)
    exact ⟨c (e i, e j), e i, e j, e l,
      e_inj.ne hij, e_inj.ne hjl, e_inj.ne hil,
      rfl, h_ij_jl.symm, h_ij_il.symm⟩

/-- Inductive upper bound on R(3;k): R(3;k) ≤ 2 + k·(R(3;k-1) - 1).
    Proved from the pigeonhole step using Nat.find_min'. -/
theorem R3k_inductive_upper (k : ℕ) (hk : k ≥ 2) :
    R3k k ≤ 2 + k * (R3k (k - 1) - 1) := by
  have hk1 : k ≥ 1 := by omega
  have hkm1 : k - 1 ≥ 1 := by omega
  unfold R3k
  rw [dif_pos hk1, dif_pos hkm1]
  apply Nat.find_min'
  have hm := Nat.find_spec (forcing_set_nonempty (k - 1) hkm1)
  -- forcing_step gives: ForcesMonochromaticTriangle ((k-1+1)*(find...-1)+2) (k-1+1)
  -- Since k-1+1 = k, this is ForcesMonochromaticTriangle (k*(find...-1)+2) k
  have heq : k - 1 + 1 = k := by omega
  have hkey := forcing_step (k - 1) _ hkm1 hm
  rw [heq] at hkey
  convert hkey using 1
  omega

/-- R(3;k) ≤ 3·k! for all k ≥ 1.
    Proof by induction using the pigeonhole recurrence R3k_inductive_upper.
    Base: R(3;1) = 3 = 3·1!.
    Step: R(3;k+1) ≤ 2 + (k+1)·(3·k! - 1) = 3·(k+1)! + 2 - (k+1) ≤ 3·(k+1)!. -/
theorem R3k_le_three_factorial (k : ℕ) (hk : k ≥ 1) : R3k k ≤ 3 * k.factorial := by
  induction k with
  | zero => omega
  | succ n ih =>
    by_cases hn : n = 0
    · subst hn; rw [R3k_one]; norm_num
    · have hn1 : n ≥ 1 := Nat.pos_of_ne_zero hn
      have h_ih := ih hn1
      have h_ge := R3k_ge_three n hn1
      have h_upper := R3k_inductive_upper (n + 1) (by omega)
      -- Cast to ℤ where subtraction is well-behaved
      suffices h : (R3k (n + 1) : ℤ) ≤ 3 * ↑((n + 1).factorial) by exact_mod_cast h
      have h1 : (R3k (n + 1) : ℤ) ≤ 2 + (↑n + 1) * (↑(R3k n) - 1) := by
        have hsub : (↑(R3k n - 1) : ℤ) = ↑(R3k n) - 1 :=
          Nat.cast_sub (show 1 ≤ R3k n by omega)
        have hup : (R3k (n + 1) : ℤ) ≤ ↑(2 + (n + 1) * (R3k n - 1)) := by exact_mod_cast h_upper
        have hcast : (↑(2 + (n + 1) * (R3k n - 1)) : ℤ) = 2 + (↑n + 1) * (↑(R3k n) - 1) := by
          push_cast [hsub]; ring
        linarith
      have h2 : (R3k n : ℤ) ≤ 3 * ↑(n.factorial) := by exact_mod_cast h_ih
      rw [show ((n + 1).factorial : ℤ) = (↑n + 1) * ↑(n.factorial) from by
        push_cast [Nat.factorial_succ]; ring]
      nlinarith [show (n : ℤ) ≥ 1 from by exact_mod_cast hn1]

/-- The upper bound via pigeonhole: R(3;k) ≤ C·k! for C = 3.
    Proved from R3k_le_three_factorial. The tighter bound R(3;k) ≤ ⌈e·k!⌉
    (i.e., C = e with no additive constant) also holds but requires real
    analysis to connect the subfactorial sum to the exp series. -/
theorem R3k_factorial_upper :
    ∃ C : ℝ, C > 0 ∧ ∀ k : ℕ, k ≥ 1 → (R3k k : ℝ) ≤ C * k.factorial := by
  exact ⟨3, by norm_num, fun k hk => by exact_mod_cast R3k_le_three_factorial k hk⟩

/-
# Part 5: Lower Bound via Schur Numbers

The best known lower bound uses connections to Schur numbers.
R(3;k) ≥ 380^{k/5} - O(1) (Ageron et al., 2021)
-/

/-- Schur number S(k) is the largest n such that {1,...,n} can be k-colored
    without monochromatic x + y = z.
    Defined as a Prop (not computed) since Schur numbers are extremely hard to determine.
    Known values: S(1)=1, S(2)=4, S(3)=13, S(4)=44; S(5) is unknown.
    Not used in any theorem below — included for documentation. -/
def SchurNumber (_k : ℕ) : Prop :=
  True  -- placeholder; full definition would require sum-free coloring formalization


/-- Vertex monotonicity for `ForcesMonochromaticTriangle`: if m vertices already
    force a monochromatic triangle under any k-coloring, then so do m' ≥ m
    vertices. Proof: restrict an m'-coloring to its first m vertices via
    `Fin.castLE`, apply the m-forcing hypothesis, lift the resulting triangle
    back to m' using injectivity of `Fin.castLE`. Building block toward the
    doubling construction R(3;k+1) ≥ 2·R(3;k) - 1, which would eliminate the
    remaining axiom. -/
private lemma forces_mono {m m' k : ℕ} (h : m ≤ m')
    (hf : ForcesMonochromaticTriangle m k) :
    ForcesMonochromaticTriangle m' k := by
  intro hk c hsym
  let c_r : EdgeColoring m k := fun p => c (Fin.castLE h p.1, Fin.castLE h p.2)
  have h_inj : Function.Injective (Fin.castLE h) := by
    intro a b hab
    ext
    have := congr_arg Fin.val hab
    simpa [Fin.castLE] using this
  have c_r_sym : IsSymmetric c_r := fun i j => hsym _ _
  obtain ⟨color, i, j, l, hij, hjl, hil, hcij, hcjl, hcil⟩ := hf hk c_r c_r_sym
  refine ⟨color, Fin.castLE h i, Fin.castLE h j, Fin.castLE h l,
    fun heq => hij (h_inj heq), fun heq => hjl (h_inj heq),
    fun heq => hil (h_inj heq), ?_, ?_, ?_⟩
  · exact hcij
  · exact hcjl
  · exact hcil

/- The lower bound R(3;k) ≥ 2^k is proved below via the doubling construction.
   This gives R3k_exponential_lower with c = 2, eliminating the axiom. -/

/-
# Part 6b: The Doubling Construction

Formalizes the argument in the docstring above:
- doubleColoring: a triangle-free k-coloring of K_n → triangle-free (k+1)-coloring of K_{2n}
- Uses a new color for cross-half edges, reuses the k-coloring within each half
-/

/-- The doubling construction: given a triangle-free k-coloring of K_n,
    build a (k+1)-coloring of K_{n+n} by using a new color (index k) for
    cross-half edges and the original coloring within each half. -/
def doubleColoring {n k : ℕ} (c : EdgeColoring n k) : EdgeColoring (n + n) (k + 1) :=
  fun p =>
    if h₁ : p.1.val < n then
      if h₂ : p.2.val < n then
        Fin.castLE (Nat.le_succ k) (c (⟨p.1.val, h₁⟩, ⟨p.2.val, h₂⟩))
      else Fin.last k
    else
      if h₂ : p.2.val < n then Fin.last k
      else
        Fin.castLE (Nat.le_succ k)
          (c (⟨p.1.val - n, by omega⟩, ⟨p.2.val - n, by omega⟩))

/-- The doubling construction preserves symmetry. -/
lemma doubleColoring_sym {n k : ℕ} (c : EdgeColoring n k) (hc : IsSymmetric c) :
    IsSymmetric (doubleColoring c) := by
  intro i j
  simp only [doubleColoring, Prod.fst, Prod.snd]
  by_cases hi : i.val < n <;> by_cases hj : j.val < n
  · simp only [dif_pos hi, dif_pos hj]
    exact congrArg (Fin.castLE _) (hc ⟨i.val, hi⟩ ⟨j.val, hj⟩)
  · simp only [dif_pos hi, dif_neg hj]
  · simp only [dif_neg hi, dif_pos hj]
  · simp only [dif_neg hi, dif_neg hj]
    exact congrArg (Fin.castLE _) (hc ⟨i.val - n, by omega⟩ ⟨j.val - n, by omega⟩)

/-- Within-half colors have value < k, while the cross-half color has value = k.
    This distinguishes the two cases. -/
private lemma castLE_ne_last {k : ℕ} (x : Fin k) :
    Fin.castLE (Nat.le_succ k) x ≠ Fin.last k := by
  intro h
  have hval : (Fin.castLE (Nat.le_succ k) x).val = x.val := rfl
  have hlast : (Fin.last k).val = k := rfl
  rw [h] at hval; simp [hlast] at hval
  exact Nat.not_lt.mpr (Nat.le_of_eq hval) x.isLt

/-- The doubling construction avoids monochromatic triangles if the original does.
    With 3 vertices and 2 halves, at least 2 are in the same half. If there's a
    monochromatic triangle, same-half edges use old colors and cross-half edges use
    the new color (k). These can't match, giving a contradiction unless all 3 are
    in the same half — but that gives a triangle in c. -/
lemma doubleColoring_avoids {n k : ℕ} (c : EdgeColoring n k)
    (hc : AvoidsMonochromaticTriangles c) :
    AvoidsMonochromaticTriangles (doubleColoring c) := by
  intro ⟨color, i, j, l, hij, hjl, hil, hcij, hcjl, hcil⟩
  by_cases hi : i.val < n <;>
  by_cases hj : j.val < n <;>
  by_cases hl : l.val < n <;>
  simp only [doubleColoring, dif_pos, dif_neg, *] at hcij hcjl hcil
  -- (T,T,T): all first half — triangle in c
  · apply hc; exact ⟨c (⟨i.val,hi⟩, ⟨j.val,hj⟩), ⟨i.val,hi⟩, ⟨j.val,hj⟩, ⟨l.val,hl⟩,
      fun h => hij (by simp only [Fin.mk.injEq] at h; exact Fin.ext h),
      fun h => hjl (by simp only [Fin.mk.injEq] at h; exact Fin.ext h),
      fun h => hil (by simp only [Fin.mk.injEq] at h; exact Fin.ext h),
      rfl, Fin.ext (congrArg Fin.val (hcjl.trans hcij.symm)),
      Fin.ext (congrArg Fin.val (hcil.trans hcij.symm))⟩
  -- (T,T,F): i,j first, l second — i,j edge is within-first (castLE), others cross (last k)
  · exact absurd (hcij.trans hcil.symm) (castLE_ne_last _)
  -- (T,F,T): i,l first, j second — i,l edge is within-first, others cross
  · exact absurd (hcil.trans hcij.symm) (castLE_ne_last _)
  -- (T,F,F): i first, j,l second — j,l edge within-second, others cross
  · exact absurd (hcjl.trans hcij.symm) (castLE_ne_last _)
  -- (F,T,T): j,l first, i second — j,l edge within-first, others cross
  · exact absurd (hcjl.trans hcij.symm) (castLE_ne_last _)
  -- (F,T,F): j first, i,l second — i,l edge within-second, others cross
  · exact absurd (hcil.trans hcij.symm) (castLE_ne_last _)
  -- (F,F,T): l first, i,j second — i,j edge within-second, others cross
  · exact absurd (hcij.trans hcil.symm) (castLE_ne_last _)
  -- (F,F,F): all second half — triangle in c shifted
  · apply hc; exact ⟨c (⟨i.val-n,by omega⟩, ⟨j.val-n,by omega⟩),
      ⟨i.val-n,by omega⟩, ⟨j.val-n,by omega⟩, ⟨l.val-n,by omega⟩,
      fun h => hij (Fin.ext (by simp only [Fin.mk.injEq] at h; omega)),
      fun h => hjl (Fin.ext (by simp only [Fin.mk.injEq] at h; omega)),
      fun h => hil (Fin.ext (by simp only [Fin.mk.injEq] at h; omega)),
      rfl, Fin.ext (congrArg Fin.val (hcjl.trans hcij.symm)),
      Fin.ext (congrArg Fin.val (hcil.trans hcij.symm))⟩

/-- R3k k satisfies both the forcing property and the minimality property. -/
private lemma R3k_min_spec (k : ℕ) (hk : k ≥ 1) :
    ForcesMonochromaticTriangle (R3k k) k ∧
    ∀ m, ForcesMonochromaticTriangle m k → R3k k ≤ m := by
  unfold R3k; rw [dif_pos hk]
  exact ⟨Nat.find_spec (forcing_set_nonempty k hk),
         fun m hm => Nat.find_min' (forcing_set_nonempty k hk) hm⟩

/-- Since R3k k is the minimum forcing n, K_{R3k k - 1} admits a triangle-free k-coloring. -/
private lemma R3k_avoidance_coloring (k : ℕ) (hk : k ≥ 1) :
    ∃ c : EdgeColoring (R3k k - 1) k, IsSymmetric c ∧ AvoidsMonochromaticTriangles c := by
  have h_ge := R3k_ge_three k hk
  have h_not : ¬ForcesMonochromaticTriangle (R3k k - 1) k := fun hf =>
    absurd ((R3k_min_spec k hk).2 _ hf) (by omega)
  unfold ForcesMonochromaticTriangle at h_not
  push_neg at h_not
  obtain ⟨-, c, hcsym, hcno⟩ := h_not
  exact ⟨c, hcsym, hcno⟩

/-- Doubling gives the recurrence 2·(R3k k - 1) + 1 ≤ R3k (k+1). -/
private lemma R3k_doubling_bound (k : ℕ) (hk : k ≥ 1) :
    2 * (R3k k - 1) + 1 ≤ R3k (k + 1) := by
  obtain ⟨c, hcsym, hcavoid⟩ := R3k_avoidance_coloring k hk
  have hdc_avoids := doubleColoring_avoids c hcavoid
  have hdc_sym := doubleColoring_sym c hcsym
  have h_not : ¬ForcesMonochromaticTriangle (R3k k - 1 + (R3k k - 1)) (k + 1) := fun hf =>
    hdc_avoids (hf (by omega) (doubleColoring c) hdc_sym)
  have h_lt : R3k k - 1 + (R3k k - 1) < R3k (k + 1) := by
    by_contra hge
    push_neg at hge
    exact h_not (forces_mono hge (R3k_min_spec (k + 1) (by omega)).1)
  omega

/-- By induction: R3k k ≥ 2^k + 1 for all k ≥ 1. -/
private lemma R3k_ge_two_pow_succ (k : ℕ) (hk : k ≥ 1) : R3k k ≥ 2 ^ k + 1 := by
  induction k with
  | zero => omega
  | succ n ih =>
    by_cases hn : n = 0
    · subst hn; rw [R3k_one]; norm_num
    · have hn1 : n ≥ 1 := by omega
      have h_ih := ih hn1
      have h_dbl := R3k_doubling_bound n hn1
      have h_sub : R3k n - 1 ≥ 2 ^ n := by omega
      have h_mul : 2 * (R3k n - 1) ≥ 2 * 2 ^ n := by omega
      have h_pow : 2 * 2 ^ n = 2 ^ (n + 1) := by ring
      linarith

/-- The exponential lower bound: R3k k ≥ 2^k for all k ≥ 1.
    Proved via the doubling construction: a triangle-free k-coloring of K_n yields
    a triangle-free (k+1)-coloring of K_{2n} by using a new color for cross-half edges.
    Iterating from R(3;1) = 3 gives R(3;k) ≥ 2^k + 1. -/
theorem R3k_exponential_lower :
    ∃ c : ℝ, c > 1 ∧ ∀ k : ℕ, k ≥ 1 → (R3k k : ℝ) ≥ c ^ k := by
  refine ⟨2, by norm_num, fun k hk => ?_⟩
  have h_nat : R3k k ≥ 2 ^ k := by linarith [R3k_ge_two_pow_succ k hk]
  calc (R3k k : ℝ) ≥ ((2 ^ k : ℕ) : ℝ) := by exact_mod_cast h_nat
    _ = (2 : ℝ) ^ k := by push_cast; ring

/-
# Part 6: The Main Question - Limit of k-th Root

Erdős asks: what is lim_{k→∞} R(3;k)^{1/k}?

From the bounds:
- Upper: R(3;k)^{1/k} ≤ (e·k!)^{1/k} → ∞ (suplinear)
- Lower: R(3;k)^{1/k} ≥ 380^{1/5} ≈ 3.28

So R(3;k) grows faster than any exponential c^k but slower than k!.
-/

/-- The k-th root function for R(3;k) -/
noncomputable def kthRootR3k (k : ℕ) : ℝ :=
  (R3k k : ℝ) ^ (1 / k : ℝ)

-- Note: kthRoot_lower and kthRoot_upper were removed due to inconsistency.
-- kthRoot_lower required c > 3 for all k ≥ 1, but kthRootR3k(1) = 3.
-- kthRoot_upper claimed kthRootR3k(k) ≤ (e·k!)^{1/k} for k ≥ 1,
-- but kthRootR3k(1) = 3 > e ≈ 2.718.
-- The correct bounds hold for sufficiently large k and follow from
-- R3k_exponential_lower (lower) and R3k_factorial_upper (upper).

/-- The main open question: does lim R(3;k)^{1/k} exist and what is it? -/
def ErdosProblem183 : Prop :=
  ∃ L : ℝ, Filter.Tendsto kthRootR3k Filter.atTop (nhds L)

/-- Alternative formulation: is the limit finite?
    (All reals are finite, so this is equivalent to ErdosProblem183.) -/
def LimitIsFinite : Prop :=
  ∃ L : ℝ, Filter.Tendsto kthRootR3k Filter.atTop (nhds L)

/-- Alternative formulation: is the limit infinite? -/
def LimitIsInfinite : Prop :=
  Filter.Tendsto kthRootR3k Filter.atTop Filter.atTop

/-
# Part 7: The Growth Rate Question

The gap between bounds is enormous:
- Lower: R(3;k) ≥ c^k for c ≈ 380^{1/5} ≈ 3.28
- Upper: R(3;k) ≤ O(k!)

This means R(3;k) is between exponential and factorial growth.
The exact growth rate remains unknown.
-/

/-- The problem is open -/
def erdos_183_status : String := "OPEN"

/-- Summary of bounds: exponential lower, factorial upper. -/
theorem bounds_summary :
    (∃ c : ℝ, c > 1 ∧ ∀ k ≥ 1, (R3k k : ℝ) ≥ c ^ k) ∧
    (∃ C : ℝ, ∀ k ≥ 1, (R3k k : ℝ) ≤ C * k.factorial) := by
  exact ⟨R3k_exponential_lower, let ⟨C, _, h⟩ := R3k_factorial_upper; ⟨C, h⟩⟩

/-
# Part 8: Connection to Other Problems

R(3;k) connects to several other Ramsey-theoretic quantities.
-/

/-- Erdős Problem #483 is related -/
def relatedProblem : ℕ := 483

/-
# Part 9: Formal Statement

The precise formal statement of Problem #183.
-/

/-- Main theorem: R(3;k) exists and satisfies the given bounds -/
theorem erdos_183_main :
    (∀ k ≥ 1, R3k k ≥ 3) ∧
    (∃ C : ℝ, C > 0 ∧ ∀ k ≥ 1, (R3k k : ℝ) ≤ C * k.factorial) := by
  exact ⟨R3k_ge_three, R3k_factorial_upper⟩

end Erdos183
