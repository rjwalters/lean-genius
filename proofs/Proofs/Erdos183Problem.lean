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
private def mapColor {k : ℕ} (c₀ x : Fin (k + 1)) : Fin k :=
  if h : x = c₀ then ⟨0, by omega⟩
  else ⟨if x.val < c₀.val then x.val else x.val - 1, by
    have := x.isLt; have := c₀.isLt; have : x.val ≠ c₀.val := Fin.val_ne_of_ne h
    split <;> omega⟩

/-- mapColor is injective on arguments ≠ c₀ -/
private lemma mapColor_injective_ne {k : ℕ} {c₀ x y : Fin (k + 1)}
    (hx : x ≠ c₀) (hy : y ≠ c₀) (heq : mapColor c₀ x = mapColor c₀ y) : x = y := by
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
  · exact hij (Subsingleton.elim i j)
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
      subst hk'; exact ⟨3, fun _ c _ =>
        ⟨⟨0, by omega⟩, ⟨0, by omega⟩, ⟨1, by omega⟩, ⟨2, by omega⟩,
         by decide, by decide, by decide,
         Subsingleton.elim _ _, Subsingleton.elim _ _, Subsingleton.elim _ _⟩⟩
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
      have h_pig : (Finset.univ : Finset (Fin (k' + 1))).card • (m - 1) < others.card := by
        rw [Finset.card_univ, Fintype.card_fin, hoc, smul_eq_mul]; omega
      obtain ⟨c₀, _, h_fib⟩ := Finset.exists_lt_card_fiber_of_nsmul_lt_card
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
        exact ⟨c₀, v₀, e i, e j, e_ne i, e_inj.ne hij, e_ne j,
          e_col i, hcij, e_col j⟩
      · -- No c₀-edge among embedded vertices: relabel to k'-coloring
        push_neg at h_c₀
        let g : EdgeColoring m k' := fun p => mapColor c₀ (c (e p.1, e p.2))
        have g_sym : IsSymmetric g := fun i j =>
          show mapColor c₀ (c (e i, e j)) = mapColor c₀ (c (e j, e i)) from
            congr_arg (mapColor c₀) (hsym (e i) (e j))
        -- Apply inductive hypothesis: k'-coloring of K_m has a monochromatic triangle
        obtain ⟨color', i, j, l, hij, hjl, hil, hcij', hcjl', hcil'⟩ :=
          hm hk'1 g g_sym
        -- All three edges have the same original color (mapColor injective on ≠ c₀)
        have h_ij_jl := mapColor_injective_ne (h_c₀ i j hij) (h_c₀ j l hjl)
          (hcij'.trans hcjl'.symm)
        have h_ij_il := mapColor_injective_ne (h_c₀ i j hij) (h_c₀ i l hil)
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
  apply Nat.find_eq_iff.mpr
  refine ⟨?_, ?_⟩
  · -- ForcesMonochromaticTriangle 3 1: any 1-coloring of K_3 has monochromatic triangle
    intro _ c _
    -- With Fin 1, all edges have the same (unique) color
    exact ⟨⟨0, by omega⟩, ⟨0, by omega⟩, ⟨1, by omega⟩, ⟨2, by omega⟩,
      by decide, by decide, by decide,
      Subsingleton.elim _ _, Subsingleton.elim _ _, Subsingleton.elim _ _⟩
  · -- ∀ m < 3, ¬ForcesMonochromaticTriangle m 1
    intro m hm hf
    have := hf (le_refl 1) (fun _ => ⟨0, by omega⟩) (fun _ _ => rfl)
    obtain ⟨_, i, j, l, hij, hjl, hil, _, _, _⟩ := this
    -- Fin m with m < 3 can't have 3 distinct elements
    interval_cases m
    · exact i.elim0
    · exact hij (Subsingleton.elim i j)
    · -- m = 2: Fin 2 = {0, 1}, pigeonhole on 3 elements
      have : i = j ∨ i = l ∨ j = l := by
        rcases i with ⟨i, hi⟩; rcases j with ⟨j, hj⟩; rcases l with ⟨l, hl⟩
        simp only [Fin.mk.injEq]; omega
      rcases this with rfl | rfl | rfl <;> contradiction

/-- Pigeonhole for 5 items in 2 bins: at least 3 share a value.
    Used to find 3 same-colored edges from a vertex in K_6. -/
private lemma pigeonhole_five_two (f : Fin 5 → Fin 2) :
    ∃ (color : Fin 2) (i j k : Fin 5), i ≠ j ∧ j ≠ k ∧ i ≠ k ∧
      f i = color ∧ f j = color ∧ f k = color := by
  native_decide

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
  · exact hij (Subsingleton.elim i j)
  · have : i = j ∨ i = l ∨ j = l := by
      rcases i with ⟨i, hi⟩; rcases j with ⟨j, hj⟩; rcases l with ⟨l, hl⟩
      simp only [Fin.mk.injEq]; omega
    rcases this with rfl | rfl | rfl <;> contradiction

/-- R(3;2) = 6 is the classical Ramsey number R(3,3).
    Proof: Upper bound by pigeonhole (vertex with 5 edges → 3 same color → forced triangle).
    Lower bound: exhibit triangle-free 2-colorings for K₃, K₄, K₅. -/
theorem R3k_two : R3k 2 = 6 := by
  unfold R3k
  rw [dif_pos (show (2 : ℕ) ≥ 1 from by omega)]
  apply Nat.find_eq_iff.mpr
  refine ⟨?_, ?_⟩
  · -- UPPER BOUND: ForcesMonochromaticTriangle 6 2
    intro _ c _hsym
    -- Consider edges from vertex 0 to the 5 other vertices
    let f : Fin 5 → Fin 2 := fun i => c (⟨0, by omega⟩, ⟨i.val + 1, by omega⟩)
    -- Pigeonhole: some color appears on ≥ 3 of these 5 edges
    obtain ⟨color, i, j, k, hij, hjk, hik, hci, hcj, hck⟩ := pigeonhole_five_two f
    -- Apply the triangle lemma to vertex 0 and the three same-colored neighbors
    exact triangle_from_three_neighbors c
      ⟨0, by omega⟩ ⟨i.val + 1, by omega⟩ ⟨j.val + 1, by omega⟩ ⟨k.val + 1, by omega⟩
      (by intro h; simp [Fin.ext_iff] at h; omega)
      (by intro h; simp [Fin.ext_iff] at h; omega)
      (by intro h; simp [Fin.ext_iff] at h; omega)
      (by intro h; simp [Fin.ext_iff] at h; exact hij (Fin.ext (by omega)))
      (by intro h; simp [Fin.ext_iff] at h; exact hjk (Fin.ext (by omega)))
      (by intro h; simp [Fin.ext_iff] at h; exact hik (Fin.ext (by omega)))
      color hci hcj hck
  · -- LOWER BOUND: ∀ m < 6, ¬ForcesMonochromaticTriangle m 2
    intro m hm hf
    interval_cases m
    -- m = 0: Fin 0 is empty
    · obtain ⟨_, i, _, _, _, _, _, _, _, _⟩ :=
        hf (by omega) (fun _ => ⟨0, by omega⟩) (fun _ _ => rfl)
      exact i.elim0
    -- m = 1: Fin 1 is a singleton
    · obtain ⟨_, i, j, _, hij, _, _, _, _, _⟩ :=
        hf (by omega) (fun _ => ⟨0, by omega⟩) (fun _ _ => rfl)
      exact hij (Subsingleton.elim i j)
    -- m = 2: Fin 2, can't find 3 distinct
    · obtain ⟨_, i, j, l, hij, hjl, hil, _, _, _⟩ :=
        hf (by omega) (fun _ => ⟨0, by omega⟩) (fun _ _ => rfl)
      exact no_three_distinct_lt3 (by omega) i j l hij hjl hil
    -- m = 3: color edge {0,1} with 0, rest with 1
    · let c₃ : EdgeColoring 3 2 := fun p =>
        if (p.1.val = 0 ∧ p.2.val = 1) ∨ (p.1.val = 1 ∧ p.2.val = 0) then 0 else 1
      have hsym₃ : IsSymmetric c₃ := by
        intro i j; simp only [c₃]; fin_cases i <;> fin_cases j <;> simp
      obtain ⟨color, i, j, l, hij, hjl, hil, hcij, hcjl, hcil⟩ := hf (by omega) c₃ hsym₃
      fin_cases color <;> fin_cases i <;> fin_cases j <;> fin_cases l <;> simp_all [c₃]
    -- m = 4: matching {01, 23} color 0, rest color 1
    · let c₄ : EdgeColoring 4 2 := fun p =>
        if (p.1.val = 0 ∧ p.2.val = 1) ∨ (p.1.val = 1 ∧ p.2.val = 0) ∨
           (p.1.val = 2 ∧ p.2.val = 3) ∨ (p.1.val = 3 ∧ p.2.val = 2) then 0 else 1
      have hsym₄ : IsSymmetric c₄ := by
        intro i j; simp only [c₄]; fin_cases i <;> fin_cases j <;> simp
      obtain ⟨color, i, j, l, hij, hjl, hil, hcij, hcjl, hcil⟩ := hf (by omega) c₄ hsym₄
      fin_cases color <;> fin_cases i <;> fin_cases j <;> fin_cases l <;> simp_all [c₄]
    -- m = 5: C₅ coloring — cycle {01,12,23,34,40} color 0, diagonals color 1
    · let c₅ : EdgeColoring 5 2 := fun p =>
        let d := (p.1.val + 5 - p.2.val) % 5
        if d = 1 ∨ d = 4 then 0 else 1
      have hsym₅ : IsSymmetric c₅ := by
        intro i j; simp only [c₅]; fin_cases i <;> fin_cases j <;> simp
      obtain ⟨color, i, j, l, hij, hjl, hil, hcij, hcjl, hcil⟩ := hf (by omega) c₅ hsym₅
      fin_cases color <;> fin_cases i <;> fin_cases j <;> fin_cases l <;> simp_all [c₅]

/-- R(3;3) = 17 (Greenwood and Gleason, 1955) -/
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
  have h_pig : (Finset.univ : Finset (Fin (k + 1))).card • (m - 1) < others.card := by
    rw [Finset.card_univ, Fintype.card_fin, hoc, smul_eq_mul]; omega
  obtain ⟨c₀, _, h_fib⟩ := Finset.exists_lt_card_fiber_of_nsmul_lt_card
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
    exact ⟨c₀, v₀, e i, e j, e_ne i, e_inj.ne hij, e_ne j,
      e_col i, hcij, e_col j⟩
  · push_neg at h_c₀
    let g : EdgeColoring m k := fun p => mapColor c₀ (c (e p.1, e p.2))
    have g_sym : IsSymmetric g := fun i j =>
      show mapColor c₀ (c (e i, e j)) = mapColor c₀ (c (e j, e i)) from
        congr_arg (mapColor c₀) (hsym (e i) (e j))
    obtain ⟨color', i, j, l, hij, hjl, hil, hcij', hcjl', hcil'⟩ :=
      hm hk g g_sym
    have h_ij_jl := mapColor_injective_ne (h_c₀ i j hij) (h_c₀ j l hjl)
      (hcij'.trans hcjl'.symm)
    have h_ij_il := mapColor_injective_ne (h_c₀ i j hij) (h_c₀ i l hil)
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
  have : k - 1 + 1 = k := by omega
  rw [← this]
  convert forcing_step (k - 1) _ hkm1 hm using 2
  omega

/-- The upper bound via pigeonhole: R(3;k) ≤ e·k! + O(1) -/
axiom R3k_factorial_upper :
  ∃ C : ℝ, C > 0 ∧ ∀ k : ℕ, k ≥ 1 → (R3k k : ℝ) ≤ Real.exp 1 * k.factorial + C

-- Note: The ceiling form R(3;k) ≤ ⌈e·k!⌉ + 1 requires a tighter constant
-- than R3k_factorial_upper provides. Omitted to avoid a sorry.

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


/-- The Ageron et al. lower bound (2021) -/
axiom R3k_exponential_lower :
  ∃ c : ℝ, c > 1 ∧ ∀ k : ℕ, k ≥ 1 → (R3k k : ℝ) ≥ c ^ k

/-- Specifically: R(3;k) ≥ 380^{k/5} - O(1) -/
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
  constructor
  · exact R3k_exponential_lower
  · obtain ⟨C, _, hbound⟩ := R3k_factorial_upper
    use Real.exp 1 + C
    intro k hk
    have hfact : (k.factorial : ℝ) ≥ 1 := by
      exact_mod_cast Nat.factorial_pos k
    nlinarith [hbound k hk]

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
  constructor
  · exact R3k_ge_three
  · obtain ⟨C, hCpos, hbound⟩ := R3k_factorial_upper
    use Real.exp 1 + C
    constructor
    · linarith [Real.exp_pos 1]
    · intro k hk
      have hfact : (k.factorial : ℝ) ≥ 1 := by
        exact_mod_cast Nat.factorial_pos k
      nlinarith [hbound k hk]

end Erdos183
