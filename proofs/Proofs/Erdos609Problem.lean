/-
  Erdős Problem #609: Monochromatic Odd Cycles in Edge Colorings

  Source: https://erdosproblems.com/609
  Status: OPEN

  Statement:
  Let f(n) be the minimal m such that if the edges of K_{2^n+1} are colored
  with n colors, then there must be a monochromatic odd cycle of length ≤ m.

  Estimate f(n).

  Key Observations:
  - The edges of K_{2^n} CAN be n-colored avoiding all monochromatic odd cycles
  - But K_{2^n+1} forces at least one monochromatic odd cycle
  - The question: how short must such a cycle be?

  Known Results:
  - Chung (1997): Asked if f(n) → ∞
  - Day-Johnson (2017): f(n) ≥ 2^{c√(log n)} for some c > 0
  - Girão-Hunter (2024): f(n) ≪ 2^n / n^{1-o(1)}
  - Janzer-Yip (2025): f(n) ≪ n^{3/2} · 2^{n/2}

  The gap between lower and upper bounds remains large!

  Related: Problem #608 (avoiding specific odd cycles)
-/

import Mathlib

open Finset Function Set SimpleGraph

/-! ## Basic Definitions -/

/-- An n-edge-coloring of a graph G -/
def EdgeColoring' (V : Type*) [DecidableEq V] (n : ℕ) :=
  Sym2 V → Fin n

/-- A cycle in a graph represented as a list of vertices -/
def IsCycle {V : Type*} (G : SimpleGraph V) (cycle : List V) : Prop :=
  cycle.length ≥ 3 ∧
  cycle.Nodup ∧
  (∀ i : Fin (cycle.length - 1), G.Adj (cycle.get ⟨i.val, by omega⟩)
    (cycle.get ⟨i.val + 1, by omega⟩)) ∧
  G.Adj (cycle.getLast (by simp_all)) (cycle.head (by simp_all))

/-- The length of a cycle -/
def cycleLength (cycle : List V) : ℕ := cycle.length

/-- A cycle is odd if its length is odd -/
def IsOddCycle {V : Type*} (G : SimpleGraph V) (cycle : List V) : Prop :=
  IsCycle G cycle ∧ Odd cycle.length

/-! ## Monochromatic Structures -/

/-- A cycle is monochromatic in color c if all edges have color c -/
def IsMonochromaticCycle {V : Type*} [DecidableEq V] {n : ℕ}
    (G : SimpleGraph V) (coloring : EdgeColoring' V n)
    (cycle : List V) (c : Fin n) : Prop :=
  IsCycle G cycle ∧
  ∀ i : Fin (cycle.length - 1),
    coloring ⟦(cycle.get ⟨i.val, by omega⟩, cycle.get ⟨i.val + 1, by omega⟩)⟧ = c

/-- A coloring has a monochromatic odd cycle of length ≤ m -/
def HasMonochromaticOddCycleOfLength {V : Type*} [DecidableEq V] {n : ℕ}
    (G : SimpleGraph V) (coloring : EdgeColoring' V n) (m : ℕ) : Prop :=
  ∃ cycle : List V, ∃ c : Fin n,
    IsOddCycle G cycle ∧
    IsMonochromaticCycle G coloring cycle c ∧
    cycle.length ≤ m

/-! ## The Complete Graph -/

/-- The complete graph on a type -/
def completeGraph (V : Type*) : SimpleGraph V where
  Adj x y := x ≠ y
  symm := fun _ _ h => h.symm
  loopless := fun _ h => h rfl

/-- K_n is the complete graph on Fin n -/
abbrev K (n : ℕ) : SimpleGraph (Fin n) := completeGraph (Fin n)

/-! ## The Function f(n) -/

/-- A coloring of K_{2^n+1} with n colors avoids odd cycles of length ≤ m -/
def AvoidsOddCyclesUpTo (n m : ℕ) (coloring : EdgeColoring' (Fin (2^n + 1)) n) : Prop :=
  ¬HasMonochromaticOddCycleOfLength (K (2^n + 1)) coloring m

/-- f(n) is the minimal m such that every n-coloring of K_{2^n+1}
    has a monochromatic odd cycle of length ≤ m -/
def erdos609_f (n : ℕ) : ℕ :=
  Nat.find (f_exists n)
where
  f_exists (n : ℕ) : ∃ m : ℕ, ∀ coloring : EdgeColoring' (Fin (2^n + 1)) n,
      HasMonochromaticOddCycleOfLength (K (2^n + 1)) coloring m := by
    sorry

/-- Alternative predicate-based definition -/
def IsErdos609_f (n m : ℕ) : Prop :=
  (∀ coloring : EdgeColoring' (Fin (2^n + 1)) n,
    HasMonochromaticOddCycleOfLength (K (2^n + 1)) coloring m) ∧
  (∀ m' < m, ∃ coloring : EdgeColoring' (Fin (2^n + 1)) n,
    ¬HasMonochromaticOddCycleOfLength (K (2^n + 1)) coloring m')

/-! ## The 2^n Threshold -/

/-- Key fact: K_{2^n} CAN be n-colored with no monochromatic odd cycles at all!
    This uses recursive "doubling" construction. -/
theorem K_2n_avoids_odd_cycles (n : ℕ) :
    ∃ coloring : EdgeColoring' (Fin (2^n)) n,
      ∀ m : ℕ, ¬HasMonochromaticOddCycleOfLength (K (2^n)) coloring m := by
  sorry

/-- But K_{2^n+1} forces a monochromatic odd cycle -/
theorem K_2n_plus_1_forces_odd_cycle (n : ℕ) (hn : n ≥ 1) :
    ∀ coloring : EdgeColoring' (Fin (2^n + 1)) n,
      ∃ cycle : List (Fin (2^n + 1)), ∃ c : Fin n,
        IsOddCycle (K (2^n + 1)) cycle ∧
        IsMonochromaticCycle (K (2^n + 1)) coloring cycle c := by
  sorry

/-! ## Avoiding Specific Short Cycles -/

/-- C_5 (pentagon) can be avoided for large n -/
theorem can_avoid_C5 : ∃ N : ℕ, ∀ n ≥ N,
    ∃ coloring : EdgeColoring' (Fin (2^n + 1)) n,
      ¬HasMonochromaticOddCycleOfLength (K (2^n + 1)) coloring 5 := by
  sorry

/-- C_7 (heptagon) can be avoided for large n -/
theorem can_avoid_C7 : ∃ N : ℕ, ∀ n ≥ N,
    ∃ coloring : EdgeColoring' (Fin (2^n + 1)) n,
      ¬HasMonochromaticOddCycleOfLength (K (2^n + 1)) coloring 7 := by
  sorry

/-- Chung's question (1997): Does f(n) → ∞? -/
def chungQuestion : Prop :=
  ∀ M : ℕ, ∃ N : ℕ, ∀ n ≥ N, erdos609_f n ≥ M

/-! ## Known Bounds -/

/-- Day-Johnson (2017): Lower bound f(n) ≥ 2^{c√(log n)} -/
theorem day_johnson_lower_bound : ∃ c : ℝ, c > 0 ∧
    ∀ n ≥ 2, (erdos609_f n : ℝ) ≥ 2^(c * Real.sqrt (Real.log n)) := by
  sorry

/-- Day-Johnson answered Chung's question affirmatively -/
theorem f_tends_to_infinity : chungQuestion := by
  sorry

/-- Girão-Hunter (2024): Upper bound f(n) ≪ 2^n / n^{1-o(1)} -/
theorem girao_hunter_upper_bound : ∃ C : ℝ, C > 0 ∧
    ∀ n ≥ 2, (erdos609_f n : ℝ) ≤ C * 2^n / n := by
  sorry

/-- Janzer-Yip (2025): Improved upper bound f(n) ≪ n^{3/2} · 2^{n/2} -/
theorem janzer_yip_upper_bound : ∃ C : ℝ, C > 0 ∧
    ∀ n ≥ 2, (erdos609_f n : ℝ) ≤ C * n^(3/2 : ℝ) * 2^(n/2) := by
  sorry

/-! ## The Gap -/

/-- The gap between lower and upper bounds is exponential!
    Lower: 2^{c√(log n)}
    Upper: n^{3/2} · 2^{n/2}

    The true behavior of f(n) remains unknown. -/
def boundsGap (n : ℕ) : ℝ :=
  (n^(3/2 : ℝ) * 2^(n/2)) / 2^(Real.sqrt (Real.log n))

/-! ## Connection to Ramsey Theory -/

/-- The Ramsey number R(C_k, C_k, ..., C_k) with r copies -/
def cycleRamsey (k r : ℕ) : ℕ := by
  sorry

/-- For odd k, the cycle Ramsey number grows exponentially in r -/
theorem odd_cycle_ramsey_exponential (k : ℕ) (hk : Odd k) (hk3 : k ≥ 3) :
    ∃ c C : ℝ, c > 0 ∧ C > 0 ∧
      ∀ r ≥ 2, c * 2^r ≤ (cycleRamsey k r : ℝ) ∧
        (cycleRamsey k r : ℝ) ≤ C * 2^r := by
  sorry

/-! ## Bipartite-Free Colorings -/

/-- A graph is bipartite iff it has no odd cycles -/
theorem bipartite_iff_no_odd_cycles (V : Type*) [Fintype V] (G : SimpleGraph V) :
    G.IsBipartite ↔ ∀ cycle : List V, IsCycle G cycle → Even cycle.length := by
  sorry

/-- Each color class avoiding odd cycles must be bipartite -/
theorem color_class_bipartite {V : Type*} [DecidableEq V] [Fintype V] {n : ℕ}
    (coloring : EdgeColoring' V n) (c : Fin n)
    (h : ∀ cycle : List V, ¬(IsOddCycle (completeGraph V) cycle ∧
      IsMonochromaticCycle (completeGraph V) coloring cycle c)) :
    ∃ G : SimpleGraph V, G.IsBipartite ∧
      ∀ e : Sym2 V, coloring e = c → G.Adj e.out.1 e.out.2 := by
  sorry

/-! ## The Doubling Construction -/

/-- The key construction: n-coloring of K_{2^n} avoiding odd cycles.

    Build inductively:
    - Base: K_2 with 1 color (no odd cycles possible)
    - Step: Given K_{2^n} with n colors, build K_{2^{n+1}} with n+1 colors
            by "doubling" and using the new color for cross-edges -/
def doublingConstruction (n : ℕ) : EdgeColoring' (Fin (2^n)) n := by
  sorry

theorem doubling_avoids_odd_cycles (n : ℕ) :
    ∀ m : ℕ, ¬HasMonochromaticOddCycleOfLength (K (2^n)) (doublingConstruction n) m := by
  sorry

/-! ## Main Problem Statement -/

/-- Erdős Problem #609: OPEN

    Estimate f(n), the minimum cycle length forced in any n-coloring of K_{2^n+1}.

    Best known bounds:
    - Lower: 2^{c√(log n)} (Day-Johnson 2017)
    - Upper: n^{3/2} · 2^{n/2} (Janzer-Yip 2025)

    The exponential gap suggests our understanding is incomplete. -/
theorem erdos_609 : ∃ n : ℕ, erdos609_f n ≥ 3 := by
  use 1
  sorry

/-- The problem asks for tight asymptotics of f(n) -/
def erdos609_precise : Prop :=
  ∃ g : ℕ → ℝ, (∀ n, g n > 0) ∧
    (fun n => (erdos609_f n : ℝ)) ≍ g
  where
    f ≍ g := ∃ c₁ c₂ : ℝ, c₁ > 0 ∧ c₂ > 0 ∧ ∃ N : ℕ,
      ∀ n ≥ N, c₁ * g n ≤ f n ∧ f n ≤ c₂ * g n

#check erdos_609
#check day_johnson_lower_bound
#check janzer_yip_upper_bound
#check chungQuestion
