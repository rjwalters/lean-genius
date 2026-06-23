/-
# Erdős Problem 129: Ramsey Numbers Avoiding Monochromatic Cliques

Let `R(n; k, r)` denote the smallest `N` such that if the edges of `K_N` are
`r`-colored, there exists a set of `n` vertices containing no monochromatic `K_k`.

Erdős and Gyárfás conjectured that there exist constants `C₁, C₂ > 1`
(depending only on `r`) such that
$$C_1^{n^{1/(k-1)}} < R(n; k, r) < C_2^{n^{1/(k-1)}}.$$

They proved the lower bound for `k = 3`. The upper bound for `k = 3` remains open,
though Girão noted the original formulation may need clarification.

*Reference:* [erdosproblems.com/129](https://www.erdosproblems.com/129)
-/

import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Tactic

open Finset

/- ## Edge coloring and monochromatic clique avoidance -/

/-- An `r`-coloring of edges of the complete graph on `Fin N`. -/
def EdgeColoring (N : ℕ) (r : ℕ) : Type :=
    { p : Fin N × Fin N // p.1 < p.2 } → Fin r

/-- A set `S` of vertices avoids monochromatic `K_k` in color `c` if no `k`-element
subset of `S` has all edges colored `c`. -/
def AvoidsMono (N : ℕ) (r : ℕ) (coloring : EdgeColoring N r)
    (S : Finset (Fin N)) (k : ℕ) (c : Fin r) : Prop :=
    ∀ T : Finset (Fin N), T ⊆ S → T.card = k →
      ∃ e : { p : Fin N × Fin N // p.1 < p.2 },
        e.val.1 ∈ T ∧ e.val.2 ∈ T ∧ coloring e ≠ c

/-- A set `S` contains no monochromatic `K_k` (in any color). -/
def NoMonoClique (N : ℕ) (r : ℕ) (coloring : EdgeColoring N r)
    (S : Finset (Fin N)) (k : ℕ) : Prop :=
    ∀ c : Fin r, AvoidsMono N r coloring S k c

/-- `HasRamseyAvoid N n k r` holds when every `r`-coloring of `K_N`
admits a set of `n` vertices with no monochromatic `K_k`. -/
def HasRamseyAvoid (N n k r : ℕ) : Prop :=
    ∀ coloring : EdgeColoring N r,
      ∃ S : Finset (Fin N), S.card ≥ n ∧ NoMonoClique N r coloring S k

/- ## Main conjecture: exponential bounds -/

/-- The Erdős–Gyárfás conjecture for general `k`: there exist `C₁, C₂ > 1` such that
`C₁^{n^{1/(k-1)}} < R(n;k,r) < C₂^{n^{1/(k-1)}}` for all sufficiently large `n`. -/
def ErdosProblem129 (k r : ℕ) : Prop :=
    2 ≤ k ∧ 2 ≤ r →
    ∃ (C₁ C₂ : ℝ), 1 < C₁ ∧ 1 < C₂ ∧
      ∀ᶠ n in Filter.atTop, ∀ N : ℕ,
        HasRamseyAvoid N n k r →
          C₁ ^ ((n : ℝ) ^ (1 / ((k : ℝ) - 1))) < (N : ℝ) ∧
          ∃ M : ℕ, HasRamseyAvoid M n k r ∧
            (M : ℝ) < C₂ ^ ((n : ℝ) ^ (1 / ((k : ℝ) - 1)))

/-- The specific case `k = 3`: prove `R(n;3,r) < C^{√n}` for some `C > 1`. -/
def ErdosProblem129_k3 (r : ℕ) : Prop :=
    2 ≤ r →
    ∃ (C : ℝ), 1 < C ∧ ∀ᶠ n in Filter.atTop,
      ∃ M : ℕ, HasRamseyAvoid M n 3 r ∧ (M : ℝ) < C ^ Real.sqrt n

/- ## Known results -/

/-- Erdős–Gyárfás lower bound for `k = 3`: `R(n;3,r) > C^{√n}` for some `C > 1`.
That is, for large `n`, no `N < C^{√n}` satisfies `HasRamseyAvoid N n 3 r`. -/

/- ## Basic properties -/

/-- The `n = 0` case is trivially satisfiable: the empty set has card ≥ 0
    and vacuously avoids all monochromatic cliques. -/
theorem hasRamseyAvoid_zero (N k r : ℕ) (hr : 0 < r) :
    HasRamseyAvoid N 0 k r := by
  intro coloring
  exact ⟨∅, by omega, fun c T hT hTk => by
    have : T.card = 0 := Finset.card_eq_zero.mpr (Finset.subset_empty.mp hT)
    omega⟩

/-- The singleton case: for k ≥ 3 and N ≥ 1, any coloring has a 1-vertex set
    avoiding monochromatic K_k. A single vertex has no k-element subset
    when k ≥ 3, so avoidance holds vacuously. -/
theorem hasRamseyAvoid_one_of_k_ge_three (N r : ℕ) (k : ℕ) (hk : 3 ≤ k)
    (hN : 1 ≤ N) (hr : 0 < r) :
    HasRamseyAvoid N 1 k r := by
  intro coloring
  have ⟨v⟩ : Nonempty (Fin N) := ⟨⟨0, by omega⟩⟩
  refine ⟨{v}, by simp, fun c T hT hTk => ?_⟩
  have hTcard := Finset.card_le_card hT
  simp at hTcard
  omega

/-- Small sets avoid large cliques: any set S with |S| < k has no monochromatic
    K_k, since no k-element subset exists. -/
theorem noMonoClique_of_card_lt (N r : ℕ) (coloring : EdgeColoring N r)
    (S : Finset (Fin N)) (k : ℕ) (hlt : S.card < k) :
    NoMonoClique N r coloring S k := by
  intro c T hT hTk
  have : T.card ≤ S.card := Finset.card_le_card hT
  omega

/-- For k ≥ 3 and n ≤ 1, HasRamseyAvoid N n k r holds whenever N ≥ n.
    This combines the n = 0 and n = 1 cases. -/
theorem hasRamseyAvoid_of_n_le_one (N n k r : ℕ) (hk : 3 ≤ k)
    (hn : n ≤ 1) (hN : n ≤ N) (hr : 0 < r) :
    HasRamseyAvoid N n k r := by
  intro coloring
  have ⟨v⟩ : Nonempty (Fin N) := ⟨⟨0, by omega⟩⟩
  refine ⟨{v}, by simp; omega, fun c T hT hTk => ?_⟩
  have : T.card ≤ ({v} : Finset (Fin N)).card := Finset.card_le_card hT
  simp at this
  omega

/-- With more colors, avoiding monochromatic cliques in a fixed set is easier:
    if NoMonoClique holds for r colors, it holds for r' ≥ r colors
    (viewing the r-coloring as an r'-coloring via Fin.castLE). -/
theorem noMonoClique_of_color_embed (N r r' : ℕ) (hr : r ≤ r')
    (coloring : EdgeColoring N r)
    (S : Finset (Fin N)) (k : ℕ)
    (h : NoMonoClique N r coloring S k) :
    NoMonoClique N r' (fun e => Fin.castLE hr (coloring e)) S k := by
  intro c T hT hTk
  -- If c is in range of castLE, use the original avoidance
  -- If c is out of range (c.val ≥ r), then coloring e = castLE(coloring e)
  -- has value < r ≤ c.val, so coloring e ≠ c automatically
  by_cases hc : c.val < r
  · -- c is in the range of the original colors
    obtain ⟨e, he1, he2, hne⟩ := h ⟨c.val, hc⟩ T hT hTk
    exact ⟨e, he1, he2, by simp [Fin.castLE]; intro heq; exact hne (Fin.ext (by omega))⟩
  · -- c is a "new" color not used by the embedded coloring
    -- Any edge in any k-subset will have castLE(coloring e).val < r ≤ c.val
    obtain ⟨e, he1, he2, _⟩ := h ⟨0, by omega⟩ T hT hTk
    exact ⟨e, he1, he2, by
      intro heq
      have : (Fin.castLE hr (coloring e)).val < r := (coloring e).isLt
      rw [heq] at this
      omega⟩
