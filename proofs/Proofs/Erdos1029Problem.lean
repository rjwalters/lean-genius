/-
  Erdős Problem #1029: Ramsey Number Growth Rate

  Source: https://erdosproblems.com/1029
  Status: OPEN ($100 for proof, $1000 for disproof)

  Statement:
  If R(k) is the diagonal Ramsey number (minimal n such that every
  2-coloring of K_n contains a monochromatic K_k), prove that
    R(k) / (k · 2^{k/2}) → ∞

  Background:
  The Erdős-Szekeres bounds give:
    (1+o(1)) · (k/e) · 2^{k/2} ≤ R(k) ≤ C(2k-2, k-1) ≈ 4^k / √k

  The lower bound comes from the probabilistic method: a random 2-coloring
  of K_n has expected number of monochromatic K_k's roughly n^k · 2^{-C(k,2)},
  which is < 1 when n ≈ k · 2^{k/2}.

  This problem asks whether R(k) grows strictly faster than k · 2^{k/2}.
  Equivalently: is the probabilistic lower bound far from tight?

  Spencer (1975) improved the lower bound constant to √2/e, but this still
  leaves the ratio R(k)/(k · 2^{k/2}) bounded. The conjecture asserts this
  ratio tends to infinity.

  References:
  [ES35] Erdős-Szekeres, "A combinatorial problem in geometry" (1935)
  [Er93] Erdős, "On some of my favourite problems" (1993)
  [Sp75] Spencer, "Ramsey's theorem - a new lower bound" (1975)

  Tags: ramsey-theory, graph-theory, probabilistic-method, open-problem
-/

import Mathlib
import Proofs.RamseysTheorem

open Nat Filter

/-
## Ramsey Numbers

The diagonal Ramsey number R(k) and basic properties.
-/

/-- A 2-coloring of edges of a complete graph -/
def EdgeColoring (V : Type*) := Sym2 V → Bool

/-- A set of vertices is monochromatic in color c -/
def IsMonochromatic {V : Type*} (coloring : EdgeColoring V) (S : Set V) (c : Bool) : Prop :=
  ∀ x y : V, x ∈ S → y ∈ S → x ≠ y → coloring s(x, y) = c

/-- A coloring contains a monochromatic k-clique -/
def HasMonochromaticClique {V : Type*} [Fintype V] (coloring : EdgeColoring V) (k : ℕ) : Prop :=
  ∃ S : Finset V, S.card = k ∧ (IsMonochromatic coloring S true ∨ IsMonochromatic coloring S false)

/-- Ramsey's theorem: for every k, there exists n such that every 2-coloring
    of K_n contains a monochromatic K_k. Proved by bridging to RamseysTheorem.lean
    which formalizes the classical inductive proof (Wiedijk #31).

    The bridge converts a Sym2-based coloring (col : Sym2 (Fin n) → Bool) to the
    RamseysTheorem.EdgeColoring structure by forcing the diagonal to false (which
    doesn't affect clique membership since cliques only involve distinct vertices). -/
theorem ramsey_exists (k : ℕ) :
    ∃ n, ∀ coloring : EdgeColoring (Fin n), HasMonochromaticClique coloring k := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · -- k = 0: the empty finset is a monochromatic 0-clique in any graph
    exact ⟨0, fun _ => ⟨∅, by simp, Or.inl (fun x y hx _ _ => hx.elim)⟩⟩
  -- k ≥ 1: use RamseysTheorem's inductive proof
  obtain ⟨n, _, hn⟩ := RamseysTheorem.ramsey_theorem k k (by omega) (by omega)
  refine ⟨n, fun col => ?_⟩
  -- Construct a RamseysTheorem.EdgeColoring from the Sym2-based coloring.
  -- Diagonal is forced to false (satisfying irrefl); this is harmless since
  -- IsMonochromatic only queries col s(x, y) for distinct x ≠ y.
  let c : RamseysTheorem.EdgeColoring (Fin n) :=
    { color := fun x y => if x = y then false else col s(x, y)
      symm := fun x y => by
        by_cases h : x = y
        · simp [h]
        · simp only [if_neg h, if_neg (Ne.symm h)]
          congr 1; exact Sym2.eq_swap
      irrefl := fun x => by simp }
  -- Apply the Ramsey property to get a monochromatic k-clique
  rcases hn c with ⟨S, hcard, hred⟩ | ⟨S, hcard, hblue⟩
  · -- Red k-clique → monochromatic clique with color true
    refine ⟨S, hcard, Or.inl fun x y hx hy hne => ?_⟩
    -- Extract: c.redGraph.Adj x y ↔ c.color x y = true ∧ x ≠ y (by def of redGraph)
    have hcolor : c.color x y = true ∧ x ≠ y := hred hx hy hne
    -- c.color x y = (if x = y then false else col s(x,y)) = col s(x,y) since x ≠ y
    rw [show c.color x y = col s(x, y) from if_neg hne] at hcolor
    exact hcolor.1
  · -- Blue k-clique → monochromatic clique with color false
    refine ⟨S, hcard, Or.inr fun x y hx hy hne => ?_⟩
    -- Extract: c.blueGraph.Adj x y ↔ c.color x y = false ∧ x ≠ y (by def of blueGraph)
    have hcolor : c.color x y = false ∧ x ≠ y := hblue hx hy hne
    rw [show c.color x y = col s(x, y) from if_neg hne] at hcolor
    exact hcolor.1

/-- The diagonal Ramsey number R(k): minimal n such that every 2-coloring
    of K_n contains a monochromatic K_k -/
noncomputable def R (k : ℕ) : ℕ :=
  Nat.find (ramsey_exists k)

/-- R(k) is well-defined: the property holds for n = R(k) -/
theorem R_spec (k : ℕ) : ∀ coloring : EdgeColoring (Fin (R k)), HasMonochromaticClique coloring k :=
  Nat.find_spec (ramsey_exists k)

/-
## Known Bounds

The Erdős-Szekeres bounds and Spencer's improvement.
-/

/-- Erdős-Szekeres upper bound: R(k) ≤ C(2k-2, k-1) -/
axiom erdos_szekeres_upper :
  ∀ k ≥ 2, R k ≤ Nat.choose (2*k - 2) (k - 1)

/-- Asymptotic form of upper bound: R(k) ≤ 4^k / √(πk) · (1 + o(1)) -/
/-- Erdős-Szekeres lower bound from probabilistic method -/
/-- Spencer's improved lower bound constant: √2/e -/
axiom spencer_lower_bound :
  ∀ ε > 0, ∃ K : ℕ, ∀ k ≥ K,
    (R k : ℝ) ≥ (Real.sqrt 2 / Real.exp 1 - ε) * k * 2^(k/2 : ℝ)

/-
## The Conjecture

The central open problem: R(k) grows faster than k · 2^{k/2}.
-/

/-- The normalized ratio R(k) / (k · 2^{k/2}) -/
noncomputable def ramseyRatio (k : ℕ) : ℝ :=
  (R k : ℝ) / (k * 2^(k/2 : ℝ))

/-- Erdős's conjecture: the ratio tends to infinity -/
def erdos1029Conjecture : Prop :=
  Tendsto ramseyRatio atTop atTop

/-- Equivalent formulation: for every M, ratio eventually exceeds M -/
def erdos1029ConjectureAlt : Prop :=
  ∀ M : ℝ, ∃ K : ℕ, ∀ k ≥ K, ramseyRatio k > M

/-- The two formulations are equivalent -/
theorem conjecture_equiv : erdos1029Conjecture ↔ erdos1029ConjectureAlt := by
  constructor
  · intro h M
    rw [Tendsto, Filter.map_atTop_atTop] at h
    obtain ⟨K, hK⟩ := h M
    exact ⟨K, fun k hk => hK k hk⟩
  · intro h
    rw [Tendsto, Filter.map_atTop_atTop]
    intro M
    obtain ⟨K, hK⟩ := h M
    exact ⟨K, fun k hk => le_of_lt (hK k hk)⟩

/-
## Lower Bound is Not Tight

What we know: the ratio is bounded below, but possibly not above.
-/

/-- The ratio is bounded below by Spencer's constant -/
/-- If conjecture is false, ratio is bounded -/
def conjectureNegation : Prop :=
  ∃ M : ℝ, ∀ k : ℕ, ramseyRatio k ≤ M

/-- Negation equivalence: the conjecture fails iff the ratio is bounded -/
/-
## Small Values

Known exact values of Ramsey numbers.
-/

/-- R(1) = 1 (trivial) -/
/-- R(2) = 2 (need 2 vertices for an edge) -/
/-- R(3) = 6 (classical result) -/
axiom R_3 : R 3 = 6

/-- R(4) = 18 (Greenwood-Gleason 1955) -/
axiom R_4 : R 4 = 18

/-- R(5) is between 43 and 48 -/
/-
## Ratio Values for Small k

The ratio for known Ramsey numbers.
-/

/-- Ratio at k=3: R(3)/(3·2^{3/2}) = 6/(3·2√2) ≈ 0.707 -/
theorem ratio_3 : ramseyRatio 3 = 6 / (3 * 2^(3/2 : ℝ)) := by
  simp only [ramseyRatio, R_3]
  ring

/-- Ratio at k=4: R(4)/(4·2^2) = 18/16 = 1.125 -/
theorem ratio_4 : ramseyRatio 4 = 18 / (4 * 2^(2 : ℝ)) := by
  simp only [ramseyRatio, R_4]
  ring

/-
## The Prize Problem

Erdős offered $100 for proof, $1000 for disproof.
-/

/-- The main open question -/
def erdos1029OpenProblem : Prop := erdos1029Conjecture

#check R
#check erdos1029Conjecture
#check spencer_lower_bound
#check erdos_szekeres_upper
