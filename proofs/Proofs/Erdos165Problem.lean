/-
  Erdős Problem #165: Asymptotic Formula for R(3,k)

  Source: https://erdosproblems.com/165
  Prize: $250 (claimed by Kim 1995 for establishing the asymptotic order)
  Status: SOLVED (asymptotic order determined; exact constant conjectured but unproved)

  Statement:
  Give an asymptotic formula for R(3,k).

  Answer: R(3,k) = Θ(k²/log k), with tight bounds:
    - Upper: R(3,k) ≤ (1 + o(1)) · k²/log k  [Shearer 1983]
    - Lower: R(3,k) ≥ (1/2 - o(1)) · k²/log k  [Hefty-Horn-King-Pfender 2025]

  Timeline of Lower Bounds:
    - Kim (1995): R(3,k) ≥ c · k²/log k for some c > 0 (breakthrough; c ≥ 1/162)
    - Bohman-Keevash (2021): c ≥ 1/4
    - Pontiveros-Griffiths-Morris (2020): c ≥ 1/4  (independently)
    - Campos-Jenssen-Michelen-Sahasrabudhe (2025): c ≥ 1/3
    - Hefty-Horn-King-Pfender (2025): c ≥ 1/2  (current record)

  Open Problem: Determine the exact constant c in R(3,k) ~ c · k²/log k.
  Conjecture: c = 1/2.

  References:
    [AKS80] Ajtai, Komlós, Szemerédi, "A note on Ramsey numbers" (1980)
    [Sh83]  Shearer, "A note on the independence number of triangle-free graphs" (1983)
    [Ki95]  Kim, "The Ramsey number R(3,t) has order of magnitude t²/log t" (1995)
    [BK21]  Bohman-Keevash, "The early evolution of the H-free process" (2021)
    [CJMS25] Campos-Jenssen-Michelen-Sahasrabudhe, "A new lower bound for R(3,k)" (2025)
    [HHKP25] Hefty-Horn-King-Pfender, "Improving R(3,k) in just two bites" (2025)
-/

import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Basic

open Real

namespace Erdos165

/- ## Part I: Ramsey Numbers — Basic Definitions -/

/-- The Ramsey number R(m,n): the minimum N such that any 2-coloring of the
    edges of the complete graph K_N contains a red clique of size m or a blue
    clique of size n.

    For R(3,k): minimum N such that any graph on N vertices contains a
    triangle (K₃) or an independent set of size k.

    Axiomatized: computing exact Ramsey numbers requires extensive combinatorics
    beyond current Mathlib. -/
axiom ramseyNumber (m n : ℕ) : ℕ

/-- Symmetry: R(m,n) = R(n,m) — swapping colors swaps clique sizes. -/
axiom ramseyNumber_symm (m n : ℕ) : ramseyNumber m n = ramseyNumber n m

/-- Ramsey recurrence: R(m,n) ≤ R(m-1,n) + R(m,n-1).
    Follows from a greedy vertex-coloring argument. -/
axiom ramseyNumber_recurrence (m n : ℕ) (hm : m ≥ 2) (hn : n ≥ 2) :
    ramseyNumber m n ≤ ramseyNumber (m - 1) n + ramseyNumber m (n - 1)

/-- R(3,k): the Ramsey number for triangles vs independent sets of size k. -/
noncomputable def R3 (k : ℕ) : ℕ := ramseyNumber 3 k

/-- Small values: R(3,3)=6, R(3,4)=9, R(3,5)=14, R(3,6)=18, R(3,7)=23,
    R(3,8)=28, R(3,9)=36 — all known exactly. -/
axiom R3_small_values : R3 3 = 6 ∧ R3 4 = 9 ∧ R3 5 = 14 ∧
    R3 6 = 18 ∧ R3 7 = 23 ∧ R3 8 = 28 ∧ R3 9 = 36

/- ## Part II: Upper Bound — Shearer (1983) -/

/-- **Ajtai-Komlós-Szemerédi (1980)**: R(3,k) = O(k²/log k).
    First proof of the upper bound order. Shearer later found the tight constant. -/
axiom aks_upper_bound :
    ∃ C : ℝ, C > 0 ∧ ∃ k₀ : ℕ, ∀ k : ℕ, k ≥ k₀ →
      (R3 k : ℝ) ≤ C * k^2 / log k

/-- **Shearer's Theorem (1983)**: R(3,k) ≤ (1 + o(1)) · k² / log k.

    Proof idea: Shearer showed that any triangle-free graph on n vertices has
    independence number α(G) ≥ (1 + o(1)) · n · log n / ⌊n/α(G)⌋,
    leading to the tight upper bound on R(3,k).

    This is essentially optimal: the upper bound constant 1 matches the
    conjectured true constant (1/2) only in order of magnitude. -/
axiom shearer_upper_bound :
    ∀ ε > 0, ∃ k₀ : ℕ, ∀ k : ℕ, k ≥ k₀ →
      (R3 k : ℝ) ≤ (1 + ε) * k^2 / log k

/- ## Part III: Lower Bounds — History of Constant c -/

/-- **Kim (1995)**: R(3,k) = Ω(k²/log k). The breakthrough result establishing
    the correct order of magnitude. Kim used the semi-random "triangle-free process":
    add edges one at a time uniformly at random, rejecting edges that create triangles.
    This produces triangle-free graphs with small independence number.

    The constant Kim obtained was c ≥ 1/162. The $250 Erdős prize was claimed
    for establishing the order of magnitude. -/
axiom kim_lower_bound :
    ∀ ε > 0, ∃ k₀ : ℕ, ∀ k : ℕ, k ≥ k₀ →
      (R3 k : ℝ) ≥ (1/162 - ε) * k^2 / log k

/-- **Bohman-Keevash (2021)** and **Pontiveros-Griffiths-Morris (2020)** independently:
    c ≥ 1/4. Both groups gave a sharper analysis of the triangle-free process.
    This improved the constant from 1/162 to 1/4, giving c = 1/4 simultaneously. -/
axiom bk_pgm_bound :
    ∀ ε > 0, ∃ k₀ : ℕ, ∀ k : ℕ, k ≥ k₀ →
      (R3 k : ℝ) ≥ (1/4 - ε) * k^2 / log k

/-- **Campos-Jenssen-Michelen-Sahasrabudhe (2025)**: c ≥ 1/3.
    A new approach using a "refined semi-random" method, pushing the constant from
    1/4 to 1/3. This paper also conjectured c = 1/2. -/
axiom cjms_bound :
    ∀ ε > 0, ∃ k₀ : ℕ, ∀ k : ℕ, k ≥ k₀ →
      (R3 k : ℝ) ≥ (1/3 - ε) * k^2 / log k

/-- **Hefty-Horn-King-Pfender (2025)**: c ≥ 1/2. Current best lower bound.
    Title: "Improving R(3,k) in just two bites."
    The paper provides two iterative improvements to the triangle-free process
    analysis, reaching c = 1/2. This matches the conjectured exact constant. -/
axiom hhkp_bound :
    ∀ ε > 0, ∃ k₀ : ℕ, ∀ k : ℕ, k ≥ k₀ →
      (R3 k : ℝ) ≥ (1/2 - ε) * k^2 / log k

/- ## Part IV: Main Asymptotic Result -/

/-- **Current best two-sided bounds** (combining Shearer and HHKP):
    For any ε > 0, for sufficiently large k:
      (1/2 - ε) · k²/log k ≤ R(3,k) ≤ (1 + ε) · k²/log k.

    This is a proved theorem, following from hhkp_bound and shearer_upper_bound. -/
theorem current_best_bounds :
    ∀ ε > 0, ∃ k₀ : ℕ, ∀ k : ℕ, k ≥ k₀ →
      (1/2 - ε) * k^2 / log k ≤ R3 k ∧ (R3 k : ℝ) ≤ (1 + ε) * k^2 / log k := by
  intro ε hε
  obtain ⟨k₁, hk₁⟩ := hhkp_bound ε hε
  obtain ⟨k₂, hk₂⟩ := shearer_upper_bound ε hε
  exact ⟨max k₁ k₂, fun k hk =>
    ⟨hk₁ k (le_of_max_le_left hk), hk₂ k (le_of_max_le_right hk)⟩⟩

/-- **Erdős Problem #165 — Main Theorem**:
    R(3,k) = Θ(k²/log k).

    There exist positive constants c₁, c₂ such that for all sufficiently large k:
      c₁ · k²/log k ≤ R(3,k) ≤ c₂ · k²/log k.

    Explicit witnesses: c₁ = 1/4 (from HHKP with ε = 1/4) and c₂ = 2
    (from Shearer with ε = 1). -/
theorem erdos_165 :
    ∃ c₁ c₂ : ℝ, c₁ > 0 ∧ c₂ > 0 ∧
      ∃ k₀ : ℕ, ∀ k : ℕ, k ≥ k₀ →
        c₁ * k^2 / log k ≤ R3 k ∧ (R3 k : ℝ) ≤ c₂ * k^2 / log k := by
  use 1/4, 2
  refine ⟨by norm_num, by norm_num, ?_⟩
  obtain ⟨k₀, hk₀⟩ := current_best_bounds (1/4) (by norm_num)
  -- Past `max k₀ 2` we also have `k ≥ 2`, hence `log k > 0` and `k²/log k ≥ 0`;
  -- this nonnegativity is what lets us widen the constant `5/4` up to `2`.
  refine ⟨max k₀ 2, fun k hk => ?_⟩
  have hk0 : k ≥ k₀ := le_of_max_le_left hk
  have hk2 : k ≥ 2 := le_of_max_le_right hk
  have h2k : (2:ℝ) ≤ (k:ℝ) := by exact_mod_cast hk2
  have hlog : 0 < log k := Real.log_pos (by linarith)
  have hatom : 0 ≤ (k:ℝ)^2 / log k := le_of_lt (div_pos (by positivity) hlog)
  obtain ⟨hl, hu⟩ := hk₀ k hk0
  rw [mul_div_assoc] at hl hu
  refine ⟨?_, ?_⟩
  · rw [mul_div_assoc]; linarith
  · rw [mul_div_assoc]; linarith [hatom]

/- ## Part V: The Triangle-Free Process -/

/-
**The Triangle-Free Process** (underlying Kim 1995 and all later improvements):

Start with an empty graph on n vertices. At each step, choose a random edge
uniformly at random that does not create a triangle, and add it. Continue until
no such edge exists.

The resulting graph G satisfies:
  1. G is triangle-free by construction.
  2. G is "saturated" — adding any edge creates a triangle.
  3. The independence number α(G) is small (roughly √(n log n)).

Kim proved: for n = R(3,k), the process gives α(G) < k, which is a contradiction
unless R(3,k) = Ω(k²/log k).

The key difficulty: analyzing the process requires tracking the "codegree" of pairs
of vertices (how many common neighbors they have), which evolves as edges are added.
Kim used martingale concentration inequalities; later authors used differential
equations and more refined methods.
-/

/- ## Part VI: Conjectures and Open Questions -/

/-- **Main Conjecture** (supported by CJMS 2025 and HHKP 2025):
    R(3,k) ~ (1/2) · k² / log k.

    Equivalently, c = 1/2 is the exact constant. The upper bound constant is 1
    (from Shearer), so this would mean the true ratio converges to 1/2, leaving
    a factor of 2 gap in the constants. -/
def mainConjecture : Prop :=
    ∀ ε > 0, ∃ k₀ : ℕ, ∀ k : ℕ, k ≥ k₀ →
      (1/2 - ε) * k^2 / log k ≤ R3 k ∧ (R3 k : ℝ) ≤ (1/2 + ε) * k^2 / log k

/-- The PGM Conjecture (Pontiveros-Griffiths-Morris 2020):
    R(3,k) ~ (1/4) · k²/log k.

    This was the leading conjecture before CJMS and HHKP 2025.
    It has been superseded: since R(3,k) ≥ (1/2 - o(1))k²/log k (HHKP),
    the PGM upper bound (1/4 + ε)k²/log k is now known to be wrong. -/
def pgmConjecture : Prop :=
    ∀ ε > 0, ∃ k₀ : ℕ, ∀ k : ℕ, k ≥ k₀ →
      (1/4 - ε) * k^2 / log k ≤ R3 k ∧ (R3 k : ℝ) ≤ (1/4 + ε) * k^2 / log k

/-
**Why the PGM Conjecture is Refuted**

The PGM conjecture claims R(3,k) ≤ (1/4 + ε)k²/log k for large k.
But HHKP proved R(3,k) ≥ (1/2 - ε)k²/log k.

For large k (where log k > 0) and ε = 1/16:
  HHKP: R(3,k) ≥ (7/16)k²/log k
  PGM:  R(3,k) ≤ (5/16)k²/log k
These are incompatible since 7/16 > 5/16 and k²/log k > 0.
Therefore ¬pgmConjecture follows from hhkp_bound. The formal proof is given
below (`pgm_conjecture_refuted`); its core is the axiom-free incompatibility
lemma `asymptotic_constant_le`, which handles the k²/log k positivity argument
once and for all via `div_pos` and `Real.log_pos`.
-/

/-- **Axiom-free incompatibility lemma.** Suppose a real sequence `f` is, for
    *every* `ε > 0`, eventually bounded below by `(a - ε)·k²/log k` and eventually
    bounded above by `(b + ε)·k²/log k`. Then necessarily `a ≤ b`.

    In words: two asymptotic constants that simultaneously lower- and upper-bound
    the same sequence (to first order, in the `k²/log k` scale) cannot be in the
    wrong order. This is the structural fact underlying every "conjectured
    constant refuted by a better bound" argument for `R(3,k)`. The proof contains
    no Ramsey theory and no axioms: it is pure real analysis.

    Strategy: if `b < a`, take `ε = (a-b)/4`, so `a - ε > b + ε`. Pick any
    `k ≥ 2` past both thresholds; then `k²/log k > 0`, and the two bounds force
    `(a - ε)·k²/log k ≤ (b + ε)·k²/log k`, i.e. `a - ε ≤ b + ε`, contradiction. -/
theorem asymptotic_constant_le
    (f : ℕ → ℝ) (a b : ℝ)
    (lower : ∀ ε > 0, ∃ k₀ : ℕ, ∀ k : ℕ, k ≥ k₀ → (a - ε) * k^2 / log k ≤ f k)
    (upper : ∀ ε > 0, ∃ k₀ : ℕ, ∀ k : ℕ, k ≥ k₀ → f k ≤ (b + ε) * k^2 / log k) :
    a ≤ b := by
  by_contra h
  push_neg at h          -- h : b < a
  set ε := (a - b) / 4 with hε_def
  have hε : ε > 0 := by rw [hε_def]; linarith
  obtain ⟨k₁, hk₁⟩ := lower ε hε
  obtain ⟨k₂, hk₂⟩ := upper ε hε
  -- a witness index past both thresholds and ≥ 2 (so log k > 0 and k² > 0)
  set k := max (max k₁ k₂) 2 with hk_def
  have hk1 : k ≥ k₁ := le_trans (le_max_left _ _) (le_max_left _ _)
  have hk2 : k ≥ k₂ := le_trans (le_max_right _ _) (le_max_left _ _)
  have hk_ge2 : k ≥ 2 := le_max_right _ _
  have h2k : (2:ℝ) ≤ (k:ℝ) := by exact_mod_cast hk_ge2
  have hkpos : (0:ℝ) < (k:ℝ) := by linarith
  have h1k : (1:ℝ) < (k:ℝ) := by linarith
  have hlogpos : 0 < log k := Real.log_pos h1k
  have hksq : (0:ℝ) < (k:ℝ)^2 := pow_pos hkpos 2
  have hg : 0 < (k:ℝ)^2 / log k := div_pos hksq hlogpos
  -- chain the two bounds at this k
  have hcomb : (a - ε) * k^2 / log k ≤ (b + ε) * k^2 / log k :=
    le_trans (hk₁ k hk1) (hk₂ k hk2)
  rw [mul_div_assoc, mul_div_assoc] at hcomb
  have hle : a - ε ≤ b + ε := le_of_mul_le_mul_right hcomb hg
  -- a - ε ≤ b + ε with ε = (a-b)/4 forces a ≤ b, contradicting b < a
  rw [hε_def] at hle
  linarith

/-- **No asymptotic upper constant below `1/2`.** If `R(3,k) ≤ (b + ε)·k²/log k`
    holds eventually for every `ε > 0`, then `b ≥ 1/2`. This is the HHKP lower
    bound (`c ≥ 1/2`) phrased as an obstruction: any *valid* first-order upper
    constant for `R(3,k)` is at least `1/2`. -/
theorem R3_upper_constant_ge_half (b : ℝ)
    (hb : ∀ ε > 0, ∃ k₀ : ℕ, ∀ k : ℕ, k ≥ k₀ →
        (R3 k : ℝ) ≤ (b + ε) * k^2 / log k) :
    (1:ℝ)/2 ≤ b := by
  refine asymptotic_constant_le (fun k => (R3 k : ℝ)) (1/2) b ?_ hb
  intro ε hε
  obtain ⟨k₀, hk₀⟩ := hhkp_bound ε hε
  exact ⟨k₀, fun k hk => hk₀ k hk⟩

/-- **PGM Conjecture refuted.** The conjecture `R(3,k) ~ (1/4)·k²/log k`
    (Pontiveros–Griffiths–Morris 2020) is false. Its upper half asserts an
    asymptotic constant `1/4`, but `R3_upper_constant_ge_half` forces any valid
    upper constant to be at least `1/2`, and `1/2 ≤ 1/4` is absurd. The only
    Ramsey input is `hhkp_bound`; the rest is the axiom-free lemma above. -/
theorem pgm_conjecture_refuted : ¬ pgmConjecture := by
  intro h
  have hupper : ∀ ε > 0, ∃ k₀ : ℕ, ∀ k : ℕ, k ≥ k₀ →
      (R3 k : ℝ) ≤ (1/4 + ε) * k^2 / log k := by
    intro ε hε
    obtain ⟨k₀, hk₀⟩ := h ε hε
    exact ⟨k₀, fun k hk => (hk₀ k hk).2⟩
  have : (1:ℝ)/2 ≤ 1/4 := R3_upper_constant_ge_half (1/4) hupper
  norm_num at this

/-- **No asymptotic lower constant above `1`.**  The mirror of
    `R3_upper_constant_ge_half`: if `R(3,k) ≥ (a - ε)·k²/log k` holds eventually for
    *every* `ε > 0`, then `a ≤ 1`.  This is Shearer's upper bound (`c ≤ 1`) phrased as an
    obstruction — any *valid* first-order lower constant for `R(3,k)` is at most `1`.  The
    only Ramsey input is `shearer_upper_bound`; the rest is the axiom-free
    `asymptotic_constant_le`. -/
theorem R3_lower_constant_le_one (a : ℝ)
    (ha : ∀ ε > 0, ∃ k₀ : ℕ, ∀ k : ℕ, k ≥ k₀ →
        (a - ε) * k^2 / log k ≤ (R3 k : ℝ)) :
    a ≤ 1 := by
  refine asymptotic_constant_le (fun k => (R3 k : ℝ)) a 1 ha ?_
  intro ε hε
  obtain ⟨k₀, hk₀⟩ := shearer_upper_bound ε hε
  exact ⟨k₀, fun k hk => hk₀ k hk⟩

/-- A conjectured exact asymptotic constant `c` for `R(3,k)`, i.e. `R(3,k) ~ c·k²/log k`:
    `(c-ε)·k²/log k ≤ R(3,k) ≤ (c+ε)·k²/log k` eventually for every `ε > 0`.  This is the
    common shape of `mainConjecture` (`c = 1/2`) and `pgmConjecture` (`c = 1/4`). -/
def constantConjecture (c : ℝ) : Prop :=
    ∀ ε > 0, ∃ k₀ : ℕ, ∀ k : ℕ, k ≥ k₀ →
      (c - ε) * k^2 / log k ≤ R3 k ∧ (R3 k : ℝ) ≤ (c + ε) * k^2 / log k

/-- **Any conjectured constant `> 1` is refuted by Shearer's upper bound.**  The symmetric
    companion to `pgm_conjecture_refuted`: whereas the PGM constant `1/4` is ruled out from
    *below* (HHKP forces the constant `≥ 1/2`), any constant exceeding `1` is ruled out from
    *above* — its lower half would assert a valid lower constant `> 1`, contradicting
    `R3_lower_constant_le_one`.  Together with `pgm_conjecture_refuted` this pins the exact
    constant to the interval `[1/2, 1]`: no conjecture with constant `< 1/2` or `> 1` can
    hold.  The only Ramsey input is `shearer_upper_bound`. -/
theorem constantConjecture_refuted_of_one_lt (c : ℝ) (hc : 1 < c) :
    ¬ constantConjecture c := by
  intro h
  have hlower : ∀ ε > 0, ∃ k₀ : ℕ, ∀ k : ℕ, k ≥ k₀ →
      (c - ε) * k^2 / log k ≤ (R3 k : ℝ) := by
    intro ε hε
    obtain ⟨k₀, hk₀⟩ := h ε hε
    exact ⟨k₀, fun k hk => (hk₀ k hk).1⟩
  have : c ≤ 1 := R3_lower_constant_le_one c hlower
  linarith

/-- **Any conjectured constant `< 1/2` is refuted by the HHKP lower bound.**  The general
    form of `pgm_conjecture_refuted` (the PGM constant `1/4` is just the `c = 1/4` instance):
    a conjecture `R(3,k) ~ c·k²/log k` with `c < 1/2` has an upper half asserting a valid
    first-order upper constant `c`, but `R3_upper_constant_ge_half` forces every valid upper
    constant to be `≥ 1/2`.  The only Ramsey input is `hhkp_bound`. -/
theorem constantConjecture_refuted_of_lt_half (c : ℝ) (hc : c < 1/2) :
    ¬ constantConjecture c := by
  intro h
  have hupper : ∀ ε > 0, ∃ k₀ : ℕ, ∀ k : ℕ, k ≥ k₀ →
      (R3 k : ℝ) ≤ (c + ε) * k^2 / log k := by
    intro ε hε
    obtain ⟨k₀, hk₀⟩ := h ε hε
    exact ⟨k₀, fun k hk => (hk₀ k hk).2⟩
  have : (1:ℝ)/2 ≤ c := R3_upper_constant_ge_half c hupper
  linarith

/-- **The exact constant, if it exists, lies in `[1/2, 1]`.**  Unifying headline of the
    two-sided obstruction: any conjectured exact asymptotic constant `c` for `R(3,k)`
    (`constantConjecture c`) must satisfy `1/2 ≤ c ≤ 1`.  The lower fence is HHKP
    (`constantConjecture_refuted_of_lt_half`), the upper fence is Shearer
    (`constantConjecture_refuted_of_one_lt`); the PGM value `1/4` is excluded by the former
    and Erdős's conjectured `1/2` sits exactly on the lower fence, hence survives.  Both
    Ramsey inputs (`hhkp_bound`, `shearer_upper_bound`) are used; no new axioms. -/
theorem constantConjecture_forces_bracket (c : ℝ) (h : constantConjecture c) :
    (1:ℝ)/2 ≤ c ∧ c ≤ 1 := by
  refine ⟨?_, ?_⟩
  · by_contra hlt
    push_neg at hlt
    exact constantConjecture_refuted_of_lt_half c hlt h
  · by_contra hgt
    push_neg at hgt
    exact constantConjecture_refuted_of_one_lt c hgt h

/-- **Uniqueness of the exact asymptotic constant.**  At most one constant can be the
    first-order asymptotic constant of `R(3,k)`: if both `constantConjecture c₁` and
    `constantConjecture c₂` hold, then `c₁ = c₂`.  A two-sided application of the axiom-free
    `asymptotic_constant_le` — pairing `c₁`'s lower bound with `c₂`'s upper bound gives
    `c₁ ≤ c₂`, and the symmetric pairing gives `c₂ ≤ c₁`.  So the family `constantConjecture c`
    is a genuine *singleton predicate*: at most one member can hold, and (with
    `constantConjecture_forces_bracket`) that member's constant lies in `[1/2, 1]`.  In
    particular `mainConjecture` (`c = 1/2`) and `pgmConjecture` (`c = 1/4`) are mutually
    exclusive.  No Ramsey axioms are used. -/
theorem constantConjecture_unique (c₁ c₂ : ℝ)
    (h₁ : constantConjecture c₁) (h₂ : constantConjecture c₂) :
    c₁ = c₂ := by
  have h12 : c₁ ≤ c₂ :=
    asymptotic_constant_le (fun k => (R3 k : ℝ)) c₁ c₂
      (fun ε hε => by obtain ⟨k₀, hk₀⟩ := h₁ ε hε; exact ⟨k₀, fun k hk => (hk₀ k hk).1⟩)
      (fun ε hε => by obtain ⟨k₀, hk₀⟩ := h₂ ε hε; exact ⟨k₀, fun k hk => (hk₀ k hk).2⟩)
  have h21 : c₂ ≤ c₁ :=
    asymptotic_constant_le (fun k => (R3 k : ℝ)) c₂ c₁
      (fun ε hε => by obtain ⟨k₀, hk₀⟩ := h₂ ε hε; exact ⟨k₀, fun k hk => (hk₀ k hk).1⟩)
      (fun ε hε => by obtain ⟨k₀, hk₀⟩ := h₁ ε hε; exact ⟨k₀, fun k hk => (hk₀ k hk).2⟩)
  linarith

/- ## Part VII: Related Problems -/

/-
**Related Erdős Problems:**

- **Erdős #544**: Determine R(k,k) (diagonal Ramsey numbers). Known only that
  2^(k/2) ≤ R(k,k) ≤ 4^k. A recent breakthrough (2023) by Campos-Griffiths-
  Morris-Sahasrabudhe improved the upper bound exponentially.

- **Erdős #986**: Determine R(s,k) for fixed s ≥ 4 and growing k.
  For fixed s, R(s,k) = Θ(k^((s+1)/2) / (log k)^((s-1)/2)) is conjectured but
  not proved for s ≥ 5.

- **Triangle-free Ramsey multiplicity**: How many triangles must appear in a
  2-coloring of K_n if the graph is not triangle-free?
-/

end Erdos165
