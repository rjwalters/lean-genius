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

/-- **`mainConjecture` is the `constantConjecture` at `c = 1/2`.**  The Erdős main
    conjecture `R(3,k) ~ (1/2)·k²/log k` (`mainConjecture`) is definitionally the
    generic exact-constant conjecture instantiated at `c = 1/2`.  This wires the
    standalone `mainConjecture` def into the general `constantConjecture` machinery
    (`_unique`, `_forces_bracket`, the refutation lemmas). -/
theorem mainConjecture_iff_constant : mainConjecture ↔ constantConjecture (1/2) :=
  Iff.rfl

/-- **`pgmConjecture` is the `constantConjecture` at `c = 1/4`.**  The PGM conjecture
    `R(3,k) ~ (1/4)·k²/log k` (`pgmConjecture`) is definitionally the generic
    exact-constant conjecture at `c = 1/4`, connecting it to the general machinery. -/
theorem pgmConjecture_iff_constant : pgmConjecture ↔ constantConjecture (1/4) :=
  Iff.rfl

/-- **The main and PGM conjectures are mutually exclusive.**  `mainConjecture`
    (`c = 1/2`) and `pgmConjecture` (`c = 1/4`) cannot both hold: they assert two
    different exact asymptotic constants for the *same* sequence `R(3,k)`, and
    `constantConjecture_unique` forces any two such constants to coincide, whereas
    `1/2 ≠ 1/4`.  This is the machine-checked form of the "in particular … mutually
    exclusive" remark in `constantConjecture_unique`'s docstring, and — unlike
    `pgm_conjecture_refuted` (which invokes the Ramsey bound `hhkp_bound`) — it uses
    *no* Ramsey input at all: it is a purely structural incompatibility of two
    exact-constant claims, holding for any sequence whatsoever. -/
theorem main_pgm_mutually_exclusive : ¬ (mainConjecture ∧ pgmConjecture) := by
  rintro ⟨hm, hp⟩
  have h : (1 : ℝ) / 2 = 1 / 4 :=
    constantConjecture_unique (1/2) (1/4)
      (mainConjecture_iff_constant.mp hm) (pgmConjecture_iff_constant.mp hp)
  norm_num at h

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

/- ## Part VIII: Minimality of the axiom set

The file declares ten axioms, but four of the six *analytic* ones carry no logical
content beyond the two sharpest bounds.  The historical lower bounds form an increasing
chain of leading constants `1/162 → 1/4 → 1/3 → 1/2`, and a first-order lower bound of
the shape `R(3,k) ≥ (c−ε)·k²/log k` is monotone in `c`: a bound with the larger constant
formally implies every bound with a smaller one.  Hence Kim, Bohman–Keevash/PGM and CJMS
are all consequences of `hhkp_bound`.  Dually, the AKS `O(k²/log k)` upper bound is the
`ε = 1` instance of Shearer's sharper `(1+o(1))` bound.  So the genuine analytic
assumptions are exactly `hhkp_bound` and `shearer_upper_bound` (atop the Ramsey-number
scaffolding); the other four are documentation of the historical record, not independent
hypotheses.  Nothing below introduces a new axiom. -/

/-- **Monotone weakening of a first-order lower bound.**  If `R(3,k) ≥ (a−ε)·k²/log k`
    holds eventually for every `ε > 0`, then the same shape holds with any *smaller* leading
    constant `a' ≤ a`.  The mechanism is the eventual nonnegativity of the atom `k²/log k`
    (for `k ≥ 2`, where `log k > 0`), which transports `a'−ε ≤ a−ε` through the
    multiplication.  This is the engine making every pre-HHKP lower bound a formal
    consequence of the strongest one. -/
theorem lower_bound_mono {a a' : ℝ} (haa : a' ≤ a)
    (h : ∀ ε > 0, ∃ k₀ : ℕ, ∀ k : ℕ, k ≥ k₀ →
        (R3 k : ℝ) ≥ (a - ε) * k^2 / log k) :
    ∀ ε > 0, ∃ k₀ : ℕ, ∀ k : ℕ, k ≥ k₀ →
        (R3 k : ℝ) ≥ (a' - ε) * k^2 / log k := by
  intro ε hε
  obtain ⟨k₀, hk₀⟩ := h ε hε
  refine ⟨max k₀ 2, fun k hk => ?_⟩
  have hk0 : k ≥ k₀ := le_of_max_le_left hk
  have hk2 : k ≥ 2 := le_of_max_le_right hk
  have h2k : (2:ℝ) ≤ (k:ℝ) := by exact_mod_cast hk2
  have hlog : 0 < log k := Real.log_pos (by linarith)
  have hatom : 0 ≤ (k:ℝ)^2 / log k := le_of_lt (div_pos (by positivity) hlog)
  have hmono : (a' - ε) * k^2 / log k ≤ (a - ε) * k^2 / log k := by
    rw [mul_div_assoc, mul_div_assoc]
    exact mul_le_mul_of_nonneg_right (by linarith) hatom
  exact le_trans hmono (hk₀ k hk0)

/-- **HHKP subsumes CJMS (`1/3`).**  The Campos–Jenssen–Michelen–Sahasrabudhe lower bound is a
    formal consequence of `hhkp_bound`, since `1/3 ≤ 1/2`. -/
theorem hhkp_subsumes_cjms :
    ∀ ε > 0, ∃ k₀ : ℕ, ∀ k : ℕ, k ≥ k₀ →
        (R3 k : ℝ) ≥ (1/3 - ε) * k^2 / log k :=
  lower_bound_mono (by norm_num) hhkp_bound

/-- **HHKP subsumes Bohman–Keevash / PGM (`1/4`).**  Consequence of `hhkp_bound`, `1/4 ≤ 1/2`. -/
theorem hhkp_subsumes_bk_pgm :
    ∀ ε > 0, ∃ k₀ : ℕ, ∀ k : ℕ, k ≥ k₀ →
        (R3 k : ℝ) ≥ (1/4 - ε) * k^2 / log k :=
  lower_bound_mono (by norm_num) hhkp_bound

/-- **HHKP subsumes Kim (`1/162`).**  Consequence of `hhkp_bound`, `1/162 ≤ 1/2`. -/
theorem hhkp_subsumes_kim :
    ∀ ε > 0, ∃ k₀ : ℕ, ∀ k : ℕ, k ≥ k₀ →
        (R3 k : ℝ) ≥ (1/162 - ε) * k^2 / log k :=
  lower_bound_mono (by norm_num) hhkp_bound

/-- **Shearer subsumes AKS.**  The AKS upper bound (`R(3,k) = O(k²/log k)` for *some* `C>0`) is
    the `ε = 1` instance of Shearer's sharper `(1+o(1))` bound: take `C = 1+1 = 2`. -/
theorem shearer_subsumes_aks :
    ∃ C : ℝ, C > 0 ∧ ∃ k₀ : ℕ, ∀ k : ℕ, k ≥ k₀ →
      (R3 k : ℝ) ≤ C * k^2 / log k :=
  ⟨1 + 1, by norm_num, shearer_upper_bound 1 (by norm_num)⟩

/-- **Four of the ten axioms are logically redundant.**  Every pre-HHKP lower bound (Kim
    `1/162`, Bohman–Keevash / PGM `1/4`, CJMS `1/3`) is a consequence of `hhkp_bound` (`1/2`),
    and the AKS upper bound is a consequence of `shearer_upper_bound`.  So the effective
    analytic assumption set is just `{hhkp_bound, shearer_upper_bound}`: the exact statements of
    `kim_lower_bound`, `bk_pgm_bound`, `cjms_bound` and `aks_upper_bound` are all *proved* below
    without invoking those four axioms. -/
theorem historical_bounds_redundant :
    (∀ ε > 0, ∃ k₀ : ℕ, ∀ k : ℕ, k ≥ k₀ → (R3 k : ℝ) ≥ (1/162 - ε) * k^2 / log k) ∧
    (∀ ε > 0, ∃ k₀ : ℕ, ∀ k : ℕ, k ≥ k₀ → (R3 k : ℝ) ≥ (1/4 - ε) * k^2 / log k) ∧
    (∀ ε > 0, ∃ k₀ : ℕ, ∀ k : ℕ, k ≥ k₀ → (R3 k : ℝ) ≥ (1/3 - ε) * k^2 / log k) ∧
    (∃ C : ℝ, C > 0 ∧ ∃ k₀ : ℕ, ∀ k : ℕ, k ≥ k₀ → (R3 k : ℝ) ≤ C * k^2 / log k) :=
  ⟨hhkp_subsumes_kim, hhkp_subsumes_bk_pgm, hhkp_subsumes_cjms, shearer_subsumes_aks⟩

/- ## Part IX: The dual (upper-side) monotonicity, and general-sequence uniqueness

The subsumption chain above rests on `lower_bound_mono`: a first-order *lower* bound may be
weakened to any *smaller* leading constant.  The present section supplies the two structural
companions that the file was missing.

First, the exact mirror image, `upper_bound_mono`: a first-order *upper* bound
`R(3,k) ≤ (b+ε)·k²/log k` may be weakened to any *larger* leading constant `b' ≥ b`.  This is
precisely the widening performed by hand inside `erdos_165` (there the constant `5/4` was
opened up to `2`); here it is isolated as a reusable lemma.  Combined with Shearer it yields
`R3_upper_constant_of_one_le`: *every* `b ≥ 1` is a valid first-order upper constant for
`R(3,k)` — the exact dual of the `hhkp_subsumes_*` family.  Placing this beside
`R3_upper_constant_ge_half` (every valid upper constant is `≥ 1/2`) sandwiches the set of
valid asymptotic upper constants inside `[1/2, ∞)` while showing it contains `[1, ∞)`; the
residual window `[1/2, 1)` is exactly the file's quantitative ignorance about the true
constant.

Second, `asymptotic_constant_unique`: the R3-specific `constantConjecture_unique` is really an
instance of a statement about *any* real sequence `f` — at most one leading constant can
two-side pin it.  We record that general form (`constantConjecture_unique` is its `f = R3`
instance).  All three results are axiom-free: they use only `asymptotic_constant_le` and the
eventual positivity of `k²/log k`, no Ramsey input. -/

/-- **Monotone weakening of a first-order upper bound** (dual of `lower_bound_mono`).  If
    `R(3,k) ≤ (b+ε)·k²/log k` holds eventually for every `ε > 0`, then the same shape holds
    with any *larger* leading constant `b' ≥ b`.  The mechanism is identical to
    `lower_bound_mono`: the atom `k²/log k` is eventually nonnegative (for `k ≥ 2`), so
    `b+ε ≤ b'+ε` transports through the multiplication.  This isolates the widening step that
    `erdos_165` performs inline. -/
theorem upper_bound_mono {b b' : ℝ} (hbb : b ≤ b')
    (h : ∀ ε > 0, ∃ k₀ : ℕ, ∀ k : ℕ, k ≥ k₀ →
        (R3 k : ℝ) ≤ (b + ε) * k^2 / log k) :
    ∀ ε > 0, ∃ k₀ : ℕ, ∀ k : ℕ, k ≥ k₀ →
        (R3 k : ℝ) ≤ (b' + ε) * k^2 / log k := by
  intro ε hε
  obtain ⟨k₀, hk₀⟩ := h ε hε
  refine ⟨max k₀ 2, fun k hk => ?_⟩
  have hk0 : k ≥ k₀ := le_of_max_le_left hk
  have hk2 : k ≥ 2 := le_of_max_le_right hk
  have h2k : (2:ℝ) ≤ (k:ℝ) := by exact_mod_cast hk2
  have hlog : 0 < log k := Real.log_pos (by linarith)
  have hatom : 0 ≤ (k:ℝ)^2 / log k := le_of_lt (div_pos (by positivity) hlog)
  have hmono : (b + ε) * k^2 / log k ≤ (b' + ε) * k^2 / log k := by
    rw [mul_div_assoc, mul_div_assoc]
    exact mul_le_mul_of_nonneg_right (by linarith) hatom
  exact le_trans (hk₀ k hk0) hmono

/-- **Every constant `b ≥ 1` is a valid first-order upper constant for `R(3,k)`.**  The dual of
    the `hhkp_subsumes_*` family: whereas HHKP (`1/2`) forces every smaller constant to be a
    valid *lower* bound, Shearer (`1`) makes every *larger* constant a valid *upper* bound, via
    `upper_bound_mono`.  In particular `b = 2` recovers the upper witness used in `erdos_165`. -/
theorem R3_upper_constant_of_one_le (b : ℝ) (hb : 1 ≤ b) :
    ∀ ε > 0, ∃ k₀ : ℕ, ∀ k : ℕ, k ≥ k₀ →
        (R3 k : ℝ) ≤ (b + ε) * k^2 / log k :=
  upper_bound_mono hb shearer_upper_bound

/-- **Shearer subsumes the constant `2`.**  The `b = 2` instance of
    `R3_upper_constant_of_one_le`; it is the upper-side analogue of `hhkp_subsumes_bk_pgm`, and
    exactly the widened Shearer bound `erdos_165` uses as its `c₂ = 2` witness. -/
theorem shearer_subsumes_upper_two :
    ∀ ε > 0, ∃ k₀ : ℕ, ∀ k : ℕ, k ≥ k₀ →
        (R3 k : ℝ) ≤ (2 + ε) * k^2 / log k :=
  R3_upper_constant_of_one_le 2 (by norm_num)

/-- **Uniqueness of a first-order asymptotic constant, for an arbitrary sequence.**  The
    R3-specific `constantConjecture_unique` is the `f = fun k => (R3 k : ℝ)` instance of this:
    for *any* real sequence `f`, at most one leading constant can two-sidedly pin it in the
    `k²/log k` scale.  A two-sided application of the axiom-free `asymptotic_constant_le`,
    pairing each constant's lower half against the other's upper half.  No Ramsey input. -/
theorem asymptotic_constant_unique
    (f : ℕ → ℝ) (c₁ c₂ : ℝ)
    (h₁ : ∀ ε > 0, ∃ k₀ : ℕ, ∀ k : ℕ, k ≥ k₀ →
        (c₁ - ε) * k^2 / log k ≤ f k ∧ f k ≤ (c₁ + ε) * k^2 / log k)
    (h₂ : ∀ ε > 0, ∃ k₀ : ℕ, ∀ k : ℕ, k ≥ k₀ →
        (c₂ - ε) * k^2 / log k ≤ f k ∧ f k ≤ (c₂ + ε) * k^2 / log k) :
    c₁ = c₂ := by
  have h12 : c₁ ≤ c₂ :=
    asymptotic_constant_le f c₁ c₂
      (fun ε hε => by obtain ⟨k₀, hk₀⟩ := h₁ ε hε; exact ⟨k₀, fun k hk => (hk₀ k hk).1⟩)
      (fun ε hε => by obtain ⟨k₀, hk₀⟩ := h₂ ε hε; exact ⟨k₀, fun k hk => (hk₀ k hk).2⟩)
  have h21 : c₂ ≤ c₁ :=
    asymptotic_constant_le f c₂ c₁
      (fun ε hε => by obtain ⟨k₀, hk₀⟩ := h₂ ε hε; exact ⟨k₀, fun k hk => (hk₀ k hk).1⟩)
      (fun ε hε => by obtain ⟨k₀, hk₀⟩ := h₁ ε hε; exact ⟨k₀, fun k hk => (hk₀ k hk).2⟩)
  linarith

/- ## Part X: The conjecture reduces to the upper bound

The two-sided obstruction of Parts VI–IX pins any exact constant to `[1/2, 1]`.  This final
section records the sharper structural payoff hiding in that interval: the *lower* endpoint
`1/2` is not merely a fence but an already-proved theorem (`hhkp_bound`), so the Erdős main
conjecture `R(3,k) ~ (1/2)·k²/log k` is logically equivalent to a *one-sided* statement —
improving Shearer's upper constant from `1` down to `1/2`.  We also complete the
lower-constant/upper-constant symmetry left open in Part IX: `R3_lower_constant_of_le_half`
is the exact dual of `R3_upper_constant_of_one_le`.  Both are axiom-frugal (only the two
sharp Ramsey bounds). -/

/-- **Every constant `a ≤ 1/2` is a valid first-order lower constant for `R(3,k)`** (dual of
    `R3_upper_constant_of_one_le`).  Whereas Shearer (`1`) makes every *larger* constant a valid
    upper bound, HHKP (`1/2`) makes every *smaller* constant a valid lower bound, via
    `lower_bound_mono`.  This is the general statement behind the specific `hhkp_subsumes_*`
    family (`1/162, 1/4, 1/3` are its instances), completing the Part IX symmetry: valid lower
    constants contain `(−∞, 1/2]`, valid upper constants contain `[1, ∞)`. -/
theorem R3_lower_constant_of_le_half (a : ℝ) (ha : a ≤ 1/2) :
    ∀ ε > 0, ∃ k₀ : ℕ, ∀ k : ℕ, k ≥ k₀ →
        (R3 k : ℝ) ≥ (a - ε) * k^2 / log k :=
  lower_bound_mono ha hhkp_bound

/-- **The Erdős conjecture reduces to the upper bound.**  Because the lower half of
    `mainConjecture` — `R(3,k) ≥ (1/2 − ε)·k²/log k` — is already the theorem `hhkp_bound`, the
    full conjecture `R(3,k) ~ (1/2)·k²/log k` is *equivalent* to its upper half alone:

      `mainConjecture ↔ ∀ ε > 0, eventually R(3,k) ≤ (1/2 + ε)·k²/log k`.

    In other words, settling Erdős #165 is exactly the problem of sharpening Shearer's upper
    constant from `1` to `1/2`; the matching lower bound is done.  Forward is projection to the
    upper half; backward pairs the hypothesized upper half with `hhkp_bound`. -/
theorem mainConjecture_iff_upper_half :
    mainConjecture ↔
      (∀ ε > 0, ∃ k₀ : ℕ, ∀ k : ℕ, k ≥ k₀ →
          (R3 k : ℝ) ≤ (1/2 + ε) * k^2 / log k) := by
  constructor
  · intro h ε hε
    obtain ⟨k₀, hk₀⟩ := h ε hε
    exact ⟨k₀, fun k hk => (hk₀ k hk).2⟩
  · intro hup ε hε
    obtain ⟨k₁, hk₁⟩ := hhkp_bound ε hε
    obtain ⟨k₂, hk₂⟩ := hup ε hε
    exact ⟨max k₁ k₂, fun k hk =>
      ⟨hk₁ k (le_of_max_le_left hk), hk₂ k (le_of_max_le_right hk)⟩⟩

/- ## Part XI: The set of valid asymptotic constants, and its order interface

Parts VI–X repeatedly manipulate the two half-statements "`b` is a valid first-order
*upper* constant for `R(3,k)`" and "`a` is a valid first-order *lower* constant".  This
section names those predicates (`ValidUpperConstant`, `ValidLowerConstant`) and assembles
the scattered facts into a single order-theoretic interface:

* the valid upper constants form an **up-set** (`ValidUpperConstant_mono`, from
  `upper_bound_mono`) and the valid lower constants a **down-set**
  (`ValidLowerConstant_anti`, from `lower_bound_mono`);
* Shearer gives `1` as a valid upper constant and HHKP gives `1/2` as a valid lower one,
  so the sets are nonempty with the known containments `[1,∞) ⊆ uppers` and
  `(−∞,1/2] ⊆ lowers`, while the fences `uppers ⊆ [1/2,∞)` and `lowers ⊆ (−∞,1]` hold;
* **every** valid lower constant is `≤` **every** valid upper constant
  (`validLowerConstant_le_validUpperConstant`, from the axiom-free
  `asymptotic_constant_le`);
* the headline: the Erdős conjecture is *exactly* the statement that `1/2` is a valid
  upper constant (`mainConjecture_iff_validUpperConstant_half`), and under it `1/2` is the
  **least** valid upper constant — the infimum of the valid upper constants is the exact
  asymptotic constant of `R(3,k)`.

No new axioms: everything is glue over the results of Parts II–X. -/

/-- **`b` is a valid first-order asymptotic upper constant for `R(3,k)`**: for every
    `ε > 0`, eventually `R(3,k) ≤ (b + ε)·k²/log k`.  This is the recurring upper half of
    the conjecture predicates (`mainConjecture`, `pgmConjecture`, `constantConjecture`). -/
def ValidUpperConstant (b : ℝ) : Prop :=
  ∀ ε > 0, ∃ k₀ : ℕ, ∀ k : ℕ, k ≥ k₀ → (R3 k : ℝ) ≤ (b + ε) * k^2 / log k

/-- **`a` is a valid first-order asymptotic lower constant for `R(3,k)`**: for every
    `ε > 0`, eventually `R(3,k) ≥ (a − ε)·k²/log k`.  The dual of `ValidUpperConstant`. -/
def ValidLowerConstant (a : ℝ) : Prop :=
  ∀ ε > 0, ∃ k₀ : ℕ, ∀ k : ℕ, k ≥ k₀ → (R3 k : ℝ) ≥ (a - ε) * k^2 / log k

/-- **The valid upper constants form an up-set.**  If `b` is a valid upper constant and
    `b ≤ b'`, then so is `b'` — a weaker upper bound is still valid (`upper_bound_mono`). -/
theorem ValidUpperConstant_mono {b b' : ℝ} (hbb : b ≤ b') (h : ValidUpperConstant b) :
    ValidUpperConstant b' :=
  upper_bound_mono hbb h

/-- **The valid lower constants form a down-set.**  If `a` is a valid lower constant and
    `a' ≤ a`, then so is `a'` — a weaker lower bound is still valid (`lower_bound_mono`). -/
theorem ValidLowerConstant_anti {a a' : ℝ} (haa : a' ≤ a) (h : ValidLowerConstant a) :
    ValidLowerConstant a' :=
  lower_bound_mono haa h

/-- **Shearer: `1` is a valid upper constant** (`R(3,k) ≤ (1+ε)·k²/log k`). -/
theorem shearer_validUpperConstant_one : ValidUpperConstant 1 := shearer_upper_bound

/-- **HHKP: `1/2` is a valid lower constant** (`R(3,k) ≥ (1/2−ε)·k²/log k`). -/
theorem hhkp_validLowerConstant_half : ValidLowerConstant (1/2) := hhkp_bound

/-- **Every valid upper constant is `≥ 1/2`** (the HHKP fence, `R3_upper_constant_ge_half`). -/
theorem ValidUpperConstant_ge_half {b : ℝ} (h : ValidUpperConstant b) : (1:ℝ)/2 ≤ b :=
  R3_upper_constant_ge_half b h

/-- **Every valid lower constant is `≤ 1`** (the Shearer fence, `R3_lower_constant_le_one`). -/
theorem ValidLowerConstant_le_one {a : ℝ} (h : ValidLowerConstant a) : a ≤ 1 :=
  R3_lower_constant_le_one a h

/-- **Every `b ≥ 1` is a valid upper constant** (Shearer widened, `R3_upper_constant_of_one_le`);
    so `[1, ∞) ⊆ {b | ValidUpperConstant b} ⊆ [1/2, ∞)`. -/
theorem one_le_validUpperConstant {b : ℝ} (hb : 1 ≤ b) : ValidUpperConstant b :=
  R3_upper_constant_of_one_le b hb

/-- **Every `a ≤ 1/2` is a valid lower constant** (HHKP weakened, `R3_lower_constant_of_le_half`);
    so `(−∞, 1/2] ⊆ {a | ValidLowerConstant a} ⊆ (−∞, 1]`. -/
theorem validLowerConstant_of_le_half {a : ℝ} (ha : a ≤ 1/2) : ValidLowerConstant a :=
  R3_lower_constant_of_le_half a ha

/-- **Every valid lower constant is `≤` every valid upper constant.**  The two families
    interleave correctly: no valid lower constant can exceed a valid upper one.  A direct
    application of the axiom-free `asymptotic_constant_le` to `f = R3` — the structural core
    behind the bracket `[1/2, 1]`. -/
theorem validLowerConstant_le_validUpperConstant {a b : ℝ}
    (hl : ValidLowerConstant a) (hu : ValidUpperConstant b) : a ≤ b :=
  asymptotic_constant_le (fun k => (R3 k : ℝ)) a b hl hu

/-- **The Erdős conjecture ⟺ `1/2` is a valid upper constant.**  Since the lower half of
    `mainConjecture` is already the theorem `hhkp_bound`, the full conjecture reduces to its
    upper half — precisely `ValidUpperConstant (1/2)` (`mainConjecture_iff_upper_half`). -/
theorem mainConjecture_iff_validUpperConstant_half :
    mainConjecture ↔ ValidUpperConstant (1/2) :=
  mainConjecture_iff_upper_half

/-- **Under the Erdős conjecture, `1/2` is the least valid upper constant.**  The conjecture
    makes `1/2` a valid upper constant (`mainConjecture_iff_validUpperConstant_half`), and the
    HHKP fence `ValidUpperConstant_ge_half` bounds every valid upper constant below by `1/2`.
    Hence `1/2 = min {b | ValidUpperConstant b}`: the exact asymptotic constant of `R(3,k)` is
    the infimum of its valid first-order upper constants, and it equals `1/2` iff Erdős #165's
    conjecture holds. -/
theorem mainConjecture_imp_isLeast_validUpperConstant (h : mainConjecture) :
    IsLeast {b : ℝ | ValidUpperConstant b} (1/2) :=
  ⟨mainConjecture_iff_validUpperConstant_half.mp h,
   fun b hb => ValidUpperConstant_ge_half hb⟩

/- ## Part XII: The exact asymptotic constants exist unconditionally

Part XI closed with a *conditional* headline (`mainConjecture_imp_isLeast_validUpperConstant`):
**under** the Erdős conjecture, `1/2` is the least valid upper constant.  This section removes
the hypothesis.  The set `{b | ValidUpperConstant b}` is nonempty (`1 ∈`, Shearer) and bounded
below (`≥ 1/2`, the HHKP fence), so its infimum `c⁺ := sInf {b | ValidUpperConstant b}` exists —
and, crucially, is **attained**: `c⁺` is itself a valid upper constant.  Hence, with *no*
conjecture assumed, `R(3,k)` has a genuine least first-order upper constant `c⁺ ∈ [1/2, 1]`, the
true asymptotic upper constant.  Dually the valid lower constants have a greatest element
`c⁻ := sSup {a | ValidLowerConstant a} ∈ [1/2, 1]`, with `c⁻ ≤ c⁺`.  The Erdős conjecture then
collapses to the crisp scalar equation `c⁺ = 1/2` — an *iff*, upgrading the conditional
one-directional Part XI result to a genuine characterisation.

The one non-formal step is attainment of the infimum, `validUpperConstant_sInf_mem`: for any
`δ > 0`, since `c⁺ < c⁺ + δ` there is a valid upper constant `b < c⁺ + δ` (`exists_lt_of_csInf_lt`),
and feeding `ε' = c⁺ + δ − b > 0` into `ValidUpperConstant b` yields `R(3,k) ≤ (c⁺ + δ)·k²/log k`
eventually.  This is exactly the statement that the up-set of valid upper constants is *closed at
its infimum*.  No new axioms; the two sharp Ramsey bounds enter only through Part XI. -/

/-- The valid first-order upper constants are bounded below (by `1/2`, the HHKP fence). -/
theorem bddBelow_validUpperConstant : BddBelow {b : ℝ | ValidUpperConstant b} :=
  ⟨1/2, fun b hb => ValidUpperConstant_ge_half hb⟩

/-- The valid first-order upper constants form a nonempty set (`1`, Shearer). -/
theorem nonempty_validUpperConstant : {b : ℝ | ValidUpperConstant b}.Nonempty :=
  ⟨1, shearer_validUpperConstant_one⟩

/-- The valid first-order lower constants are bounded above (by `1`, the Shearer fence). -/
theorem bddAbove_validLowerConstant : BddAbove {a : ℝ | ValidLowerConstant a} :=
  ⟨1, fun a ha => ValidLowerConstant_le_one ha⟩

/-- The valid first-order lower constants form a nonempty set (`1/2`, HHKP). -/
theorem nonempty_validLowerConstant : {a : ℝ | ValidLowerConstant a}.Nonempty :=
  ⟨1/2, hhkp_validLowerConstant_half⟩

/-- **The infimum of the valid upper constants is attained.**  `sInf {b | ValidUpperConstant b}`
    is itself a valid upper constant.  This is the key structural fact upgrading the conditional
    least-element result of Part XI to an unconditional one: the up-set of valid upper constants
    is closed at its infimum.  Proof: for any `δ > 0`, `sInf < sInf + δ`, so some valid upper
    constant `b` satisfies `b < sInf + δ`; feeding `ε' = sInf + δ − b > 0` into `b`'s validity
    gives `R(3,k) ≤ (sInf + δ)·k²/log k` eventually. -/
theorem validUpperConstant_sInf_mem :
    ValidUpperConstant (sInf {b : ℝ | ValidUpperConstant b}) := by
  intro δ hδ
  obtain ⟨b, hbmem, hb⟩ :=
    exists_lt_of_csInf_lt nonempty_validUpperConstant
      (show sInf {b : ℝ | ValidUpperConstant b} < sInf {b : ℝ | ValidUpperConstant b} + δ by
        linarith)
  have hb' : ValidUpperConstant b := hbmem
  have hε' : sInf {b : ℝ | ValidUpperConstant b} + δ - b > 0 := by linarith
  obtain ⟨k₀, hk₀⟩ := hb' _ hε'
  refine ⟨k₀, fun k hk => ?_⟩
  have hval := hk₀ k hk
  have heq : b + (sInf {b : ℝ | ValidUpperConstant b} + δ - b)
      = sInf {b : ℝ | ValidUpperConstant b} + δ := by ring
  rwa [heq] at hval

/-- **The supremum of the valid lower constants is attained** (dual of
    `validUpperConstant_sInf_mem`).  `sSup {a | ValidLowerConstant a}` is itself a valid lower
    constant: the down-set of valid lower constants is closed at its supremum. -/
theorem validLowerConstant_sSup_mem :
    ValidLowerConstant (sSup {a : ℝ | ValidLowerConstant a}) := by
  intro δ hδ
  obtain ⟨a, hamem, ha⟩ :=
    exists_lt_of_lt_csSup nonempty_validLowerConstant
      (show sSup {a : ℝ | ValidLowerConstant a} - δ < sSup {a : ℝ | ValidLowerConstant a} by
        linarith)
  have ha' : ValidLowerConstant a := hamem
  have hε' : a - (sSup {a : ℝ | ValidLowerConstant a} - δ) > 0 := by linarith
  obtain ⟨k₀, hk₀⟩ := ha' _ hε'
  refine ⟨k₀, fun k hk => ?_⟩
  have hval := hk₀ k hk
  have heq : a - (a - (sSup {a : ℝ | ValidLowerConstant a} - δ))
      = sSup {a : ℝ | ValidLowerConstant a} - δ := by ring
  rwa [heq] at hval

/-- **Unconditionally, `R(3,k)` has a least valid first-order upper constant.**  The infimum
    `sInf {b | ValidUpperConstant b}` is a member (`validUpperConstant_sInf_mem`) and a lower
    bound (`csInf_le`), so it is the least element — no conjecture required.  This is the
    unconditional strengthening of `mainConjecture_imp_isLeast_validUpperConstant`, which only
    identified that least element *as* `1/2` under the Erdős conjecture. -/
theorem isLeast_validUpperConstant :
    IsLeast {b : ℝ | ValidUpperConstant b} (sInf {b : ℝ | ValidUpperConstant b}) :=
  ⟨validUpperConstant_sInf_mem, fun b hb => csInf_le bddBelow_validUpperConstant hb⟩

/-- **Unconditionally, `R(3,k)` has a greatest valid first-order lower constant** (dual). -/
theorem isGreatest_validLowerConstant :
    IsGreatest {a : ℝ | ValidLowerConstant a} (sSup {a : ℝ | ValidLowerConstant a}) :=
  ⟨validLowerConstant_sSup_mem, fun a ha => le_csSup bddAbove_validLowerConstant ha⟩

/-- **The true asymptotic upper constant of `R(3,k)`.**  `c⁺ := sInf {b | ValidUpperConstant b}`,
    the least real `b` for which `R(3,k) ≤ (b + ε)·k²/log k` holds eventually for every `ε > 0`.
    By `isLeast_validUpperConstant` this infimum is attained; by `asymptoticUpperConstant_mem_Icc`
    it lies in `[1/2, 1]`; and Erdős #165's conjecture is exactly `c⁺ = 1/2`. -/
noncomputable def asymptoticUpperConstant : ℝ := sInf {b : ℝ | ValidUpperConstant b}

/-- **The true asymptotic lower constant of `R(3,k)`.**  `c⁻ := sSup {a | ValidLowerConstant a}`,
    the greatest real `a` for which `R(3,k) ≥ (a − ε)·k²/log k` holds eventually for every
    `ε > 0`.  Attained (`isGreatest_validLowerConstant`) and in `[1/2, 1]`. -/
noncomputable def asymptoticLowerConstant : ℝ := sSup {a : ℝ | ValidLowerConstant a}

/-- **`c⁺ ∈ [1/2, 1]` unconditionally.**  The Shearer fence bounds it above (`1` is a valid upper
    constant, so the infimum is `≤ 1`) and the HHKP fence below (every valid upper constant is
    `≥ 1/2`, so their infimum is `≥ 1/2`).  This brackets the exact asymptotic upper constant
    with no conjecture assumed. -/
theorem asymptoticUpperConstant_mem_Icc :
    (1:ℝ)/2 ≤ asymptoticUpperConstant ∧ asymptoticUpperConstant ≤ 1 :=
  ⟨le_csInf nonempty_validUpperConstant (fun b hb => ValidUpperConstant_ge_half hb),
   csInf_le bddBelow_validUpperConstant shearer_validUpperConstant_one⟩

/-- **`c⁻ ∈ [1/2, 1]` unconditionally** (dual of `asymptoticUpperConstant_mem_Icc`). -/
theorem asymptoticLowerConstant_mem_Icc :
    (1:ℝ)/2 ≤ asymptoticLowerConstant ∧ asymptoticLowerConstant ≤ 1 :=
  ⟨le_csSup bddAbove_validLowerConstant hhkp_validLowerConstant_half,
   csSup_le nonempty_validLowerConstant (fun a ha => ValidLowerConstant_le_one ha)⟩

/-- **`c⁻ ≤ c⁺`.**  The greatest valid lower constant does not exceed the least valid upper
    constant — a direct application of `validLowerConstant_le_validUpperConstant` to the two
    attained extremal members.  Together with the two brackets this says both exact asymptotic
    constants live in `[1/2, 1]` with `c⁻ ≤ c⁺`; the Erdős answer `R(3,k) ~ c·k²/log k` would be
    the collapse `c⁻ = c⁺`. -/
theorem asymptoticLowerConstant_le_asymptoticUpperConstant :
    asymptoticLowerConstant ≤ asymptoticUpperConstant :=
  validLowerConstant_le_validUpperConstant validLowerConstant_sSup_mem validUpperConstant_sInf_mem

/-- **The Erdős conjecture ⟺ `c⁺ = 1/2`.**  The crisp scalar form of Erdős #165: the exact
    asymptotic upper constant equals `1/2` *iff* the main conjecture holds.  Forward: the
    conjecture makes `1/2` a valid upper constant, so `c⁺ ≤ 1/2`, and the fence gives `c⁺ ≥ 1/2`.
    Backward: `c⁺` is attained (`validUpperConstant_sInf_mem`), so `c⁺ = 1/2` makes `1/2` itself a
    valid upper constant — which is the conjecture (`mainConjecture_iff_validUpperConstant_half`).
    This is the *unconditional* upgrade of `mainConjecture_imp_isLeast_validUpperConstant`. -/
theorem mainConjecture_iff_asymptoticUpperConstant_eq_half :
    mainConjecture ↔ asymptoticUpperConstant = 1/2 := by
  rw [mainConjecture_iff_validUpperConstant_half]
  constructor
  · intro h
    have h1 : asymptoticUpperConstant ≤ 1/2 := csInf_le bddBelow_validUpperConstant h
    have h2 : (1:ℝ)/2 ≤ asymptoticUpperConstant := asymptoticUpperConstant_mem_Icc.1
    linarith
  · intro h
    have hmem := validUpperConstant_sInf_mem
    rw [← h]
    exact hmem

/-- **Under the Erdős conjecture the two asymptotic constants collapse to `1/2`.**  The
    conjecture forces the least valid upper constant to `1/2`
    (`mainConjecture_iff_asymptoticUpperConstant_eq_half`); since the greatest valid lower
    constant obeys `1/2 ≤ c⁻ ≤ c⁺ = 1/2` (`asymptoticLowerConstant_mem_Icc`,
    `asymptoticLowerConstant_le_asymptoticUpperConstant`), it too is pinned to `1/2`.  So the
    conjecture is exactly the statement that *both* extremal first-order constants of `R(3,k)`
    equal `1/2` — the upper and lower threads of Part XII collapse to a single value. -/
theorem mainConjecture_imp_asymptoticConstants_eq_half (h : mainConjecture) :
    asymptoticLowerConstant = 1/2 ∧ asymptoticUpperConstant = 1/2 := by
  have hup : asymptoticUpperConstant = 1/2 :=
    mainConjecture_iff_asymptoticUpperConstant_eq_half.mp h
  have hle : asymptoticLowerConstant ≤ asymptoticUpperConstant :=
    asymptoticLowerConstant_le_asymptoticUpperConstant
  have hge : (1:ℝ)/2 ≤ asymptoticLowerConstant := asymptoticLowerConstant_mem_Icc.1
  refine ⟨le_antisymm ?_ hge, hup⟩
  rw [hup] at hle; linarith

/-- **The Erdős conjecture ⟺ both extremal asymptotic constants equal `1/2`.**  The two-sided
    (upper *and* lower) crisp scalar form of Erdős #165, upgrading the upper-only
    `mainConjecture_iff_asymptoticUpperConstant_eq_half`.  Backward direction needs only
    `c⁺ = 1/2` (the lower conjunct is then automatic), but the statement records the full
    collapse. -/
theorem mainConjecture_iff_asymptoticConstants_eq_half :
    mainConjecture ↔ (asymptoticLowerConstant = 1/2 ∧ asymptoticUpperConstant = 1/2) := by
  refine ⟨mainConjecture_imp_asymptoticConstants_eq_half, ?_⟩
  rintro ⟨_, hu⟩
  exact mainConjecture_iff_asymptoticUpperConstant_eq_half.mpr hu

/-- **Under the Erdős conjecture the asymptotic constant of `R(3,k)` genuinely exists**: the
    greatest valid lower constant and least valid upper constant coincide, `c⁻ = c⁺`.  The
    collapse of the bracket `[c⁻, c⁺] ⊆ [1/2, 1]` to a point — the first-order asymptotic
    `R(3,k) ~ (1/2)·k²/log k` in the pinched-constant sense.  Immediate from
    `mainConjecture_imp_asymptoticConstants_eq_half`. -/
theorem mainConjecture_imp_asymptoticConstants_collapse (h : mainConjecture) :
    asymptoticLowerConstant = asymptoticUpperConstant := by
  obtain ⟨hl, hu⟩ := mainConjecture_imp_asymptoticConstants_eq_half h
  rw [hl, hu]

end Erdos165
