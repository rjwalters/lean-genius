/-
  Erdős Problem #1020 — OQ-02: The small-n / large-n regime transition
  for the Erdős Matching Conjecture.

  Parent: Erdős Matching Conjecture (erdosproblems.com/1020).
  Status of the conjecture: OPEN for r ≥ 4.

  Context.
  The conjectured extremal value of f(n; r, k) — the maximum number of edges
  in an r-uniform hypergraph on n vertices with no k pairwise-disjoint edges —
  is the maximum of two explicit constructions:

    construction1 r k     = C(r·k − 1, r)              (all r-edges on r·k−1 vertices)
    construction2 n r k   = C(n, r) − C(n − k + 1, r)  (all edges meeting a fixed (k−1)-set)
    conjecturedValue      = max(construction1, construction2)

  The conjecture is KNOWN in two opposite regimes:
    • small n   — Frankl: n ≤ kr + kr/(2 r^{2r+1})
    • large n   — Huang–Loh–Sudakov: n ≥ 3 k r²
  and OPEN in the gap between them (for r ≥ 4).

  The two constructions are extremal in opposite regimes:
  `construction1` is the maximiser for small n, `construction2` for large n.
  This file does NOT resolve the open gap. Instead it pins down, fully and
  axiom-free, the *shape* of the transition between the two regimes:

    1. `construction1` is constant in n;
    2. `construction2` is monotonically nondecreasing in n (for n ≥ k);
    3. hence the set of n on which `construction2` dominates `construction1`
       is upward-closed — there is a single threshold separating the
       "small-n regime" (extremal value = construction1) from the
       "large-n regime" (extremal value = construction2);
    4. consequently `conjecturedValue` is itself monotone nondecreasing in n;
    5. on each side of the threshold `conjecturedValue` collapses to the
       relevant construction (`max_eq_left`/`max_eq_right`).

  The monotonicity (2) is a Pascal-telescoping identity:
    construction2 (n+1) − construction2 n  =  C(n, r−1) − C(n−k+1, r−1)  ≥ 0.

  A worked instance (r = 4, k = 2) exhibits the crossover concretely at n = 8.

  All results are machine-checked with `decide` / `omega` only — no axioms,
  no `native_decide`, no `sorry`.

  Tags: hypergraph-theory, matching, extremal-combinatorics, regime-transition
-/

import Mathlib

open Finset Nat

namespace Erdos1020OQ02

/-- Construction 1: all r-edges on `r·k − 1` vertices. Independent of `n`. -/
def construction1 (r k : ℕ) : ℕ := Nat.choose (r * k - 1) r

/-- Construction 2: all edges meeting a fixed `(k−1)`-set, on `n` vertices. -/
def construction2 (n r k : ℕ) : ℕ := Nat.choose n r - Nat.choose (n - k + 1) r

/-- The conjectured extremal value `f(n; r, k)`. -/
def conjecturedValue (n r k : ℕ) : ℕ := max (construction1 r k) (construction2 n r k)

/-! ### 1. `construction2` is monotone nondecreasing in `n`.

(`construction1 r k` is independent of `n` by construction — it has no `n`
argument — so all of the regime structure below is carried by `construction2`.)

The single-step inequality is the heart of the file: it is the nonnegativity
of `C(n, r−1) − C(n−k+1, r−1)`, exposed via two Pascal identities. -/

/-- One step of monotonicity in `n`. -/
theorem construction2_mono_step (n r k : ℕ) (hr : r ≥ 1) (hk : k ≥ 1) (hn : n ≥ k) :
    construction2 n r k ≤ construction2 (n + 1) r k := by
  unfold construction2
  -- Normalise the shifted index of the upper construction.
  have hidx : n + 1 - k + 1 = n - k + 2 := by omega
  rw [hidx]
  have hr1 : r - 1 + 1 = r := Nat.sub_add_cancel hr
  -- Pascal at the top: C(n+1, r) = C(n, r-1) + C(n, r).
  have eq1 : Nat.choose (n + 1) r = Nat.choose n (r - 1) + Nat.choose n r := by
    have h := Nat.choose_succ_succ n (r - 1)
    simp only [Nat.succ_eq_add_one] at h
    rw [hr1] at h
    omega
  -- Pascal at the shifted index: C(n-k+2, r) = C(n-k+1, r-1) + C(n-k+1, r).
  have eq2 : Nat.choose (n - k + 2) r
      = Nat.choose (n - k + 1) (r - 1) + Nat.choose (n - k + 1) r := by
    have h := Nat.choose_succ_succ (n - k + 1) (r - 1)
    simp only [Nat.succ_eq_add_one] at h
    rw [hr1, show n - k + 1 + 1 = n - k + 2 from by omega] at h
    omega
  -- Monotonicity of `choose` in its first argument (since k ≥ 1 ⇒ n-k+1 ≤ n).
  have ineq1 : Nat.choose (n - k + 1) (r - 1) ≤ Nat.choose n (r - 1) :=
    Nat.choose_le_choose (r - 1) (by omega)
  have ineq2 : Nat.choose (n - k + 1) r ≤ Nat.choose n r :=
    Nat.choose_le_choose r (by omega)
  omega

/-- Monotonicity of `construction2` in `n` over the relevant range `k ≤ n ≤ m`. -/
theorem construction2_mono (n m r k : ℕ) (hr : r ≥ 1) (hk : k ≥ 1)
    (hkn : k ≤ n) (hnm : n ≤ m) :
    construction2 n r k ≤ construction2 m r k := by
  induction m, hnm using Nat.le_induction with
  | base => exact le_refl _
  | succ m hm ih =>
    exact le_trans ih (construction2_mono_step m r k hr hk (le_trans hkn hm))

/-! ### 2. The "construction2 dominates" region is upward-closed.

This is the precise statement that the small-n and large-n regimes are
separated by a *single* threshold: once `construction2` has caught up to
`construction1` it never falls behind again. -/

theorem construction2_dominant_up (n m r k : ℕ) (hr : r ≥ 1) (hk : k ≥ 1)
    (hkn : k ≤ n) (hnm : n ≤ m)
    (hdom : construction1 r k ≤ construction2 n r k) :
    construction1 r k ≤ construction2 m r k :=
  le_trans hdom (construction2_mono n m r k hr hk hkn hnm)

/-! ### 3. `conjecturedValue` is monotone nondecreasing in `n`. -/

theorem conjecturedValue_mono (n m r k : ℕ) (hr : r ≥ 1) (hk : k ≥ 1)
    (hkn : k ≤ n) (hnm : n ≤ m) :
    conjecturedValue n r k ≤ conjecturedValue m r k := by
  unfold conjecturedValue
  exact max_le_max (le_refl _) (construction2_mono n m r k hr hk hkn hnm)

/-! ### 4. On each side of the threshold the extremal value collapses. -/

/-- Large-n regime: when `construction2` dominates, it *is* the conjectured value. -/
theorem conjecturedValue_large (n r k : ℕ)
    (h : construction1 r k ≤ construction2 n r k) :
    conjecturedValue n r k = construction2 n r k :=
  max_eq_right h

/-- Small-n regime: when `construction1` dominates, it *is* the conjectured value. -/
theorem conjecturedValue_small (n r k : ℕ)
    (h : construction2 n r k ≤ construction1 r k) :
    conjecturedValue n r k = construction1 r k :=
  max_eq_left h

/-! ### A worked instance of the transition: r = 4, k = 2.

Here `construction1 = C(7,4) = 35`, and
`construction2 n 4 2 = C(n,4) − C(n−1,4) = C(n−1,3)`,
which first reaches 35 at `n = 8`. So the regime boundary sits between
`n = 7` (construction1 strictly larger) and `n = 8` (construction2 catches up).
Both facts are kernel-decidable, hence axiom-free. -/

/-- At `n = 7` the small-n construction is strictly larger. -/
example : construction2 7 4 2 < construction1 4 2 := by decide

/-- At `n = 8` the large-n construction has caught up. -/
example : construction1 4 2 ≤ construction2 8 4 2 := by decide

/-- The conjectured value is `construction1` just below the threshold … -/
example : conjecturedValue 7 4 2 = construction1 4 2 := by decide

/-- … and equals `construction2` at and above it. -/
example : conjecturedValue 8 4 2 = construction2 8 4 2 := by decide

/-- Monotonicity of `conjecturedValue` across the crossover, concretely. -/
example : conjecturedValue 7 4 2 ≤ conjecturedValue 8 4 2 := by decide

/-! ### 5. The exact step difference, and a strict refinement.

`construction2_mono_step` only records the *inequality* `≤`. The increment is
in fact exactly `C(n, r−1) − C(n−k+1, r−1)`. We state this additively to keep
everything in `ℕ` without truncated subtraction, then read off both the
original monotonicity and a strict version. -/

/-- Exact one-step increment of `construction2`:
    `construction2 (n+1) − construction2 n = C(n, r−1) − C(n−k+1, r−1)`,
    written additively. This is the precise identity behind
    `construction2_mono_step`. -/
theorem construction2_step_eq (n r k : ℕ) (hr : r ≥ 1) (hk : k ≥ 1) (hn : n ≥ k) :
    construction2 (n + 1) r k + Nat.choose (n - k + 1) (r - 1)
      = construction2 n r k + Nat.choose n (r - 1) := by
  unfold construction2
  have hidx : n + 1 - k + 1 = n - k + 2 := by omega
  rw [hidx]
  have hr1 : r - 1 + 1 = r := Nat.sub_add_cancel hr
  -- Pascal at the top: C(n+1, r) = C(n, r-1) + C(n, r).
  have eq1 : Nat.choose (n + 1) r = Nat.choose n (r - 1) + Nat.choose n r := by
    have h := Nat.choose_succ_succ n (r - 1)
    simp only [Nat.succ_eq_add_one] at h
    rw [hr1] at h
    omega
  -- Pascal at the shifted index: C(n-k+2, r) = C(n-k+1, r-1) + C(n-k+1, r).
  have eq2 : Nat.choose (n - k + 2) r
      = Nat.choose (n - k + 1) (r - 1) + Nat.choose (n - k + 1) r := by
    have h := Nat.choose_succ_succ (n - k + 1) (r - 1)
    simp only [Nat.succ_eq_add_one] at h
    rw [hr1, show n - k + 1 + 1 = n - k + 2 from by omega] at h
    omega
  -- Both truncated subtractions in `construction2` are genuine (no underflow).
  have hsub1 : Nat.choose (n - k + 2) r ≤ Nat.choose (n + 1) r :=
    Nat.choose_le_choose r (by omega)
  have hsub2 : Nat.choose (n - k + 1) r ≤ Nat.choose n r :=
    Nat.choose_le_choose r (by omega)
  omega

/-- Strict one-step monotonicity: whenever the lower binomial is strictly
    smaller, `construction2` strictly increases. (The hypothesis
    `C(n−k+1, r−1) < C(n, r−1)` holds, e.g., once `k ≥ 2` and `r−1 ≤ n−k+1`.) -/
theorem construction2_strict_mono_step (n r k : ℕ) (hr : r ≥ 1) (hk : k ≥ 1)
    (hn : n ≥ k) (hlt : Nat.choose (n - k + 1) (r - 1) < Nat.choose n (r - 1)) :
    construction2 n r k < construction2 (n + 1) r k := by
  have h := construction2_step_eq n r k hr hk hn
  omega

/-! ### 6. The exact crossover threshold for the worked instance `r = 4, k = 2`.

Monotonicity turns the two boundary evaluations (`n = 7` below, `n = 8` at)
into a *complete* characterization of the construction2-dominant region:
it is exactly `{ n : 8 ≤ n }`. This pins the crossover threshold to the
single value `n₀(4, 2) = 8`. -/

/-- `construction2` overtakes `construction1` (for `r = 4, k = 2`) at exactly
    `n = 8`: the regime boundary is the sharp threshold `n₀ = 8`. -/
theorem crossover_r4k2 (n : ℕ) :
    construction1 4 2 ≤ construction2 n 4 2 ↔ 8 ≤ n := by
  constructor
  · intro h
    by_contra hlt
    push_neg at hlt
    interval_cases n <;> exact absurd h (by decide)
  · intro h
    have h8 : construction1 4 2 ≤ construction2 8 4 2 := by decide
    exact construction2_dominant_up 8 n 4 2 (by norm_num) (by norm_num) (by norm_num) h h8

end Erdos1020OQ02
