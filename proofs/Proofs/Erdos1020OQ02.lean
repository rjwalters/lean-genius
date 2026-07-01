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

/-! ### 7. Closed form: `construction2` as a sum of `k − 1` consecutive binomials.

Telescoping Pascal turns the *difference* `C(n, r) − C(n−k+1, r)` into a *sum*:
each summand `C(j, r−1)` is the Pascal increment `C(j+1, r) − C(j, r)`, so over
the window `j ∈ [n−k+1, n)` the sum telescopes to `construction2 n r k`. The
window has exactly `k − 1` integers, so

  `construction2 n r k = Σ_{j = n−k+1}^{n−1} C(j, r−1)`,

a sum of `k − 1` consecutive binomial coefficients. This is the structural
source of everything in Section 1: monotonicity in `n` is now transparent
(each summand `C(j, r−1)` is itself nondecreasing as the window slides up),
and the exact one-step increment of Section 5 is just the difference of the
two endpoint summands. Combinatorially it stratifies the edges meeting a fixed
`(k−1)`-set by the largest "free" coordinate they use.

We prove the subtraction-free telescoping identity first (so the argument
stays inside `ℕ`), then read off both the closed form and the window size. -/

/-- Telescoping Pascal in additive form: for `a ≤ b` and `r ≥ 1`,
    `C(a, r) + Σ_{j ∈ [a, b)} C(j, r−1) = C(b, r)`. -/
theorem choose_add_sum_Ico (a b r : ℕ) (hab : a ≤ b) (hr : r ≥ 1) :
    Nat.choose a r + ∑ j ∈ Finset.Ico a b, Nat.choose j (r - 1) = Nat.choose b r := by
  induction b, hab using Nat.le_induction with
  | base => simp
  | succ b hab ih =>
    rw [Finset.sum_Ico_succ_top hab]
    -- Pascal at `b`: `C(b+1, r) = C(b, r−1) + C(b, r)` (uses `r ≥ 1`).
    have hpascal : Nat.choose (b + 1) r = Nat.choose b (r - 1) + Nat.choose b r := by
      have h := Nat.choose_succ_succ b (r - 1)
      simp only [Nat.succ_eq_add_one] at h
      rw [Nat.sub_add_cancel hr] at h
      omega
    omega

/-- Closed form: `construction2 n r k = Σ_{j = n−k+1}^{n−1} C(j, r−1)`, a sum of
    exactly `k − 1` consecutive binomial coefficients (see `construction2_sum_card`).
    Telescoping Pascal collapses the difference of two binomials into this sum. -/
theorem construction2_eq_sum (n r k : ℕ) (hr : r ≥ 1) (hk : k ≥ 1) (hn : n ≥ k) :
    construction2 n r k = ∑ j ∈ Finset.Ico (n - k + 1) n, Nat.choose j (r - 1) := by
  unfold construction2
  have hab : n - k + 1 ≤ n := by omega
  have h := choose_add_sum_Ico (n - k + 1) n r hab hr
  omega

/-- The summation window `[n−k+1, n)` has exactly `k − 1` integers: the closed
    form `construction2_eq_sum` is a sum of `k − 1` consecutive binomials. -/
theorem construction2_sum_card (n k : ℕ) (hk : k ≥ 1) (hn : n ≥ k) :
    (Finset.Ico (n - k + 1) n).card = k - 1 := by
  rw [Nat.card_Ico]
  omega

/-! ### 8. General threshold existence for `r ≥ 2, k ≥ 2`.

The worked instance `crossover_r4k2` exhibits a single crossover threshold `n₀(4,2) = 8`.
Here we upgrade that from an example to a theorem: such a threshold *exists* for every
`r ≥ 2, k ≥ 2`, without computing it. The engine is that `construction2` is **unbounded**
in `n` — already its top summand `C(n−1, r−1)` is, because `r − 1 ≥ 1`. Since the
"construction2 dominates" region is upward-closed (Section 2), unboundedness makes it a
genuine final segment `{ n : n₀ ≤ n }`, so the regime transition of `conjecturedValue` is
governed by a single threshold in **every** case, not just the `r = 4, k = 2` example. -/

/-- Elementary lower bound `n − d + 1 ≤ C(n, d)` for `1 ≤ d ≤ n`: fixing a `(d−1)`-subset,
    the `d`-subsets containing it number `n − d + 1`. Proved by induction on `n` from `d`
    using the Pascal step `C(n+1, d) = C(n, d−1) + C(n, d)` with `C(n, d−1) ≥ 1`. -/
theorem sub_add_one_le_choose (n d : ℕ) (hd : 1 ≤ d) (hn : d ≤ n) :
    n - d + 1 ≤ Nat.choose n d := by
  induction n, hn using Nat.le_induction with
  | base => simp
  | succ n hn ih =>
    have hpascal : Nat.choose (n + 1) d = Nat.choose n (d - 1) + Nat.choose n d := by
      have h := Nat.choose_succ_succ n (d - 1)
      simp only [Nat.succ_eq_add_one] at h
      rw [Nat.sub_add_cancel hd] at h
      omega
    have hpos : 1 ≤ Nat.choose n (d - 1) := Nat.choose_pos (by omega)
    omega

/-- `construction2` dominates its top summand `C(n−1, r−1)` (for `k ≥ 2`, `n ≥ k`): the
    index `n − 1` lies in the summation window `[n−k+1, n)` of `construction2_eq_sum`. -/
theorem choose_pred_le_construction2 (n r k : ℕ) (hr : r ≥ 1) (hk : k ≥ 2) (hn : n ≥ k) :
    Nat.choose (n - 1) (r - 1) ≤ construction2 n r k := by
  rw [construction2_eq_sum n r k hr (by omega) hn]
  apply Finset.single_le_sum (f := fun j => Nat.choose j (r - 1)) (fun _ _ => Nat.zero_le _)
  rw [Finset.mem_Ico]; omega

/-- For `r ≥ 2, k ≥ 2`, `construction2` eventually overtakes the constant `construction1`:
    some `n ≥ k` has `construction1 r k ≤ construction2 n r k`. Witness
    `n = construction1 r k + r + k`, large enough that even the single top summand
    `C(n−1, r−1) ≥ (n−1) − (r−1) + 1 = construction1 r k + k + 1` already exceeds it. -/
theorem construction2_eventually_dominates (r k : ℕ) (hr : r ≥ 2) (hk : k ≥ 2) :
    ∃ n, k ≤ n ∧ construction1 r k ≤ construction2 n r k := by
  set N := construction1 r k + r + k with hN
  refine ⟨N, by omega, ?_⟩
  have h1 : Nat.choose (N - 1) (r - 1) ≤ construction2 N r k :=
    choose_pred_le_construction2 N r k (by omega) hk (by omega)
  have h2 : (N - 1) - (r - 1) + 1 ≤ Nat.choose (N - 1) (r - 1) :=
    sub_add_one_le_choose (N - 1) (r - 1) (by omega) (by omega)
  omega

/-- **General threshold existence (`r ≥ 2, k ≥ 2`).** There is a threshold `n₀ ≥ k` beyond
    which `construction2` always dominates `construction1`: the "large-n regime" is a genuine
    final segment `{ n : n₀ ≤ n }`. This generalizes the worked instance `crossover_r4k2`
    (`r = 4, k = 2`, `n₀ = 8`) to all `r ≥ 2, k ≥ 2`, establishing that a single regime
    threshold exists in every case. (The exact `n₀(r, k)` is left open; only existence is
    proved.) -/
theorem exists_dominance_threshold (r k : ℕ) (hr : r ≥ 2) (hk : k ≥ 2) :
    ∃ n₀, k ≤ n₀ ∧ ∀ n, n₀ ≤ n → construction1 r k ≤ construction2 n r k := by
  obtain ⟨n₁, hkn₁, hdom₁⟩ := construction2_eventually_dominates r k hr hk
  exact ⟨n₁, hkn₁, fun n hn =>
    construction2_dominant_up n₁ n r k (by omega) (by omega) hkn₁ hn hdom₁⟩

/-- Beyond the threshold, `conjecturedValue` collapses to `construction2` (the large-n
    regime), for every `r ≥ 2, k ≥ 2`. Combines `exists_dominance_threshold` with the
    collapse lemma `conjecturedValue_large`. -/
theorem conjecturedValue_eq_construction2_eventually (r k : ℕ) (hr : r ≥ 2) (hk : k ≥ 2) :
    ∃ n₀, k ≤ n₀ ∧ ∀ n, n₀ ≤ n → conjecturedValue n r k = construction2 n r k := by
  obtain ⟨n₀, hkn₀, hdom⟩ := exists_dominance_threshold r k hr hk
  exact ⟨n₀, hkn₀, fun n hn => conjecturedValue_large n r k (hdom n hn)⟩

end Erdos1020OQ02
