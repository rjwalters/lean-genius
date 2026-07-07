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

  A worked instance (r = 4, k = 2) exhibits the crossover concretely at n = 8;
  and for the entire r = 2 family the threshold is pinned down in closed form,
  n₀(2, k) = ⌈(5k − 2)/2⌉ (§10), sharpening both the single point above and the
  qualitative finiteness of §9.

  All results are machine-checked with `omega`, `zify`/`ring` and `decide` only —
  no axioms, no `native_decide`, no `sorry`.

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

/-! ### 8. Window sandwich: `construction2` between `k − 1` copies of its endpoint summands.

The §7 closed form writes `construction2 n r k` as a sum of exactly `k − 1`
binomials `C(j, r−1)` with `j` ranging over the window `[n−k+1, n)`
(`construction2_eq_sum`, `construction2_sum_card`). Because `C(·, r−1)` is monotone
in its first argument, every summand lies between the two window endpoints
`C(n−k+1, r−1)` (smallest) and `C(n−1, r−1)` (largest). Summing the `k − 1` terms
gives a clean two-sided bound,

  `(k−1)·C(n−k+1, r−1) ≤ construction2 n r k ≤ (k−1)·C(n−1, r−1)`,

which sandwiches the difference-of-binomials between equal-width multiples of its
endpoint binomials. For `k ≥ 2` the window is nonempty, so the top summand alone
already gives `C(n−1, r−1) ≤ construction2 n r k` — the degree-`(r−1)` polynomial
growth in `n` that eventually drives `construction2` past the constant
`construction1` and produces the large-`n` regime. -/

/-- Lower half of the window sandwich: every summand is at least the smallest
    endpoint `C(n−k+1, r−1)`, and there are `k − 1` of them. -/
theorem construction2_window_lb (n r k : ℕ) (hr : r ≥ 1) (hk : k ≥ 1) (hn : n ≥ k) :
    (k - 1) * Nat.choose (n - k + 1) (r - 1) ≤ construction2 n r k := by
  rw [construction2_eq_sum n r k hr hk hn]
  have hcard : (Finset.Ico (n - k + 1) n).card = k - 1 := construction2_sum_card n k hk hn
  have hmin : ∀ j ∈ Finset.Ico (n - k + 1) n,
      Nat.choose (n - k + 1) (r - 1) ≤ Nat.choose j (r - 1) := by
    intro j hj
    rw [Finset.mem_Ico] at hj
    exact Nat.choose_le_choose (r - 1) hj.1
  have h := Finset.card_nsmul_le_sum _ _ _ hmin
  rw [hcard] at h
  simpa using h

/-- Upper half of the window sandwich: every summand is at most the largest
    endpoint `C(n−1, r−1)`, and there are `k − 1` of them. -/
theorem construction2_window_ub (n r k : ℕ) (hr : r ≥ 1) (hk : k ≥ 1) (hn : n ≥ k) :
    construction2 n r k ≤ (k - 1) * Nat.choose (n - 1) (r - 1) := by
  rw [construction2_eq_sum n r k hr hk hn]
  have hcard : (Finset.Ico (n - k + 1) n).card = k - 1 := construction2_sum_card n k hk hn
  have hmax : ∀ j ∈ Finset.Ico (n - k + 1) n,
      Nat.choose j (r - 1) ≤ Nat.choose (n - 1) (r - 1) := by
    intro j hj
    rw [Finset.mem_Ico] at hj
    exact Nat.choose_le_choose (r - 1) (by omega)
  have h := Finset.sum_le_card_nsmul _ _ _ hmax
  rw [hcard] at h
  simpa using h

/-- For `k ≥ 2` the window `[n−k+1, n)` contains its top point `n − 1`, so the
    largest summand `C(n−1, r−1)` alone is a lower bound for `construction2`.
    This is the degree-`(r−1)` growth driving the large-`n` regime: a single
    binomial of full degree already sits below the conjectured extremal value. -/
theorem construction2_ge_top_summand (n r k : ℕ) (hr : r ≥ 1) (hk : k ≥ 2) (hn : n ≥ k) :
    Nat.choose (n - 1) (r - 1) ≤ construction2 n r k := by
  rw [construction2_eq_sum n r k hr (by omega) hn]
  refine Finset.single_le_sum (f := fun j => Nat.choose j (r - 1)) (fun i _ => Nat.zero_le _) ?_
  rw [Finset.mem_Ico]; omega

/-- Worked instance `r = 4, k = 2`: the window has a single point (`k − 1 = 1`),
    so the sandwich is tight — both bounds equal `C(n−1, 3) = construction2 n 4 2`.
    At `n = 8` this is `C(7, 3) = 35`, the crossover value `construction1 4 2`. -/
example : construction2 8 4 2 = Nat.choose 7 3 := by decide

/-- The top-summand bound, concretely at the crossover: `C(7, 3) = 35 ≤ construction2 8 4 2`. -/
example : Nat.choose 7 3 ≤ construction2 8 4 2 := by decide

/-! ### 9. The large-`n` regime is reached — the dominance threshold is finite.

Monotonicity (§1) shows the set of `n` on which `construction2` dominates `construction1`
is *upward-closed*; the results above (§8) bound `construction2` below by a single binomial
of full degree `r − 1`.  What remains, to confirm the regime transition is a genuine finite
threshold rather than a dominance never attained, is that this set is *nonempty*: for `r ≥ 2`,
`k ≥ 2`, `construction2` eventually exceeds the constant `construction1`.  The driver is that
`C(·, r − 1)` is unbounded for `r − 1 ≥ 1`. -/

/-- `Nat.choose m d` is unbounded in `m` for any fixed degree `d ≥ 1`: for every target `T`
there is an `m` with `T ≤ C(m, d)`.  Pascal's step `C(m+1, d+1) ≥ C(m, d)` lifts the base
`C(m, 1) = m`. -/
theorem choose_unbounded (d : ℕ) (hd : 1 ≤ d) (T : ℕ) : ∃ m, T ≤ Nat.choose m d := by
  induction d with
  | zero => omega
  | succ e ih =>
    rcases Nat.eq_zero_or_pos e with he | he
    · subst he; exact ⟨T, by rw [Nat.choose_one_right]⟩
    · obtain ⟨m, hm⟩ := ih he
      refine ⟨m + 1, ?_⟩
      calc T ≤ Nat.choose m e := hm
        _ ≤ Nat.choose (m + 1) (e + 1) := by rw [Nat.choose_succ_succ]; omega

/-- **The large-`n` regime is nonempty: the dominance threshold is finite.**  For `r ≥ 2`,
`k ≥ 2`, there is an `N` beyond which `construction2` (the large-`n` extremal construction)
dominates the constant `construction1`.  Together with the upward-closed dominance from §1
this shows the regime transition is a genuine *finite* threshold: the `n`-axis splits into a
bounded small-`n` regime (extremal value `construction1`) and an unbounded large-`n` regime
(extremal value `construction2`), with the crossover actually attained.  The witness `N` is
`m + k`, where `m` realises `construction1 r k ≤ C(m, r − 1)` via `choose_unbounded`. -/
theorem exists_large_regime (r k : ℕ) (hr : 2 ≤ r) (hk : 2 ≤ k) :
    ∃ N, ∀ n, N ≤ n → construction1 r k ≤ construction2 n r k := by
  obtain ⟨m, hm⟩ := choose_unbounded (r - 1) (by omega) (construction1 r k)
  refine ⟨m + k, fun n hn => ?_⟩
  have hge : Nat.choose (n - 1) (r - 1) ≤ construction2 n r k :=
    construction2_ge_top_summand n r k (by omega) hk (by omega)
  have hmono : Nat.choose m (r - 1) ≤ Nat.choose (n - 1) (r - 1) :=
    Nat.choose_le_choose (r - 1) (by omega)
  exact le_trans hm (le_trans hmono hge)

/-! ### 10. Sharp crossover threshold for the `r = 2` family.

Sections 6 and 9 locate the crossover only *qualitatively*: a single concrete
point `n₀(4,2) = 8`, and the mere *existence* of a finite threshold for every
`r, k ≥ 2`.  Here we compute the threshold *exactly and in closed form* for the
entire `r = 2` family.  At `r = 2` both constructions are explicit quadratics:

  `2·construction2 n 2 k = (k−1)·(2n−k)`,     `2·construction1 2 k = (2k−1)·(2k−2)`,

so `construction2` reaches `construction1` precisely when `2n ≥ 5k − 2`, i.e. the
threshold is `n₀(2,k) = ⌈(5k−2)/2⌉`.  Specialising `k = 2` recovers `n₀(2,2) = 4`.

Everything stays inside `ℕ`: the doubled identities carry the polynomial content
to `ℤ` (`zify` + `ring`) with subtraction side-conditions closed by `omega`, and
the final cancellation of the common factor `k − 1` uses `Nat.le_of_mul_le_mul_left`. -/

/-- Doubling a `choose _ 2` clears the division: `2·C(m, 2) = m·(m−1)`. -/
theorem two_mul_choose_two (m : ℕ) : 2 * Nat.choose m 2 = m * (m - 1) := by
  have hev : Even (m * (m - 1)) := by
    rcases Nat.even_or_odd m with h | h
    · exact h.mul_right _
    · exact (Nat.Odd.sub_odd h odd_one).mul_left _
  rw [Nat.choose_two_right, Nat.mul_div_cancel' hev.two_dvd]

/-- Doubled closed form of `construction2` at `r = 2`:
    `2·construction2 n 2 k = (k−1)·(2n−k)` — an explicit quadratic in `n`. -/
theorem two_mul_construction2_r2 (n k : ℕ) (hk : 1 ≤ k) (hn : k ≤ n) :
    2 * construction2 n 2 k = (k - 1) * (2 * n - k) := by
  have hle : n - k + 1 ≤ n := by omega
  have hmono : Nat.choose (n - k + 1) 2 ≤ Nat.choose n 2 := Nat.choose_le_choose 2 hle
  have key : 2 * Nat.choose n 2
      = 2 * Nat.choose (n - k + 1) 2 + (k - 1) * (2 * n - k) := by
    rw [two_mul_choose_two n, two_mul_choose_two (n - k + 1)]
    have e1 : n - k + 1 - 1 = n - k := by omega
    rw [e1]
    zify [hk, hn, show 1 ≤ n by omega, show k ≤ 2 * n by omega]
    ring
  unfold construction2
  omega

/-- Doubled closed form of `construction1` at `r = 2`:
    `2·construction1 2 k = (2k−1)·(2k−2)` — the constant (in `n`) value. -/
theorem two_mul_construction1_r2 (k : ℕ) :
    2 * construction1 2 k = (2 * k - 1) * (2 * k - 2) := by
  unfold construction1
  rw [two_mul_choose_two]
  have e1 : 2 * k - 1 - 1 = 2 * k - 2 := by omega
  rw [e1]

/-- **Sharp crossover threshold for `r = 2`.**  For all `k ≥ 2` and `n ≥ k`,
`construction2` reaches `construction1` exactly when `2n ≥ 5k − 2`.  The threshold
is therefore `n₀(2,k) = ⌈(5k−2)/2⌉` (e.g. `k = 2` gives `n₀ = 4`): the exact,
closed-form counterpart — for the whole `r = 2` family — of the single worked
point `crossover_r4k2` and of the qualitative `exists_large_regime`. -/
theorem crossover_r2 (n k : ℕ) (hk : 2 ≤ k) (hn : k ≤ n) :
    construction1 2 k ≤ construction2 n 2 k ↔ 5 * k - 2 ≤ 2 * n := by
  have hc1 := two_mul_construction1_r2 k
  have hc2v := two_mul_construction2_r2 n k (by omega) hn
  -- Scaling by `2` is order-reflecting on `ℕ`, so pass to the doubled quantities.
  have hdouble : construction1 2 k ≤ construction2 n 2 k
      ↔ 2 * construction1 2 k ≤ 2 * construction2 n 2 k := by omega
  rw [hdouble, hc1, hc2v]
  -- Expose the common factor `k − 1` on the constant side.
  have hlhs : (2 * k - 1) * (2 * k - 2) = (k - 1) * (4 * k - 2) := by
    zify [show 1 ≤ k by omega, show 1 ≤ 2 * k by omega, show 2 ≤ 2 * k by omega,
      show 2 ≤ 4 * k by omega]
    ring
  rw [hlhs]
  -- Cancel the positive common factor `k − 1`.
  constructor
  · intro h
    have hpos : 0 < k - 1 := by omega
    have := Nat.le_of_mul_le_mul_left h hpos
    omega
  · intro h
    have hstep : 4 * k - 2 ≤ 2 * n - k := by omega
    exact Nat.mul_le_mul (le_refl (k - 1)) hstep

/-- On the `r = 2` family the conjectured extremal value collapses to the
large-`n` construction exactly on the threshold `2n ≥ 5k − 2`. -/
theorem conjecturedValue_r2_large (n k : ℕ) (hk : 2 ≤ k) (hn : k ≤ n)
    (hthr : 5 * k - 2 ≤ 2 * n) : conjecturedValue n 2 k = construction2 n 2 k := by
  unfold conjecturedValue
  exact max_eq_right ((crossover_r2 n k hk hn).2 hthr)

/-- **Linear lower bound for binomial coefficients.** `C(m, d) ≥ m + 1 − d` for `d ≥ 1`:
    past the diagonal the binomial coefficient grows by at least one per unit increase
    of `m`. Equality holds at `d = 1` (`C(m, 1) = m`) and at `m = d` (`C(d, d) = 1`).
    (Complements `choose_unbounded` above with an *explicit* linear rate.) -/
theorem choose_ge_linear (d m : ℕ) (hd : d ≥ 1) : m + 1 - d ≤ Nat.choose m d := by
  induction m with
  | zero =>
    have : Nat.choose 0 d = 0 := Nat.choose_eq_zero_of_lt (by omega)
    omega
  | succ m ih =>
    obtain ⟨d', rfl⟩ : ∃ d', d = d' + 1 := ⟨d - 1, by omega⟩
    have hrec : Nat.choose (m + 1) (d' + 1) = Nat.choose m d' + Nat.choose m (d' + 1) :=
      Nat.choose_succ_succ m d'
    rcases le_or_gt d' m with hle | hlt
    · have hpos : 1 ≤ Nat.choose m d' := Nat.choose_pos hle
      omega
    · -- `d' > m` ⇒ `d = d' + 1 > m + 1` ⇒ the truncated LHS `(m+1)+1 − d` is `0`.
      omega

/-- **Explicit linear growth of the large-`n` construction.**
    `n − (r − 1) ≤ construction2 n r k`: the degree-`(r−1) ≥ 1` top summand
    `C(n−1, r−1)` already contributes a linear-in-`n` term. -/
theorem construction2_ge_linear (n r k : ℕ) (hr : r ≥ 2) (hk : k ≥ 2) (hn : n ≥ k) :
    n - (r - 1) ≤ construction2 n r k := by
  have htop := construction2_ge_top_summand n r k (by omega) hk hn
  have hlin := choose_ge_linear (r - 1) (n - 1) (by omega)
  have hn1 : (n - 1) + 1 = n := by omega
  rw [hn1] at hlin
  omega

/-- **The large-`n` regime is unconditional.** For every `r ≥ 2, k ≥ 2` there is a
    threshold past which the conjectured extremal value collapses to
    `construction2`: `∀ n ≥ N, conjecturedValue n r k = construction2 n r k`.
    (What remains open is the *value* of the extremal function inside the gap band,
    not the identity of the eventual maximiser.) -/
theorem conjecturedValue_eventually (r k : ℕ) (hr : 2 ≤ r) (hk : 2 ≤ k) :
    ∃ N, ∀ n, N ≤ n → conjecturedValue n r k = construction2 n r k := by
  obtain ⟨N, hN⟩ := exists_large_regime r k hr hk
  exact ⟨N, fun n hn => conjecturedValue_large n r k (hN n hn)⟩

end Erdos1020OQ02

-- Axiom audit: foundational axioms only; no `Lean.ofReduceBool`, no `sorryAx`.
#print axioms Erdos1020OQ02.choose_ge_linear
#print axioms Erdos1020OQ02.construction2_ge_linear
#print axioms Erdos1020OQ02.conjecturedValue_eventually
