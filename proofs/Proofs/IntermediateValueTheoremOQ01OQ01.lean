import Proofs.IntermediateValueTheoremOQ01
import Mathlib

/-
# Sign Persistence of the Bisection Method (intermediate-value-theorem-oq-01-oq-01)

## Research Problem

The parent entry `intermediate-value-theorem-oq-01` formalizes the bisection
method — the recursive interval `bisectIter`, its endpoints `bisectLeft` /
`bisectRight`, and the width-decay law `bisectRight − bisectLeft = (b−a)/2ⁿ`.
It leaves open its **first** stated question:

  > Prove sign persistence: `f(aₙ) · f(bₙ) ≤ 0` at each step.

This is the *invariant* that makes the bisection method correct: it is precisely
the hypothesis "`f` changes sign on `[aₙ, bₙ]`" that, via the IVT, certifies a
root inside every interval the method produces. The parent proves that the
intervals shrink; this file proves that they never lose the root.

## What This Proves

1. `sign_persist_aux` — the pure sign-algebra lemma: from `p·q ≤ 0` and
   `0 < p·m` deduce `m·q ≤ 0`. (If the sign is kept on the left half it is
   immediate; on the right half this lemma transfers it.)
2. `bisectStep_sign_persist` — one bisection step preserves `f a · f b ≤ 0`.
3. `bisect_sign_persist` — **the invariant**: `f(aₙ)·f(bₙ) ≤ 0` for all `n`.
4. `bisect_le` — the bisection intervals stay ordered (`aₙ ≤ bₙ`).
5. `sign_change_root` — IVT corollary: a continuous sign-changing function has
   a root in `[a,b]`.
6. `bisect_interval_contains_root` — combining 3 + 4 + 5: **every** bisection
   interval contains a genuine root of a continuous `f`.
7. `bisect_sqrt2_sign_persist` — the invariant holds for `x² − 2` on `[1,2]`.
-/

namespace BisectionMethod

open Real

-- ============================================================
-- Part I: The sign-algebra core
-- ============================================================

/-- **Sign-transfer lemma.** If `p·q ≤ 0` (a sign change between `p` and `q`)
    and `0 < p·m` (so `m` has the *same* sign as `p`), then `m·q ≤ 0` — the
    sign change is inherited by the pair `(m, q)`.

    Proof: `(p·m)·(m·q) = (p·q)·m² ≤ 0` while `p·m > 0`, forcing `m·q ≤ 0`. -/
theorem sign_persist_aux {p m q : ℝ} (hpq : p * q ≤ 0) (hpm : 0 < p * m) :
    m * q ≤ 0 := by
  nlinarith [mul_nonpos_of_nonpos_of_nonneg hpq (sq_nonneg m), hpm,
    sq_nonneg m]

-- ============================================================
-- Part II: One step preserves the sign change
-- ============================================================

/-- A single bisection step preserves the sign-change invariant: if
    `f a · f b ≤ 0` then `f` still changes sign across the chosen sub-interval. -/
theorem bisectStep_sign_persist {f : ℝ → ℝ} {a b : ℝ} (hsign : f a * f b ≤ 0) :
    f (bisectStep f a b).1 * f (bisectStep f a b).2 ≤ 0 := by
  simp only [bisectStep]
  split_ifs with h
  · -- left half (a, mid): the chosen condition IS the goal
    exact h
  · -- right half (mid, b): transfer the sign via sign_persist_aux
    push_neg at h
    exact sign_persist_aux hsign h

-- ============================================================
-- Part III: The invariant for all n
-- ============================================================

/-- **Sign persistence.** If `f` changes sign on the initial interval
    (`f a · f b ≤ 0`), then it changes sign on every bisection interval:
    `f(aₙ) · f(bₙ) ≤ 0` for all `n`. This is the correctness invariant of the
    bisection method. -/
theorem bisect_sign_persist {f : ℝ → ℝ} {a b : ℝ} (hsign : f a * f b ≤ 0) :
    ∀ n : ℕ, f (bisectLeft f a b n) * f (bisectRight f a b n) ≤ 0 := by
  intro n
  induction n with
  | zero => simpa [bisectLeft, bisectRight, bisectIter] using hsign
  | succ n ih =>
      have step := bisectStep_sign_persist (f := f)
        (a := bisectLeft f a b n) (b := bisectRight f a b n) ih
      simpa [bisectLeft, bisectRight, bisectIter] using step

-- ============================================================
-- Part IV: The intervals stay ordered
-- ============================================================

/-- Every bisection interval is non-degenerate: `aₙ ≤ bₙ`. (Follows from the
    parent's width law `bisect_width`, since `(b−a)/2ⁿ ≥ 0`.) -/
theorem bisect_le {f : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b) (n : ℕ) :
    bisectLeft f a b n ≤ bisectRight f a b n := by
  have hw := bisect_width f a b hab n
  have hnn : (0 : ℝ) ≤ (b - a) / 2 ^ n := by
    have : (0 : ℝ) ≤ b - a := by linarith
    positivity
  linarith [hw]

-- ============================================================
-- Part V: IVT corollary — every interval contains a root
-- ============================================================

/-- **IVT for sign changes.** A continuous function that changes sign across
    `[a,b]` (i.e. `f a · f b ≤ 0`) has a root in `[a,b]`. -/
theorem sign_change_root {f : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hf : ContinuousOn f (Set.Icc a b)) (hsign : f a * f b ≤ 0) :
    ∃ c ∈ Set.Icc a b, f c = 0 := by
  rcases mul_nonpos_iff.mp hsign with ⟨hfa, hfb⟩ | ⟨hfa, hfb⟩
  · -- 0 ≤ f a and f b ≤ 0 : use the descending IVT
    have h0 : (0 : ℝ) ∈ Set.Icc (f b) (f a) := ⟨hfb, hfa⟩
    obtain ⟨c, hc, hfc⟩ := intermediate_value_Icc' hab hf h0
    exact ⟨c, hc, hfc⟩
  · -- f a ≤ 0 and 0 ≤ f b : use the ascending IVT
    have h0 : (0 : ℝ) ∈ Set.Icc (f a) (f b) := ⟨hfa, hfb⟩
    obtain ⟨c, hc, hfc⟩ := intermediate_value_Icc hab hf h0
    exact ⟨c, hc, hfc⟩

/-- **The bisection method never loses the root.** For a continuous `f` with an
    initial sign change, *every* bisection interval `[aₙ, bₙ]` contains a true
    root of `f`. Together with the parent's width decay (`bisect_width`), this
    is the full correctness statement: the intervals shrink to zero width while
    each one is certified to contain a root. -/
theorem bisect_interval_contains_root {f : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hf : Continuous f) (hsign : f a * f b ≤ 0) (n : ℕ) :
    ∃ c ∈ Set.Icc (bisectLeft f a b n) (bisectRight f a b n), f c = 0 :=
  sign_change_root (bisect_le hab n) (hf.continuousOn) (bisect_sign_persist hsign n)

-- ============================================================
-- Part VI: Concrete instance — √2
-- ============================================================

/-- Sign persistence for `f(x) = x² − 2` on `[1,2]` (the √2 search of the
    parent entry): `f` changes sign on every bisection interval. -/
theorem bisect_sqrt2_sign_persist (n : ℕ) :
    (fun x => x ^ 2 - 2) (bisectLeft (fun x => x ^ 2 - 2) 1 2 n) *
      (fun x => x ^ 2 - 2) (bisectRight (fun x => x ^ 2 - 2) 1 2 n) ≤ 0 := by
  have h : (fun x => x ^ 2 - 2) (1 : ℝ) * (fun x => x ^ 2 - 2) (2 : ℝ) ≤ 0 := by
    norm_num
  exact bisect_sign_persist (f := fun x => x ^ 2 - 2) (a := 1) (b := 2) h n

/-- Consequently every bisection interval of the `x² − 2` search on `[1,2]`
    contains a genuine root (namely √2). -/
theorem bisect_sqrt2_contains_root (n : ℕ) :
    ∃ c ∈ Set.Icc (bisectLeft (fun x => x ^ 2 - 2) 1 2 n)
        (bisectRight (fun x => x ^ 2 - 2) 1 2 n),
      c ^ 2 - 2 = 0 := by
  have hcont : Continuous (fun x : ℝ => x ^ 2 - 2) := by continuity
  have := bisect_interval_contains_root (f := fun x => x ^ 2 - 2)
    (a := 1) (b := 2) (by norm_num) hcont (by norm_num) n
  simpa using this

end BisectionMethod
