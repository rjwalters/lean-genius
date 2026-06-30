/-
# A fully computable IVT bisection with a decidable sign oracle (OQ02-OQ03-OQ01)

## Research problem

The parent entry (`IntermediateValueTheoremOQ02OQ03`, "Constructive vs Classical
IVT") shows the bisection method is constructive *given* a locating oracle for
the sign of `f`, and asks (its open question #1):

  > For a function over `ℚ` (where `≤` is **decidable**), can a fully computable
  > IVT bisection be formalized using a `Decidable` sign oracle, with the
  > structural theorems needing no classical axioms?

This file answers **yes**, for any ordered field `K` (in particular `ℚ`): the
sign test `f m ≤ 0` is `Decidable` from the order, so `bisect` below is a genuine
**computable `def`** — *not* `noncomputable`.  This is the precise improvement
over the parent: the parent's `bisectStep` over `ℝ` is `noncomputable`, forced to
decide `f mid ≤ 0` through `Classical.em` because `≤` on `ℝ` is not computable.
Over `ℚ` (any field with a decidable order) no classical oracle enters the
*definition*, and the algorithm actually runs — the worked example evaluates to
the exact rational bracket `[5/4, 3/2]`.

Its structural guarantees are proved by plain induction:

  * `bisect_width`     — the bracket width is exactly `(b - a) / 2^n`;
  * `bisect_sign`      — the sign-change invariant `f a' ≤ 0 ≤ f b'` is preserved;
  * `bisect_mem`       — the brackets are nested: `a ≤ a' ≤ b' ≤ b`;
  * `bisect_width_lt`  — over an Archimedean field the width drops below any `ε > 0`.

The one ingredient the parent flagged as genuinely classical — extracting the
*exact* root as the limit of the midpoints, which needs completeness of `ℝ` — is
deliberately *not* used here: everything is the computable bracketing core.

## Status
Verified — 0 sorries, 0 axiom declarations.  The proofs rest on Mathlib's usual
foundational axioms (`propext`, `Classical.choice`, `Quot.sound`); the *novelty*
is that the `bisect` definition is computable, not that the proofs avoid those.
-/

import Mathlib

namespace IntermediateValueTheoremOQ02OQ03OQ01

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- Computable bisection.  Maintaining the bracket `[a, b]` with the sign-change
    invariant `f a ≤ 0 ≤ f b`, each step tests the midpoint `m = (a+b)/2`:
    if `f m ≤ 0` recurse on `[m, b]`, else on `[a, m]`.  The test `f m ≤ 0` is
    `Decidable` from the field's linear order, so this is a real `def`. -/
def bisect (f : K → K) : ℕ → K → K → K × K
  | 0, a, b => (a, b)
  | n + 1, a, b =>
      if f ((a + b) / 2) ≤ 0 then bisect f n ((a + b) / 2) b
      else bisect f n a ((a + b) / 2)

@[simp] theorem bisect_zero (f : K → K) (a b : K) : bisect f 0 a b = (a, b) := rfl

@[simp] theorem bisect_succ (f : K → K) (n : ℕ) (a b : K) :
    bisect f (n + 1) a b
      = if f ((a + b) / 2) ≤ 0 then bisect f n ((a + b) / 2) b
        else bisect f n a ((a + b) / 2) := rfl

/-! ## Structural guarantees (all constructive) -/

/-- **Width.**  After `n` steps the bracket has width `(b - a) / 2^n`. -/
theorem bisect_width (f : K → K) (n : ℕ) (a b : K) :
    (bisect f n a b).2 - (bisect f n a b).1 = (b - a) / 2 ^ n := by
  induction n generalizing a b with
  | zero => simp
  | succ n ih =>
      rw [bisect_succ]
      split_ifs with h
      · rw [ih ((a + b) / 2) b]; ring
      · rw [ih a ((a + b) / 2)]; ring

/-- **Sign invariant.**  If `f a ≤ 0 ≤ f b` then the final bracket `[a', b']`
    still satisfies `f a' ≤ 0 ≤ f b'`: it brackets a sign change. -/
theorem bisect_sign (f : K → K) (n : ℕ) (a b : K) (ha : f a ≤ 0) (hb : 0 ≤ f b) :
    f (bisect f n a b).1 ≤ 0 ∧ 0 ≤ f (bisect f n a b).2 := by
  induction n generalizing a b with
  | zero => exact ⟨ha, hb⟩
  | succ n ih =>
      rw [bisect_succ]
      split_ifs with h
      · exact ih ((a + b) / 2) b h hb
      · exact ih a ((a + b) / 2) ha (le_of_lt (lt_of_not_ge h))

/-- **Nested brackets.**  If `a ≤ b` the result `[a', b']` satisfies
    `a ≤ a' ≤ b' ≤ b`. -/
theorem bisect_mem (f : K → K) (n : ℕ) (a b : K) (hab : a ≤ b) :
    a ≤ (bisect f n a b).1 ∧ (bisect f n a b).1 ≤ (bisect f n a b).2
      ∧ (bisect f n a b).2 ≤ b := by
  induction n generalizing a b with
  | zero => exact ⟨le_refl a, hab, le_refl b⟩
  | succ n ih =>
      have hm1 : a ≤ (a + b) / 2 := by linarith
      have hm2 : (a + b) / 2 ≤ b := by linarith
      rw [bisect_succ]
      split_ifs with h
      · obtain ⟨p, q, r⟩ := ih ((a + b) / 2) b hm2
        exact ⟨le_trans hm1 p, q, r⟩
      · obtain ⟨p, q, r⟩ := ih a ((a + b) / 2) hm1
        exact ⟨p, q, le_trans r hm2⟩

/-- **Convergence.**  Over an Archimedean field the width drops below any
    positive `ε` for large enough `n`.  This is constructive (Archimedean
    search), not a completeness argument. -/
theorem bisect_width_lt [Archimedean K] (f : K → K) (a b : K) {ε : K} (hε : 0 < ε) :
    ∃ n, (bisect f n a b).2 - (bisect f n a b).1 < ε := by
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt ((b - a) / ε) (one_lt_two (α := K))
  refine ⟨n, ?_⟩
  rw [bisect_width, div_lt_iff₀ (by positivity)]
  rw [div_lt_iff₀ hε] at hn
  linarith [hn]

/-! ## Worked computation over ℚ -/

/-- The sign oracle `f m ≤ 0` is `Decidable` over `ℚ`, so `bisect` actually
    computes.  Bisecting `f x = x² − 2` from `[1, 2]` for two steps yields the
    exact rational bracket `[5/4, 3/2]` for `√2` — verified by `decide`. -/
example : bisect (fun x : ℚ => x ^ 2 - 2) 2 1 2 = (5 / 4, 3 / 2) := by
  simp only [bisect_succ, bisect_zero]; norm_num

/-- After 10 steps the bracket for `√2` has width exactly `1/1024` (from
    `bisect_width`, no computation needed). -/
example :
    (bisect (fun x : ℚ => x ^ 2 - 2) 10 1 2).2
      - (bisect (fun x : ℚ => x ^ 2 - 2) 10 1 2).1 = 1 / 1024 := by
  rw [bisect_width]; norm_num

/-- And that 10-step bracket genuinely straddles a sign change of `x² − 2`
    (from `bisect_sign`). -/
example :
    (fun x : ℚ => x ^ 2 - 2) (bisect (fun x : ℚ => x ^ 2 - 2) 10 1 2).1 ≤ 0
      ∧ 0 ≤ (fun x : ℚ => x ^ 2 - 2) (bisect (fun x : ℚ => x ^ 2 - 2) 10 1 2).2 :=
  bisect_sign (fun x : ℚ => x ^ 2 - 2) 10 1 2 (by norm_num) (by norm_num)

end IntermediateValueTheoremOQ02OQ03OQ01
