import Mathlib

/-!
# Nested Closed Intervals Shrinking to a Point

This file answers the **first** open question recorded on the parent entry
`compactness-finite-subcover-oq-01-oq-02` ("The Finite-Intersection Dual and
Cantor's Intersection Theorem").

The parent's concrete real instance shows only that the nested intervals
`[0, 1/(n+1)]` have **nonempty** intersection (a corollary of Cantor's
intersection theorem).  Here we *pin the intersection exactly*:

> **`nested_intervals_iInter_singleton`** — for a `Monotone` left endpoint `a`,
> an `Antitone` right endpoint `b` with `a n ≤ b n` and lengths
> `b n - a n → 0`, the intersection `⋂ n, [a n, b n]` is the **singleton**
> `{⨆ n, a n}`.

Cantor's theorem (the parent's content) supplies *nonemptiness*; the new content
here is the **uniqueness** half — the shrinking-length hypothesis forces any two
common points to coincide via the squeeze `|x - y| ≤ b n - a n → 0`.  Together
they upgrade "nonempty" to "exactly one point", and that point is identified
concretely as the supremum of the left endpoints (equivalently the infimum of
the right endpoints).

The concrete corollary `iInter_Icc_zero_one_div_eq_zero` then sharpens the
parent's `[0, 1/(n+1)]` example from "nonempty" to the exact value `{0}`.
-/

open Set Filter Topology

namespace CompactnessFiniteSubcoverOq01Oq02Oq01

/-- **Nested closed intervals shrinking to a point.**

Let `a` be a monotone (non-decreasing) sequence of left endpoints and `b` an
antitone (non-increasing) sequence of right endpoints with `a n ≤ b n` for every
`n`, and suppose the lengths `b n - a n` tend to `0`.  Then the intersection of
the nested closed intervals `[a n, b n]` is the single point `⨆ n, a n`.

The supremum exists because every `a m` lies below every `b n` (so `b 0` bounds
the range of `a`); that same cross bound `a m ≤ b n` places the supremum inside
every interval.  Uniqueness is the shrinking-length squeeze: any common point `x`
satisfies `|x - (⨆ n, a n)| ≤ b n - a n` for all `n`, and the right side tends to
`0`. -/
theorem nested_intervals_iInter_singleton
    (a b : ℕ → ℝ) (ha : Monotone a) (hb : Antitone b)
    (hab : ∀ n, a n ≤ b n)
    (hlen : Tendsto (fun n => b n - a n) atTop (𝓝 0)) :
    ⋂ n, Icc (a n) (b n) = {⨆ n, a n} := by
  -- Every left endpoint lies below every right endpoint.
  have key : ∀ m n, a m ≤ b n := by
    intro m n
    rcases le_total m n with h | h
    · exact (ha h).trans (hab n)
    · exact (hab m).trans (hb h)
  -- Hence the range of `a` is bounded above (by `b 0`), so the supremum exists.
  have hbdd : BddAbove (Set.range a) := ⟨b 0, by rintro _ ⟨m, rfl⟩; exact key m 0⟩
  have hac : ∀ n, a n ≤ ⨆ j, a j := fun n => le_ciSup hbdd n
  have hcb : ∀ n, (⨆ j, a j) ≤ b n := fun n => ciSup_le (fun m => key m n)
  apply Set.eq_singleton_iff_unique_mem.2
  refine ⟨?_, ?_⟩
  · -- The supremum belongs to every interval, hence to the intersection.
    simp only [mem_iInter, mem_Icc]
    exact fun n => ⟨hac n, hcb n⟩
  · -- Any common point equals the supremum, by the shrinking-length squeeze.
    intro x hx
    simp only [mem_iInter, mem_Icc] at hx
    have hbound : ∀ n, |x - ⨆ j, a j| ≤ b n - a n := by
      intro n
      rw [abs_le]
      exact ⟨by linarith [(hx n).1, hcb n], by linarith [(hx n).2, hac n]⟩
    have h0 : |x - ⨆ j, a j| ≤ 0 := ge_of_tendsto' hlen hbound
    have : x - ⨆ j, a j = 0 := abs_nonpos_iff.1 h0
    linarith

/-- **Sharp value of the parent's concrete example.**

The nested real intervals `[0, 1/(n+1)]` intersect in *exactly* `{0}` — the
parent entry established only that this intersection is nonempty.  Specialising
`nested_intervals_iInter_singleton` with constant left endpoint `0` and right
endpoint `1/(n+1)` (antitone, with `1/(n+1) → 0`) yields the singleton; the
supremum of the constant-`0` left endpoints is `0`. -/
theorem iInter_Icc_zero_one_div_eq_zero :
    ⋂ n : ℕ, Icc (0 : ℝ) (1 / (n + 1)) = {0} := by
  have hanti : Antitone (fun n : ℕ => 1 / ((n : ℝ) + 1)) := by
    intro m n hmn
    have : (m : ℝ) ≤ n := by exact_mod_cast hmn
    apply one_div_le_one_div_of_le <;> linarith
  have hab : ∀ n : ℕ, (fun _ : ℕ => (0 : ℝ)) n ≤ (fun n : ℕ => 1 / ((n : ℝ) + 1)) n := by
    intro n; positivity
  have hlen : Tendsto (fun n : ℕ => (fun n => 1 / ((n : ℝ) + 1)) n - (fun _ => (0 : ℝ)) n)
      atTop (𝓝 0) := by
    simpa using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have h := nested_intervals_iInter_singleton (fun _ => (0 : ℝ))
      (fun n => 1 / ((n : ℝ) + 1)) monotone_const hanti hab hlen
  rw [show (⨆ _n : ℕ, (0 : ℝ)) = 0 from ciSup_const] at h
  simpa using h

end CompactnessFiniteSubcoverOq01Oq02Oq01
