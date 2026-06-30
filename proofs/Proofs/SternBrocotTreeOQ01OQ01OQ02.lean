import Mathlib
import Proofs.SternBrocotTreeOQ01OQ01

/-!
# The continued fraction of an arbitrary rational, via Stern–Brocot
(`stern-brocot-tree-oq-01-oq-01-oq-02`)

## Open question (OQ-02 of `stern-brocot-tree-oq-01-oq-01`)
The parent (`stern-brocot-tree-oq-01-oq-01`) proved the *forward* direction of the
Stern–Brocot/continued-fraction correspondence: a run-length list `qs : List ℕ`
produces the convergent `cfValFrom true qs : ℤ × ℤ`, and the rational
`cfQFrom true qs : ℚ` unfolds as the regular continued fraction
`q₀ + 1/(q₁ + 1/(q₂ + ⋯))` (`cfQFrom_two_cons`).  The grandparent
(`stern-brocot-tree-oq-01`) established the bijection between Stern–Brocot paths
`List Bool` and reduced positive rationals (`sb_surjective`, `sb_bijection`).

What was *missing* is the **inverse**: does *every* positive rational arise this
way?  Equivalently, does every `q ∈ ℚ`, `q > 0`, have a (finite) continued-fraction
expansion captured by some run-length list?

## Answer: YES — `cfQFrom true` is surjective onto the positive rationals.

The headline `exists_cf_of_rat` shows that for every `r : ℚ` with `0 < r` there is a
run-length list `qs` with `cfQFrom true qs = r`.  Together with the parent's recurrence
`cfQFrom_two_cons`, the entries of `qs` *are* the continued-fraction partial quotients
of `r`, so this literally produces the continued fraction of an arbitrary positive
rational.

## The bridge
The only genuinely new ingredient is **run-length encoding** of a Stern–Brocot path:
`path_eq_runs` shows every `p : List Bool` equals `runsToPathFrom b qs` for some start
move `b` and run-lengths `qs`, and `exists_runs_true` normalises the start to an
`R`-run (absorbing a leading `L`-run as the partial quotient `q₀ = 0`).  Chaining this
with the grandparent's surjectivity (every reduced positive `a/b` is a path label) and
`Rat.num_div_den` (an arbitrary `r` *is* `r.num / r.den` in lowest terms) closes the loop.

Mathlib has **no** Stern–Brocot development (verified by the parent against the v4.26
checkout); this result is obtained inside the parent's verified continued-fraction
framework rather than re-derived through `Mathlib.Algebra.ContinuedFractions`.

## Status
All theorems proved with `0` sorries and `0` axioms (no `native_decide`).
-/

namespace SternBrocot

/-! ## Part I: run-length encoding of an arbitrary path -/

/-- **Run-length encoding.** Every Stern–Brocot path `p : List Bool` is the
run-structured path of some start move `b` and run-length list `qs`:
`runsToPathFrom b qs = p`.  Proved by structural induction, peeling one move at a
time and either extending the leading run (`c = b`) or opening a fresh run
(`c ≠ b`, where the previous start `b = !c`). -/
theorem path_eq_runs :
    ∀ p : List Bool, ∃ (b : Bool) (qs : List ℕ), runsToPathFrom b qs = p := by
  intro p
  induction p with
  | nil => exact ⟨true, [], rfl⟩
  | cons c p' ih =>
    obtain ⟨b, qs, hpath⟩ := ih
    by_cases hcb : c = b
    · subst hcb
      cases qs with
      | nil =>
        refine ⟨c, [1], ?_⟩
        rw [← hpath]; simp [runsToPathFrom]
      | cons n ns =>
        refine ⟨c, (n + 1) :: ns, ?_⟩
        rw [← hpath]
        simp [runsToPathFrom, List.replicate_succ]
    · refine ⟨c, 1 :: qs, ?_⟩
      have hbc : (!c) = b := by cases c <;> cases b <;> simp_all
      rw [← hpath]
      simp [runsToPathFrom, hbc]

/-- Normalised run-length encoding: every path is `runsToPathFrom true qs` for some
`qs` (a leading `L`-run is absorbed as the partial quotient `q₀ = 0`). -/
theorem exists_runs_true (p : List Bool) :
    ∃ qs : List ℕ, runsToPathFrom true qs = p := by
  obtain ⟨b, qs, hpath⟩ := path_eq_runs p
  cases b with
  | true => exact ⟨qs, hpath⟩
  | false => exact ⟨0 :: qs, by rw [← hpath]; simp [runsToPathFrom]⟩

/-! ## Part II: the continued-fraction value as a quotient of path labels -/

/-- The rational value `cfQFrom true qs` is the quotient of the Stern–Brocot labels of
the corresponding `R`-started run-structured path. -/
theorem cfQFrom_true_eq_div (qs : List ℕ) :
    cfQFrom true qs
      = (sbNum (runsToPathFrom true qs) : ℚ) / (sbDen (runsToPathFrom true qs) : ℚ) := by
  simp only [cfQFrom]
  rw [sbNum_runs, sbDen_runs]

/-! ## Part III: surjectivity onto the positive rationals -/

/-- **Headline.** Every positive rational has a finite continued-fraction expansion
recorded by a run-length list: for all `r : ℚ` with `0 < r`, there is `qs : List ℕ`
with `cfQFrom true qs = r`.  By the parent's `cfQFrom_two_cons`, the entries of `qs`
are the continued-fraction partial quotients of `r`. -/
theorem exists_cf_of_rat (r : ℚ) (hr : 0 < r) :
    ∃ qs : List ℕ, cfQFrom true qs = r := by
  -- `r` is `r.num / r.den` in lowest terms, with positive numerator and denominator.
  have h0 : 0 < r.num := Rat.num_pos.mpr hr
  have hden : 0 < r.den := r.pos
  have hcop : IsCoprime (r.num) (r.den : ℤ) := by
    rw [Int.isCoprime_iff_gcd_eq_one]
    simpa [Int.gcd, Int.natAbs_natCast] using r.reduced
  -- Surjectivity of the Stern–Brocot tree gives a path with these labels.
  obtain ⟨p, hp1, hp2⟩ :=
    sb_surjective r.num (r.den : ℤ) (by omega) (by exact_mod_cast hden) hcop
  -- Run-length encode the path and read off the continued fraction.
  obtain ⟨qs, hqs⟩ := exists_runs_true p
  refine ⟨qs, ?_⟩
  rw [cfQFrom_true_eq_div, hqs, hp1, hp2]
  exact_mod_cast Rat.num_div_den r

/-! ## Part IV: concrete continued-fraction expansions -/

/-- `1/2` is the value of the run-length list `[0, 1]`: a leading `q₀ = 0` (the value is
`< 1`) followed by an `L`-run of length `1`.  Continued fraction `0 + 1/(1 + 1/1)`. -/
theorem cfQ_half : cfQFrom true [0, 1] = 1 / 2 := by
  have h : cfValFrom true [0, 1] = (1, 2) := by decide
  rw [cfQFrom, h]; norm_num

/-- `5/3` is the value of the all-ones run-length list `[1, 1, 1]` (the Fibonacci ratio,
slowest continued fraction), matching the parent's `cfQ_fib`. -/
theorem cfQ_five_thirds : cfQFrom true [1, 1, 1] = 5 / 3 := cfQ_fib

/-- Sanity check on the headline: `7/5` does have a continued-fraction expansion. -/
example : ∃ qs : List ℕ, cfQFrom true qs = 7 / 5 := exists_cf_of_rat _ (by norm_num)

/-
═══════════════════════════════════════════════════════════════════════════════
VERIFICATION
═══════════════════════════════════════════════════════════════════════════════ -/

#check @path_eq_runs
#check @exists_runs_true
#check @cfQFrom_true_eq_div
#check @exists_cf_of_rat

end SternBrocot
