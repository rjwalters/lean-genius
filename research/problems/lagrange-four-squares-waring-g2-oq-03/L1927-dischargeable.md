# Finding: `ThreeSquares.lean:1927` sorry is dischargeable from the EASY direction

**Session**: researcher-1, 2026-06-14 (both Aristotle + Docker backends DOWN)
**Status**: ORIENT-sharpening. Math reduction verified by hand; Lean NOT build-verified
(no build host available). Path-disjoint from open PR #24149 (which targets the hard
"if" axiom `not_excluded_form_is_sum_three_sq`, a different proof obligation).

## The sorry

```lean
-- ThreeSquares.lean:1925
theorem needs_four_iff_excluded (n : ℕ) (hn : n ≥ 1) :
    squaresNeeded n = 4 ↔ IsExcludedForm n := by
  sorry -- Requires full three-squares theorem
```

where

```lean
open Classical in
noncomputable def squaresNeeded (n : ℕ) : ℕ :=
  if n = 0 then 0
  else if ∃ a : ℕ, a ^ 2 = n then 1
  else if ∃ a b : ℕ, a ^ 2 + b ^ 2 = n then 2
  else if ¬IsExcludedForm n then 3
  else 4
```

## The misleading comment

The inline comment `-- Requires full three-squares theorem` says this needs the HARD
direction (the axiom `not_excluded_form_is_sum_three_sq : ¬IsExcludedForm n → ∃ a b c, ...`,
exactly what PR #24149 is scoping). **It does not.** The lemma is decidable purely from
the EASY direction, which is already a fully-proved theorem in the file:

```lean
-- ThreeSquares.lean:185 (PROVEN, no axiom)
theorem excluded_form_not_sum_three_sq {n : ℕ} (h : IsExcludedForm n) :
    ¬∃ a b c : ℤ, a ^ 2 + b ^ 2 + c ^ 2 = n
```

## Why the easy direction suffices

`squaresNeeded n = 4 ↔ IsExcludedForm n`:

- **Forward** (`= 4 → IsExcludedForm n`): purely definitional. In `squaresNeeded`, the
  value `4` is reachable only in the final `else`, which is guarded by `¬(¬IsExcludedForm n)`.
  So `split_ifs` on the hypothesis hands back `¬¬IsExcludedForm n`; conclude by `not_not`.
  No three-squares fact of any kind is used.

- **Backward** (`IsExcludedForm n → = 4`): with `hex : IsExcludedForm n` and `hn : n ≥ 1`,
  evaluate the four `if`-guards:
  - `n ≠ 0` from `hn`.
  - `¬ ∃ a : ℕ, a²=n`: a perfect square `a²=n` gives the integer 3-square rep
    `(a:ℤ)²+0²+0² = n`, contradicting `excluded_form_not_sum_three_sq hex`.
  - `¬ ∃ a b : ℕ, a²+b²=n`: a 2-square rep gives `(a:ℤ)²+(b:ℤ)²+0² = n`, same contradiction.
  - The `¬IsExcludedForm n` guard is false directly from `hex`.
  All earlier branches fail and the last guard fails, so the value is `4`.

Key observation: a sum of ≤ 3 squares is a sum of exactly 3 squares (pad with zeros), so
`excluded_form_not_sum_three_sq` alone rules out the 1- and 2-square branches. The hard
"if" direction (`not_excluded_form_is_sum_three_sq`) is never invoked.

## Ready-to-apply proof sketch (NOT build-verified — fix casts at build time)

```lean
theorem needs_four_iff_excluded (n : ℕ) (hn : n ≥ 1) :
    squaresNeeded n = 4 ↔ IsExcludedForm n := by
  have hn0 : n ≠ 0 := Nat.one_le_iff_ne_zero.mp hn
  unfold squaresNeeded
  constructor
  · intro h
    split_ifs at h with h0 h1 h2 h3
    · exact absurd h3 (not_not.mp (by simpa using h3))  -- final-branch guard ⇒ IsExcludedForm
  · intro hex
    have hno3 := excluded_form_not_sum_three_sq hex
    have hno1 : ¬ ∃ a : ℕ, a ^ 2 = n := by
      rintro ⟨a, ha⟩; exact hno3 ⟨a, 0, 0, by push_cast; rw [← ha]; push_cast; ring⟩
    have hno2 : ¬ ∃ a b : ℕ, a ^ 2 + b ^ 2 = n := by
      rintro ⟨a, b, hab⟩; exact hno3 ⟨a, b, 0, by push_cast; rw [← hab]; push_cast; ring⟩
    rw [if_neg hn0, if_neg hno1, if_neg hno2, if_neg (not_not.mpr hex)]
```

The fiddly, build-gated parts are exactly: the `split_ifs`/`not_not` shape in the forward
branch, and the `ℕ→ℤ` casts in `hno1`/`hno2` (`push_cast` + `exact_mod_cast` should close
them but were not run). This is why it is shipped as a sketch, not a live edit — replacing
a `sorry` with code that has not compiled would break the build.

## ACT recommendation

When a build host (Docker or Aristotle) returns: apply the proof above, run
`./proofs/scripts/docker-build.sh Proofs.ThreeSquares`, and on success remove the
misleading `-- Requires full three-squares theorem` comment. This discharges one of the
file's sorries WITHOUT depending on the hard axiom #24149 is scoping, so the two efforts
do not block each other.
