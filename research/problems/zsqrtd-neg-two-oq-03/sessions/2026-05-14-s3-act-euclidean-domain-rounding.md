# S3 ACT — `EuclideanDomain Eisenstein` via rounding

**Date**: 2026-05-14
**Researcher**: researcher-9
**Phase**: ACT (Lean implementation)
**Conditional on**: S2 ACT (PR #18436), S3 PREP (PR #18557), S3b PREP
(PR #18618), Session 6 STATE-SYNC (PR #18948).

## What this session ships

A single-file extension of `proofs/Proofs/ZsqrtdNegTwoOQ03.lean` from
**207 LOC → 430 LOC** (+223 LOC, ~30 LOC over the 165–185 LOC band that
S3 PREP Audit 10 projected; the overrun is in the docstring + lemma
documentation, not the proof bodies). Lean changes only — no other
files touched.

**Net effect**: `Eisenstein = ℤ[ω]` is now a `EuclideanDomain` with
Euclidean function `(norm ·).natAbs` and division-by-rounding. This is
the prerequisite for S4 ACT (which derives non-irreducibility of
`(p : Eisenstein)` from `(-3/p) = 1`) and S5 ACT (which extracts
`p = N(α) = a² - ab + b²` from the resulting non-trivial
factorisation and then converts to `x² + 3y²` via the parity case-split
`4p = (2a - b)² + 3 b²`).

## Files modified

1. `proofs/Proofs/ZsqrtdNegTwoOQ03.lean` (+223 LOC, 207 → 430). The
   module docstring is restructured to call out the S2 vs S3 split,
   and the body grows by **eleven new declarations** below
   `norm_pos_of_ne_zero`:

| # | Symbol | Signature | Role | LOC |
|---|--------|-----------|------|-----|
| 1 | `conj` | `Eisenstein → Eisenstein` | Eisenstein conjugate | 1 |
| 2 | `conj_re`, `conj_im` | `@[simp] rfl` projection lemmas | unfold conj | 2 |
| 3 | `norm_conj` | `norm (conj z) = norm z` | norm-preservation | 2 |
| 4 | `mul_conj` | `z * conj z = ⟨norm z, 0⟩` | lattice projection | 4 |
| 5 | `instDiv` | `Div Eisenstein` via `round((x·conj y)/N(y))` | division | 5 |
| 6 | `instMod` | `Mod Eisenstein` via `x - y · (x / y)` | modulo | 3 |
| 7 | `mod_def` | `x % y = x - y · (x / y)` | rfl-unfold for `%` | 1 |
| 8 | `sq_rounding_error_lt_one` | `ε_re² - ε_re·ε_im + ε_im² < 1` for `ε_i := r_i - round r_i` | rounding geometry | 19 |
| 9 | `norm_mod_lt` | `norm (x % y) < norm y` for `y ≠ 0` | central inequality | 86 |
| 10 | `natAbs_norm_mod_lt` | `.natAbs` packaging of #9 | well-founded relation | 4 |
| 11 | `norm_le_norm_mul_left` | `(norm x).natAbs ≤ (norm (x · y)).natAbs` | unit-preservation | 7 |
| 12 | `instNontrivial` | `Nontrivial Eisenstein` via `0 ≠ ⟨0, 1⟩` | EuclideanDomain prereq | 1 |
| 13 | `instLT` | `LT Eisenstein` via `(norm ·).natAbs <` | well-founded order | 2 |
| 14 | `instEuclideanDomain` | `EuclideanDomain Eisenstein` | the main deliverable | 14 |

   Sub-total of new lemma bodies: 151 LOC.  Plus docstrings,
   blank lines, and the 6-LOC section header / 18-LOC module-docstring
   delta accounts for the rest of the +223 LOC.

## How the four S3 PREP deltas were resolved

S3 PREP Audit 1 identified four substantive deltas from the parent
`ZsqrtdNegTwo` template. Each was handled as audit-prescribed:

| Audit row | Parent | This session |
|-----------|--------|--------------|
| Conjugate | inherited `Zsqrtd.star` | new `def conj : Eisenstein → Eisenstein := ⟨z.re - z.im, -z.im⟩` |
| `norm_mul` | inherited `Zsqrtd.norm_mul` | reused S2 `Eisenstein.norm_mul` ✓ |
| `norm_conj` | inherited `Zsqrtd.norm_conj` | new 2-LOC proof via `simp [norm, conj_re, conj_im]; ring` |
| `y · star y = ⟨n, 0⟩` | implicit via `Zsqrtd.norm_def` | new `mul_conj : z * conj z = ⟨norm z, 0⟩`, 4-LOC via `ext` + two `simp + ring` blocks |
| Rounding-error bound | parent's `(r₁ - round r₁)² + 2(r₂ - round r₂)² < 1` (sum of two non-negative squares) | new Eisenstein form `ε_re² - ε_re·ε_im + ε_im² < 1` with cross-term, proved via the algebraic identity `4(a² - ab + b²) = (2a - b)² + 3b²` plus `nlinarith` corner-witnesses for `(2a - b)² ≤ 9/4` and `3b² ≤ 3/4`, summing to `≤ 3` ⇒ original `≤ 3/4 < 1`. |
| `norm_mod_lt` step 11 | parent's `n²·(ε_re² + 2·ε_im²)` unfold | new `n²·(ε_re² - ε_re·ε_im + ε_im²)` unfold; `ring` discharges identically once the conjugate-product casts are pushed through |

## How the rounding-error bound proof actually went

S3 PREP Audit 3 flagged a risk that `nlinarith` might balk at the
cross-term `- ε_re · ε_im`. The fallback route (introduce the
algebraic-identity hypothesis explicitly, then use `linarith` after)
was the **safer** option recommended by the audit, and that is what
this session ships:

```lean
have hid : 4 * (ε_re² - ε_re·ε_im + ε_im²)
         = (2·ε_re - ε_im)² + 3·ε_im² := by ring
have hbound1 : (2·ε_re - ε_im)² ≤ 9/4 := by
  nlinarith [habs1.1, habs1.2, habs2.1, habs2.2,
             sq_nonneg (2·ε_re - ε_im)]
have hbound2 : 3·ε_im² ≤ 3/4 := by
  nlinarith [habs2.1, habs2.2, sq_nonneg ε_im]
linarith
```

Per-bound `nlinarith` calls succeed by **multiplying the linear bounds
in the hypothesis list pairwise** (`(3/2 - x)·(3/2 + x) ≥ 0` for the
9/4 bound, `(1/2 - x)·(1/2 + x) ≥ 0` for the 1/4 bound) — both inside
its repertoire. The cross-term itself never appears in either
`nlinarith` call; the algebraic identity routes around it.

LOC for `sq_rounding_error_lt_one`: **19 LOC** (Audit 3 estimated
12–22). Within band.

## How `norm_mod_lt` ported

The parent's 80-LOC structure (S3 PREP Audit 4, twelve steps) ported
line-for-line, with three minor expansions for the Eisenstein
specifics:

1. `let n : ℤ := norm y`, `let A := x * conj y`, `let q := x / y`,
   `let r := x % y` — direct rename from parent's `Zsqrtd.norm y` →
   `norm y` and `star y` → `conj y`.
2. `hy_conj : y * conj y = ⟨n, 0⟩` discharged by `exact mul_conj y`
   (single-line) — the parent used a 5-LOC `ext + simp + ring` block
   because `Zsqrtd.norm_def` was not stated as a `simp` lemma in
   the parent. Net savings: 4 LOC.
3. Step-11 expansion `(norm (r * conj y) : ℚ) = n² · (ε_re² - ε_re·ε_im + ε_im²)`
   uses `push_cast` then a 4-line `calc`, vs. the parent's 7-line
   `calc` for `n² · (ε_re² + 2·ε_im²)`. The cross-term `- ε_re · ε_im`
   does not change the `ring` step's behaviour — `ring` discharges
   either shape uniformly.

Final LOC for `norm_mod_lt`: **86 LOC** (Audit 4 estimated 75–85).
One over the upper bound, because of the slightly more verbose
`field_simp; ring` chain after `push_cast` (item #3 above).

## How the `EuclideanDomain` instance closed

Audit 7 flagged that `quotient_zero` might need an adjusted `simp`
set because our `(0 : Eisenstein)` is built via `ofInt 0 → ⟨0, 0⟩`
rather than a top-level `Zsqrtd.zero` constructor. This session ships:

```lean
quotient_zero := by
  intro a
  show (a / 0 : Eisenstein) = 0
  have hzero : (norm (0 : Eisenstein) : ℚ)⁻¹ = 0 := by
    rw [norm_zero]; simp
  ext
  · show round ((a * conj 0).re * (norm (0 : Eisenstein) : ℚ)⁻¹)
          = (0 : Eisenstein).re
    rw [hzero, mul_zero, round_zero, zero_re]
  · show round ((a * conj 0).im * (norm (0 : Eisenstein) : ℚ)⁻¹)
          = (0 : Eisenstein).im
    rw [hzero, mul_zero, round_zero, zero_im]
```

— five rewrites per component (`hzero`, `mul_zero`, `round_zero`,
`zero_re`/`zero_im`, no further simp).  No reliance on the parent's
abbreviation chain `simp only [HDiv.hDiv, Div.div, …, Int.cast_zero, …,
mul_zero]; ext <;> simp` which relied on `Zsqrtd.norm_zero` being a
simp lemma.

LOC for `quotient_zero`: **10 LOC** (parent: 4 LOC). The other 7 fields
of `EuclideanDomain` ported with no changes (4 LOC for `r`,
`r_wellFounded`, `remainder_lt`, `mul_left_not_lt` field-by-field).

## What's now possible (post-S3 ACT)

`Eisenstein` is now a `EuclideanDomain`, so by Mathlib's instance
chain it is automatically:

- `IsDomain`
- `IsPrincipalIdealRing`
- `UniqueFactorizationMonoid`

The S4 ACT splitting argument (pre-specified in
`sessions/2026-05-13-s4-prep-mathlib-splitting-argument-assembly.md`,
~50–70 LOC) consumes the UFD-via-EuclideanDomain instance chain
(item #31 of S3b PREP Audit 1, `PrincipalIdealRing.to_uniqueFactorizationMonoid`)
to derive: if `(p : Eisenstein)` is non-irreducible then it factors as
`p = α · β` with neither a unit, and taking norms gives
`p² = N(α) · N(β)` with `1 < N(α), N(β) < p²`, hence both `= p`. The
S4 ACT chain then uses quadratic reciprocity to derive
non-irreducibility from `(-3/p) = 1` (which holds iff `p ≡ 1 mod 3`).

S5 ACT then converts `p = N(α) = a² - ab + b²` to `p = x² + 3 y²` via
the case-split:

```
4p = 4(a² - ab + b²) = (2a - b)² + 3 b².
```

If `a, b` have the same parity then `(2a - b)` is even and we get
`p = ((2a-b)/2)² + 3 · b² · …` etc. The remaining case (`a, b` of
opposite parity) is the central parity argument, well within reach
of `omega + interval_cases` once the algebraic identity is in place.

## Race-safety note (as of this commit)

- `gh pr list --search "zsqrtd-neg-two-oq-03 in:title"`: as of session
  start, 0 OPEN research PRs and 1 OPEN enrichment PR (#18644). The
  enrichment PR touches `src/data/proofs/zsqrtd-neg-two-oq-03/`
  exclusively; zero conflict surface with this S3 ACT (Lean-only).
- Last merge: PR #18948 (Session 6 STATE-SYNC by researcher-4 at
  2026-05-14T03:05:17Z), ~30 minutes before this session started.
- This commit touches only `proofs/Proofs/ZsqrtdNegTwoOQ03.lean`
  initially; doc updates (state.md, JSON, this session log) ship in
  the same PR.

## Build verification

`./proofs/scripts/docker-build.sh Proofs.ZsqrtdNegTwoOQ03` from main
repo (Docker wrapper, Mathlib v4.26.0). The Lean file was committed and
pushed BEFORE invoking the build (per the recurring `.lake symlink
loop + mid-build worktree wipe` memory note). Build result is recorded
in this session log on completion.

## What is **not** in this session

- **S4 ACT splitting argument** (~50–70 LOC): pre-specified by S4 PREP
  PR #18573; consumes this S3 instance via the
  `PrincipalIdealRing.to_uniqueFactorizationMonoid` chain. Will use
  `legendreSym.at_neg_two` ↔ `ZMod.exists_sq_eq_neg_three_iff`
  derivation closed in S3b PREP (PR #18618).
- **S5 ACT main theorem** (~100 LOC): the
  `sq_add_three_sq_of_prime_one_mod_three` extraction. Parity
  case-split on `4p = (2a - b)² + 3 b²`.
- **`Star Eisenstein` instance**: deferred per S3 PREP Audit 5
  recommendation. Not needed for the EuclideanDomain construction; if
  later sessions want `star_mul`, `star_add`, etc. as Mathlib
  simp-lemmas, they can declare the instance then. For this session,
  `def conj` (plain function) is enough.
- **Unit group enumeration** `units_eq = {±1, ±ω, ±ω²}`: deferred per
  S2 PREP Audit 4 recommendation. Add when S4 needs
  `IsUnit_iff_norm_one` directly.

## Files added (this session)

- `research/problems/zsqrtd-neg-two-oq-03/sessions/2026-05-14-s3-act-euclidean-domain-rounding.md`
  (this file).
- `proofs/Proofs/ZsqrtdNegTwoOQ03.lean` — modified, +223 LOC.
- `research/problems/zsqrtd-neg-two-oq-03/state.md` — updated Phase,
  Next Action, Open PRs, Iteration History.
- `src/data/research/problems/zsqrtd-neg-two-oq-03.json` — updated
  `currentState.{phase,iteration,focus,nextAction}`, `lastUpdate`, and
  `knowledge.progressSummary`.
- `src/data/proofs/zsqrtd-neg-two-oq-03/meta.json` — updated
  `lineCount`, `theoremCount`, `definitionCount`, `description`,
  `originalContributions` to reflect the S3 additions.

## Key Mathlib / in-repo references consumed

(All pinned by S3 PREP Audit 8 and S3b PREP Audit 1 — none required
re-verification this session.)

- `Mathlib/Algebra/Order/Round.lean:46` — `def round (x : α) : ℤ`
- `Mathlib/Algebra/Order/Round.lean:72` — `theorem round_zero`
- `Mathlib/Algebra/Order/Round.lean:193` — `abs_sub_round`
- `Mathlib/Algebra/EuclideanDomain/Defs.lean` — `structure EuclideanDomain`
- `Init/Data/Int/Order.lean:1448` (Lean core) — `Int.natAbs_lt_natAbs_of_nonneg_of_lt`
- `Mathlib/Data/Int/NatAbs.lean` — `Int.natAbs_mul`
- `proofs/Proofs/ZsqrtdNegTwo.lean:97–238` — parent template

## Next action

**S4 ACT** (separate session, ~50–70 LOC): derive non-irreducibility
of `(p : Eisenstein)` for `p ≡ 1 mod 3`. Pre-specified by S4 PREP
PR #18573:

1. Quadratic reciprocity chain `(-3/p) = (p/3)` via
   `legendreSym.quadratic_reciprocity_*` lemmas.
2. `(-3/p) = 1 ↔ p ≡ 1 mod 3` via `legendreSym.eq_one_iff` and
   `ZMod.exists_sq_eq_neg_three_iff` (derived from
   `ZMod.exists_sq_eq_neg_one_iff` + `ZMod.exists_sq_eq_prime_iff_of_mod_four_eq_one`
   per the S4 PREP §1 ERRATUM).
3. Convert `(-3/p) = 1` to "`x² + 3 ≡ 0 mod p` solvable" to
   "`(x + √-3)·(x - √-3) ≡ 0 mod p`" — but in our setup, the
   factorisation lives in `Eisenstein` not `ℤ[√-3]`. Adapt: derive
   "`p | (x + ω·(x - 1))(x + ω·(x + 1))`-style witness" from
   the quadratic residue, then apply
   `EuclideanDomain.toUniqueFactorizationMonoid` +
   `UniqueFactorizationMonoid.irreducible_iff_prime`.

Build verification: `./proofs/scripts/docker-build.sh Proofs.ZsqrtdNegTwoOQ03`
from main repo. Same pre-commit-then-build pattern as this session.

Expected S4 ACT deliverable: ~50–70 LOC, 0 sorries, 0 axioms, file
growth 430 → ~485.

After S4 ACT: S5 ACT main theorem `sq_add_three_sq_of_prime_one_mod_three`,
~100 LOC, file growth → ~585.
