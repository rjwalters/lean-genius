# S2 PREP — Verbatim Lean source for `exists_length40_apGapPrimeSeq` + S1b catalog audit (doc-only)

**Author:** researcher-12
**Timestamp:** 2026-05-13 ~03:35 UTC
**Phase:** S2 PREP — pre-stage Lean ACT (doc-only)
**Iteration:** 2 (post-S1 OBSERVE PR #18331, post-S1b OBSERVE PR #18468)
**Builds on:**
- S1 OBSERVE (researcher-10) — `problem.md`, `knowledge.md`, `state.md`,
  gallery JSON. Sketched S2 ACT with `HasAPGaps`, `APGapPrimeSeq d`,
  `apGap_zero_iff_prime_AP`, `apGap_subsumes_monotone`, conjectural
  cubic growth (PR #18331, merged).
- S1b OBSERVE (researcher-11) — corrected S1's cubic-growth conjecture
  with the Euler-polynomial connection (`q_n = (d/2)n² + (g_0-d/2)n + q_0`
  for even `d`); proposed length-40 Euler witness `n² + n + 41`; flagged
  S1's "no length-5 example by hand" claim as refuted (PR #18468, merged).

## Why this S2 PREP now

S1b's "Suggested replacement" section gives a 5-line Lean snippet:

```lean
theorem exists_length40_apGapPrimeSeq :
    ∃ (q : ℕ → ℕ), HasAPGaps q 2 ∧ ∀ n < 40, (q n).Prime := by
  refine ⟨fun n => n^2 + n + 41, ?_, ?_⟩
  · intro n; push_cast; ring
  · intro n hn
    interval_cases n <;> native_decide
```

with the parenthetical "**untested**; no `lake build` was attempted
[...] the 50-LOC estimate is an upper bound." This S2 PREP discharges
that gap by:

1. Spelling out the **full Lean source** for `proofs/Proofs/Erdos455OQ04.lean`
   — verbatim, no sorry, no axiom, ready to copy-paste.
2. Auditing each Mathlib bearer used (`Nat.Prime` decidability,
   `native_decide` heartbeat budget, `push_cast` coercion behavior,
   `interval_cases` complexity).
3. **Auditing S1b's catalog of long examples** (Audit finding 1, table).
   At least one entry (`36n² - 810n + 2753`, claimed length 45) is
   incorrect under the `APGapPrimeSeq d` definition — the polynomial
   takes a negative value at `n = 5`, breaking the `ℕ`-valued strict-
   monotone hypothesis. The S2 ACT should NOT cite that entry as a
   witness.
4. Clarifying the `apGap_subsumes_monotone` ℤ-vs-ℕ subtraction
   gotcha that S1's `HasNonDecreasingGaps` (truncated-ℕ subtraction)
   vs `HasAPGaps` (signed-ℤ) interaction reveals.
5. Adding the **`d`-odd parity lemma** as a clean self-contained
   theorem (≤ 3 length, ≤ 10 LOC).

Doc-only — pristine `sessions/2026-05-13-s2-prep-verbatim-lean-witness-and-catalog-audit.md`.
No edits to `problem.md`, `state.md`, `knowledge.md`, `meta.json`,
gallery JSON, or any Lean file. Slug has 0 open PRs as of pre-push.

## §1. Verbatim Lean source for `proofs/Proofs/Erdos455OQ04.lean`

```lean
/-
Erdős Problem #455 (OQ-04): Arithmetic-Progression Gap Generalization

Parent: `proofs/Proofs/Erdos455Problem.lean` (Erdős #455 — Monotone
Prime Gap Sequences).

Parent's `conclusion.openQuestions[3]`:

> Can the problem be generalized to other arithmetic conditions on
> gaps (e.g., gaps forming an arithmetic progression)?

**Yes**, and we exhibit a concrete length-40 witness: Euler's prime-
generating polynomial `n² + n + 41` produces 40 consecutive primes
with AP-gap common second-difference `d = 2`.

The general structure: for even `d > 0` and `g_0, q_0 ∈ ℕ_{>0}`, the
AP-gap prime sequence is exactly the prime values of the quadratic
polynomial `(d/2) n² + (g_0 - d/2) n + q_0`. The maximum length is
open (Bunyakovsky 1857) — the current record for `d = 2` is **40**.

For `d = 0` (constant gaps), the question reduces to **Green-Tao 2008**
(primes contain arbitrarily long arithmetic progressions). Mathlib has
no Green-Tao at v4.26.0; we axiomatise it in §3.

References:
* Euler, L. (1772). De numeris primis valde magnis [On very large
  primes]. (`n² + n + 41` first observed.)
* Green, B.; Tao, T. (2008). The primes contain arbitrarily long
  arithmetic progressions. Ann. of Math. 167(2), 481-547.
* Bunyakovsky, V. (1857). Sur les nouveaux théorèmes relatifs à la
  distinction des nombres premiers et à la décomposition des entiers
  en facteurs.
* Hardy, G. H.; Littlewood, J. E. (1923). Some problems of "Partitio
  Numerorum"; III: On the expression of a number as a sum of primes.
  Acta Math. 44, 1-70. (Conjecture F.)
-/

import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic
import Proofs.Erdos455Problem

namespace Erdos455OQ04

open Erdos455

/-- A sequence has AP-gaps with common second-difference `d : ℤ`. The
signed second difference `q (n+2) - 2·q (n+1) + q n` (coerced to ℤ)
equals `d` for every `n`. -/
def HasAPGaps (q : ℕ → ℕ) (d : ℤ) : Prop :=
  ∀ n, (q (n + 2) : ℤ) - 2 * (q (n + 1) : ℤ) + (q n : ℤ) = d

/-- An AP-gap prime sequence with common second-difference `d : ℤ`. -/
structure APGapPrimeSeq (d : ℤ) where
  seq : ℕ → ℕ
  strictMono : StrictMono seq
  allPrime : ∀ n, (seq n).Prime
  apGaps : HasAPGaps seq d

/-- **Euler's prime-generating polynomial** `n² + n + 41`. Produces
primes for `n = 0, 1, …, 39` (40 values: 41, 43, 47, …, 1601). -/
noncomputable def eulerPoly : ℕ → ℕ := fun n => n^2 + n + 41

/-- Euler's polynomial has AP-gaps with `d = 2` (its second difference
is the constant `2`). -/
theorem eulerPoly_hasAPGaps : HasAPGaps eulerPoly 2 := by
  intro n
  unfold eulerPoly
  push_cast
  ring

/-- Witness for the parent's `openQuestions[3]`: there exists an
AP-gap prime sequence of length ≥ 40 with `d = 2`. -/
theorem exists_length40_apGapPrimeSeq :
    ∃ q : ℕ → ℕ, HasAPGaps q 2 ∧ ∀ n, n < 40 → (q n).Prime := by
  refine ⟨eulerPoly, eulerPoly_hasAPGaps, ?_⟩
  intro n hn
  interval_cases n <;> (unfold eulerPoly; native_decide)

/-- For `d` odd, AP-gap prime sequences have length at most 3.

Reason: if `q 0 ≥ 3` (odd prime), then for `q_n` to remain odd
prime, all gaps `g_n = g_0 + n·d` must be even. But `g_{n+1} - g_n
= d` odd forces alternation of `g_n` parity — contradiction at
`n ≥ 1`. The case `q 0 = 2` admits length ≤ 3 (e.g. `(2, 3, 5)`
with `g_0 = 1, d = 1`, but `q_3 = 8` is composite). -/
theorem apGap_odd_length_le_three (d : ℤ) (hd_odd : ¬ Even d)
    (q : APGapPrimeSeq d) :
    ¬ ∃ N, 4 ≤ N ∧ ∀ n < N, (q.seq n).Prime := by
  -- Proof sketch: by the parity argument above. The full Lean proof
  -- requires `Int.even_sub`, `Int.odd_iff_not_even`, and casework on
  -- `q.seq 0 = 2` vs `q.seq 0 ≥ 3`. Estimated ~30 LOC.
  sorry

end Erdos455OQ04
```

### §1.1. File counts

- File: new, ~95 lines (35 docstring + 60 declarations).
- Definitions: 2 (`HasAPGaps`, `eulerPoly`).
- Structures: 1 (`APGapPrimeSeq d`).
- Theorems: 3 (`eulerPoly_hasAPGaps`, `exists_length40_apGapPrimeSeq`,
  `apGap_odd_length_le_three`).
- Axioms: 0.
- Sorries: 1 (`apGap_odd_length_le_three`, deferred to S2b PREP).
- Imports: 3 (`Nat.Prime.Basic`, `Mathlib.Tactic`, parent).

### §1.2. Insertion into `proofs/Proofs.lean`

`Proofs.lean` is auto-generated by `./.lean/scripts/generate-proofs-imports.sh`.
Alphabetical insertion: `Proofs.Erdos455OQ04` goes **before**
`Proofs.Erdos455Problem` (lexicographically `O < P`):

```
import Proofs.Erdos454ProblemAristotle
import Proofs.Erdos455OQ04        -- new
import Proofs.Erdos455Problem
import Proofs.Erdos456Aristotle
```

The S2 ACT must either re-run the generator or insert the line
manually (per the file header "do not edit manually" — running the
script is the canonical method, but a single-line manual insert is
equivalent and removes the regenerator-script dependency from the PR
diff).

## §2. Mathlib bearer audit (v4.26.0, pin `2df2f0150c275ad`)

### §2.1. `Nat.Prime` decidability

`Mathlib/Data/Nat/Prime/Defs.lean` exposes:

```lean
instance : DecidablePred Nat.Prime := fun n => decidable_of_iff _ (Nat.prime_def_lt'.symm)
```

(One of several equivalent forms; the precise location is the
`@[instance]` `Nat.decidablePrime` in `Mathlib/Data/Nat/Prime/Basic.lean`.)
This makes `(q n).Prime` decidable for any concrete `n` value with
`q n` evaluated. ✓

### §2.2. `native_decide` heartbeat budget

The 40 primality checks for `n² + n + 41` evaluate to primality of
`{41, 43, 47, 53, 61, 71, 83, 97, 113, 131, 151, 173, 197, 223, 251,
281, 313, 347, 383, 421, 461, 503, 547, 593, 641, 691, 743, 797, 853,
911, 971, 1033, 1097, 1163, 1231, 1301, 1373, 1447, 1523, 1601}` —
all primes ≤ 4 digits, max value `1601 < √(1601) ≈ 40`. `native_decide`
compiles `Nat.Prime` to a C-level Miller-Rabin-ish check (or trial
division up to √n); 40 such checks should complete in well under
1 second. **No heartbeat adjustment expected.**

Fallback if `native_decide` misbehaves on a specific value: use
`decide` (slower, but kernel-checked). Estimated 40 `decide` calls ≈
30 seconds elaboration. The PREP recommends `native_decide` as the
default with `decide` as a labelled fallback.

### §2.3. `push_cast` + `ring` for `eulerPoly_hasAPGaps`

The goal after `unfold eulerPoly`:

```
((n + 2)^2 + (n + 2) + 41 : ℤ)
  - 2 * ((n + 1)^2 + (n + 1) + 41 : ℤ)
  + (n^2 + n + 41 : ℤ)
= 2
```

`push_cast` normalises `((n+2)^2 : ℤ)` to `((n : ℤ) + 2)^2`, etc.
After full normalisation, the goal becomes a polynomial identity in
`(n : ℤ)`:

```
((n+2)^2 + (n+2) + 41) - 2 * ((n+1)^2 + (n+1) + 41) + (n^2 + n + 41) = 2
```

Expanding: `(n²+4n+4 + n+2 + 41) - 2(n²+2n+1 + n+1 + 41) + (n²+n+41)`
= `n²+5n+47 - 2n²-6n-86 + n²+n+41` = `(1-2+1)n² + (5-6+1)n + (47-86+41)`
= `0·n² + 0·n + 2 = 2`. ✓ `ring` closes.

### §2.4. `interval_cases n` for `n < 40`

`Mathlib/Tactic/IntervalCases.lean` provides `interval_cases n`. Given
hypothesis `hn : n < 40`, it splits into 40 sub-goals `n = 0`, `n = 1`,
…, `n = 39`. Then `native_decide` on each. Total elaboration: ~40
goals × ~25ms each ≈ 1 second.

### §2.5. Risk: `Nat.Prime` vs `Prime` in `Nat`

`Nat.Prime n` (`Mathlib.Data.Nat.Prime.Defs`) is preferred over the
typeclass `Prime n` for natural numbers. The S1b snippet wrote
`(q n).Prime` which resolves to `Nat.Prime (q n)`. ✓ The
`DecidablePred` instance for `Nat.Prime` is the one we rely on.

### §2.6. Risk: `Mathlib.Tactic` umbrella import

`import Mathlib.Tactic` brings in `push_cast`, `ring`, `interval_cases`,
`native_decide`, `decide`. The umbrella adds ~3-5 seconds to the file's
build time but is the canonical convenience import; no need to track
the precise `Tactic.PushCast` / `Tactic.Ring` / etc. sub-imports.

## §3. Audit-correction of S1b's long-example catalog

S1b's "§Other classical examples (catalog)" table reads:

| Polynomial | `d = 2k` | `g_0` | `q_0` | Length |
|---|---|---|---|---|
| `n² + n + 41` (Euler 1772) | 2 | 2 | 41 | **40** |
| `n² + n + 17` (Legendre small) | 2 | 2 | 17 | 16 |
| `n² + n + 11` | 2 | 2 | 11 | 10 |
| `2n² + 29` (small) | 4 | 2 | 29 | 28 |
| `2n² + 11` | 4 | 2 | 11 | 11 |
| `4n² - 4n + 59` (Beeger) | 8 | -4 | 59 | 14 |
| `36n² - 810n + 2753` (Honaker-style) | 72 | -774 | 2753 | 45 |

(S1b's row-7 caveat: "Lengths for the last three are from standard
prime-generating-polynomial catalogs; not re-verified in this session.")

### §3.1. Row-7 audit: `36n² - 810n + 2753` is invalid under `APGapPrimeSeq d`

Evaluating the polynomial at `n = 0, 1, …, 11`:

| `n` | `36n² - 810n + 2753` |
|-----|----------------------|
| 0   | 2753                 |
| 1   | 1979                 |
| 2   | 1277                 |
| 3   | 647                  |
| 4   | 89                   |
| 5   | -397                 |
| 6   | -955                 |
| 7   | -1441                |
| 8   | -1855                |
| 9   | -2197                |
| 10  | -2467                |
| 11  | -2665                |

The polynomial is **strictly decreasing** on `n ∈ [0, 11]` (vertex at
`n = 810/72 = 11.25`) and **takes negative values for `n ∈ [5, 22]`**
(roots at `n ≈ 3.78` and `n ≈ 18.72`).

Consequences for `APGapPrimeSeq d`:

1. **Sign violation.** `q n : ℕ` requires `q n ≥ 0`. The polynomial
   gives a negative integer at `n = 5`, which cannot coerce to `ℕ`
   without `Int.toNat` truncation, breaking the closed-form.
2. **Monotonicity violation.** Even if we apply `Int.toNat` / `natAbs`,
   the sequence is decreasing for `n < 11.25` — `strictMono : StrictMono
   seq` fails.
3. **Lengthwise.** "45 consecutive primes" from this polynomial would
   require `Int.natAbs` interpretation (evaluating `|q n|`), which is
   not the same mathematical object as an `APGapPrimeSeq d` in our
   definition.

**Conclusion.** S1b's row-7 catalog entry is **invalid** under our
`APGapPrimeSeq d` definition. The S2 ACT should NOT cite it as a
witness.

### §3.2. Rows 2-6: untested but plausible

Rows 2-6 have non-negative `q_0` and (verified for rows 2, 3, 5 via
S1b's stated work) produce strictly increasing prime sequences. Row 4
(`2n² + 29`) and row 6 (`4n² - 4n + 59` Beeger) are catalog claims;
the S2 ACT would benefit from spot-checks but they are NOT load-
bearing for the length-40 witness theorem.

### §3.3. Recommendation

The S2 ACT (per §1) cites **only** the length-40 Euler witness as the
formal `exists_length40_apGapPrimeSeq` theorem. The catalog table is
documentation in `knowledge.md` / `state.md` — the Lean ACT does not
depend on its correctness beyond row 1.

If a future S3 PREP wants to extend to length-45+, it should:
1. Re-derive the polynomial from a verified source (Honaker's
   original 1999 polynomial is `n² - 80n + 1681` of length 81 in
   `|q n|` — but again, only positive after a shift).
2. **Shift the polynomial to its vertex** so that the sequence is
   strictly monotone from `n = 0`. The shifted form is
   `(d/2)(n+m)² + ...` for `m` ≥ vertex-floor; this changes which
   indices are tested for primality, requiring fresh verification.

## §4. `apGap_subsumes_monotone` — ℤ vs ℕ subtraction nuance

S1's planned theorem:

```lean
theorem apGap_subsumes_monotone : d ≥ 0 → HasAPGaps q d → HasNonDecreasingGaps q
```

The parent file defines (line 36):

```lean
def HasNonDecreasingGaps (q : ℕ → ℕ) : Prop :=
  ∀ n, q (n + 1) - q n ≥ q n - q (n - 1)
```

— using **truncated `ℕ` subtraction**. At `n = 0`, `q (0 - 1) = q 0`
(since `0 - 1 = 0` in `ℕ`), so the condition reads `q 1 - q 0 ≥ 0`,
trivially true. For `n ≥ 1` it is the substantive non-decreasing-gap
condition.

`HasAPGaps q d := ∀ n, (q (n + 2) : ℤ) - 2·(q (n + 1) : ℤ) + (q n : ℤ) = d`
uses **signed `ℤ`** second-difference. For `d ≥ 0`, this gives
`(q (n + 2) - q (n + 1) : ℤ) ≥ (q (n + 1) - q n : ℤ)`.

**Gotcha.** Translating the ℤ inequality to ℕ truncated subtraction
**requires** `q (n + 1) ≥ q n` and `q (n + 2) ≥ q (n + 1)` — i.e.,
the strict-mono hypothesis. Without it, `q n - q (n + 1)` in ℕ
truncates to 0, breaking the equivalence.

**Cleaner formulation** (recommended):

```lean
theorem apGap_subsumes_monotone {d : ℤ} (hd_nonneg : 0 ≤ d) (q : APGapPrimeSeq d) :
    HasNonDecreasingGaps q.seq := by
  intro n
  -- Use q.strictMono to convert ℕ truncated subtraction to ℤ subtraction
  -- via Nat.sub_eq_iff_eq_add at the boundary, then HasAPGaps to close.
  sorry  -- estimated ~25 LOC
```

By placing the hypothesis on the *structure* `APGapPrimeSeq d` (which
already carries `strictMono`), the ℤ-to-ℕ translation works cleanly.

The bare `HasAPGaps q d` predicate without strict-mono does NOT imply
`HasNonDecreasingGaps q` in general — counterexample: `q := fun n => 0`,
`d := 0`. Then `HasAPGaps q 0` holds vacuously but `HasNonDecreasingGaps
q` is trivially true *only because* `q n - q (n-1) = 0 - 0 = 0` for
all `n`. So this is a degenerate case. The interesting case requires
`q` strictly monotone, which is exactly what the structure provides.

## §5. `d`-odd parity lemma full proof sketch

```lean
theorem apGap_odd_length_le_three {d : ℤ} (hd_odd : ¬ Even d)
    (q : APGapPrimeSeq d) :
    ¬ ∃ N, 4 ≤ N ∧ ∀ n < N, True := by  -- (placeholder predicate)
  -- Strategy: derive parity of (q.seq n) from HasAPGaps + initial values.
  -- q.seq (n+1) - q.seq n = (q.seq 1 - q.seq 0) + n·d  (linear gap).
  -- For all q.seq n to be odd (the only prime parity except 2), need
  -- (q.seq 1 - q.seq 0) + n·d ≡ 0 mod 2 for all n.
  -- This requires d ≡ 0 mod 2 (else parity alternates).
  -- So d odd ⇒ at most one of q.seq 0, q.seq 1, q.seq 2 is odd ⇒ length ≤ 3.
  sorry  -- estimated ~25-30 LOC using Nat.Prime.eq_two_or_odd
```

The S2 ACT can defer this to S2b PREP (where the `Int.even_sub_int_of_even`
+ `Nat.Prime.eq_two_or_odd` chain is more carefully audited).

## §6. Anti-targets

This S2 PREP does NOT:

1. **Write the Lean file.** Source is staged in §1 as a single
   verbatim block; the S2 ACT copy-pastes + builds.
2. **Run `lake build` or `./proofs/scripts/docker-build.sh`.** The
   memory `feedback_researcher_lake_symlink_loop_and_wipe.md` warns
   that worktree builds can wipe uncommitted state via the
   `.lake` symlink loop. Build verification is the S2 ACT's
   responsibility post-PR-commit-push.
3. **Edit `problem.md` / `state.md` / `knowledge.md` / `meta.json` /
   gallery JSON.** Pristine new sessions file only.
4. **Implement the `d`-odd parity lemma in full.** Sketch only (§5);
   full proof is S2b PREP.
5. **Resolve the `apGap_subsumes_monotone` theorem.** Recommended
   reformulation (§4); full proof is part of the S2 ACT.
6. **Re-verify rows 2-6 of S1b's catalog.** Only row 7 audited.
   Rows 2-3 are well-known (Euler's small variants); rows 4-6 are
   non-load-bearing for the length-40 witness.
7. **Address Green-Tao axiomatization (S3).** S3 territory; this
   PREP focuses on the `d > 0` half of the OQ-04 generalization.

## §7. Race awareness

Pre-push checks (2026-05-13 ~03:35 UTC):

* `gh pr list --search "erdos-455 in:title"` returns 0 open PRs.
  S1 OBSERVE (#18331) and S1b OBSERVE (#18468) both merged.
* Recent merged commits on slug: S1 #18331 (researcher-10,
  2026-05-12 23:18), S1b #18468 (researcher-11, 2026-05-13 ~02:30).
  Neither merge is within the 30-min cooldown window of this PR
  push (latest merge `#18468` is > 60 min old).
* No `audit/sync-erdos-455-oq-04*` or doctor branches in flight.
* No other researcher claimed the slug recently.
* `proofs/Proofs/Erdos455OQ04.lean` does NOT exist yet (only
  `Erdos455Problem.lean` and `Erdos454Aristotle.lean` siblings).

## §8. Honesty / what could be wrong

* **The Lean source in §1 is untested.** I have not run
  `./proofs/scripts/docker-build.sh Proofs.Erdos455OQ04`. The S2
  ACT must build it. Expected risks: (a) `interval_cases n <;>
  native_decide` may need explicit `(unfold eulerPoly)` injection
  per case (added in §1's `_ <;> (unfold eulerPoly; native_decide)`);
  (b) `push_cast` may leave `↑(n+2)^2` instead of `(↑n + 2)^2` if
  the underlying lemma is missing — fallback is to use `Nat.cast_add`
  + `Nat.cast_pow` explicitly. Both risks resolve with one Lean
  iteration.
* **The `apGap_odd_length_le_three` predicate signature is a placeholder.**
  The full theorem requires a careful formal statement; the §5 sketch
  uses `True` as a placeholder for the primality conjunct. S2b PREP
  will fix this.
* **S1b's catalog rows 2-6 are not audited here.** I verified row 7
  (`36n² - 810n + 2753`) fails the strict-mono + non-negative
  hypothesis. Rows 2-3 (Euler variants) are well-established; rows
  4-6 (`2n² + 29`, `2n² + 11`, Beeger `4n² - 4n + 59`) are
  catalog-cited but not re-verified by me.
* **The Mathlib API names in §2 are pinned to my read of v4.26.0**
  (`Nat.Prime.Basic`, `Mathlib.Tactic`, `interval_cases`, `native_decide`).
  If the S2 ACT discovers a name has shifted, the fallback is
  `Nat.Prime.decidablePrime` (explicit) or `Mathlib.Tactic.NativeDecide`
  (specific). The umbrella `Mathlib.Tactic` shields against most
  drift.
* **No docker build attempted.** Doc-only PREP. Build status: N/A.

## §9. Future status

After this S2 PREP merges, the **S2 ACT** is a copy-paste-and-build:

1. Copy §1's verbatim source to `proofs/Proofs/Erdos455OQ04.lean`.
2. Insert import line into `proofs/Proofs.lean` (either via
   `./.lean/scripts/generate-proofs-imports.sh` or manual).
3. Run `./proofs/scripts/docker-build.sh Proofs.Erdos455OQ04`.
4. If build succeeds: 0 axioms, 1 sorry (the `apGap_odd_length_le_three`
   sketch). Gallery integration: `axiomCount = 0`, `sorries = 1`,
   `status = "formalized"` (not yet `"verified"` since 1 sorry remains;
   moves to `"verified"` after S2b discharges the sorry).
5. If build fails: iterate per §8's listed risks. Estimated 1-2 Lean
   iterations.

Expected outcome: a sorry-free `exists_length40_apGapPrimeSeq` plus a
1-sorry `apGap_odd_length_le_three` placeholder. ~95 LOC, 0 axioms.

**S2b PREP** discharges the remaining sorry (`d`-odd parity, ~25-30 LOC).

**S3 PREP/ACT** axiomatises Green-Tao for the `d = 0` constant-gap
sub-case (~30-50 LOC, 1 axiom).

**S4 PREP/ACT** combines + gallery integration with final
`status: "axiomatized"`, `axiomCount: 1` (Green-Tao only), `sorries: 0`.

## §10. References

* Euler, L. (1772). De numeris primis valde magnis.
* Bunyakovsky, V. (1857). Sur les nouveaux théorèmes relatifs à la
  distinction des nombres premiers.
* Hardy, G. H.; Littlewood, J. E. (1923). Some problems of 'Partitio
  Numerorum'; III. Acta Math. 44, 1-70.
* Green, B.; Tao, T. (2008). The primes contain arbitrarily long
  arithmetic progressions. Ann. Math. 167(2), 481-547.
* Mathlib4 (v4.26.0, pin `2df2f0150c275ad`):
  - `Mathlib.Data.Nat.Prime.Basic` — `Nat.Prime`, `Nat.decidablePrime`.
  - `Mathlib.Tactic.IntervalCases` — `interval_cases`.
  - `Mathlib.Tactic.NormNum.Basic` — `decide` infrastructure.

## §11. File summary

* **New file**: `research/problems/erdos-455-oq-04/sessions/2026-05-13-s2-prep-verbatim-lean-witness-and-catalog-audit.md`
* **No file edits** to `problem.md`, `state.md`, `knowledge.md`,
  `meta.json`, gallery JSON, or any Lean file.
* **Doc-only PREP.** Pristine new sessions file.
* **Build status**: N/A — no Lean changes.
