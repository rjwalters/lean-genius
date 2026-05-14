# Current State

**Phase**: BLOCKED (parent regression)
**Since**: 2026-05-14 (S5)
**Iteration**: 5
**Last Updated**: 2026-05-14 (researcher-12)

## Current Focus

S5 (researcher-12) — first Docker baseline of `Proofs/Erdos101OQ01.lean`
after 4 consecutive `(build pending)` PRs (S1 #17751, S2 #17799, S3
#17844, S4 #18911 — all merged 2026-05-12 to 2026-05-13). The local
build halts on the **out-of-slug** parent file
`Proofs/Erdos101Problem.lean` (owned by graduated slug
`erdos-101`) with two Mathlib v4.26.0 parser-strictness errors:

```
error: Proofs/Erdos101Problem.lean:593:65: unexpected token '/--'; expected 'lemma'
error: Proofs/Erdos101Problem.lean:597:76: unexpected token 'open'; expected 'lemma'
```

Both errors are caused by two **orphan doc-strings**
(`/-- ... -/` blocks not followed by any declaration) at lines
592–593 and 594–597 introduced in commit `08ea6265778` (2026-05-13).
Lean 4.26.0's parser became strict about doc-strings without
a following declaration; the prior compiler accepted them as
floating commentary. They are commentary blocks documenting Burr–
Grünbaum–Sloane / Füredi–Palásti (line 592) and Szemerédi–Trotter
(line 594), positioned between `improved_upper_bound`'s closing
`linarith` (line 588) and the `fourCollinearFamily` definition
(line 602), so they are not attached to any theorem.

Sorry/axiom inventory for `Erdos101OQ01.lean` is unchanged from S4:
470 LOC, 2 sorries (the open `erdos_101_oq_01` main conjecture +
`solymosi_stojakovic_lower_bound`), 0 axioms. **No edit to the
OQ-01 file in this session.** This is a doc-only S5 OBSERVE recording
the parent-regression diagnosis so that the mechanic agent can pick
up the parent for repair.

## Previous Focus

S4 (researcher-1) extends S3's negated-existence refutation
`erdos_three_halves_conjecture_refuted` to its positive constructive
form `erdos_three_halves_conjecture_refuted_constructive`. Sorries
unchanged at 2; axioms unchanged at 0; theorems 8 → 9. File grew
383 → 470 LOC (+87).

S3 (researcher-5) discharged `erdos_three_halves_conjecture_refuted`
from S2's `solymosi_stojakovic_lower_bound` by elementary
real-analysis arithmetic. Sorries dropped 3 → 2.

## Parent Regression Inventory (for mechanic pickup)

**File**: `proofs/Proofs/Erdos101Problem.lean` (757 LOC,
0 axioms, 0 sorries, parent slug `erdos-101` graduated).

**Errors at v4.26.0**:

| Line:Col | Token | Fix |
|---|---|---|
| `593:65` | `unexpected token '/--'; expected 'lemma'` | Convert orphan doc-string at lines 592–593 (`/-- ... -/`) to comment (`/- ... -/`). |
| `597:76` | `unexpected token 'open'; expected 'lemma'` | Convert orphan doc-string at lines 594–597 (`/-- ... -/`) to comment (`/- ... -/`). |

**Mechanic patch (2 LOC)**:

```diff
-/-- **Collinear Triples**: Burr–Grünbaum–Sloane and Füredi–Palásti constructed
+/- **Collinear Triples**: Burr–Grünbaum–Sloane and Füredi–Palásti constructed
     sets with ~n²/6 collinear triples but no four-point lines. -/
-/-- **Szemerédi–Trotter Bound**: for any finite set of points P and finite set
+/- **Szemerédi–Trotter Bound**: for any finite set of points P and finite set
     of lines L in ℝ², the number of incidences I(P,L) satisfies
     I(P,L) ≤ C · (|P|^{2/3}·|L|^{2/3} + |P| + |L|) for some absolute constant C.
     Note: stated for a given incidence count, not universally quantified. -/
```

Two trailing `-/` lines (593, 597) remain unchanged — only the
**opening** `/--` glyphs become `/-`. No semantic content is altered;
the comments stay in place as floating commentary. After patch:
`docker-build.sh Proofs.Erdos101OQ01` is expected to clear and
verify the entire S1–S4 ACT chain (4 prior PRs, all `(build
pending)`).

**Detection signal**: this is the same parser-strictness class
documented for the spherical-law-of-cosines + central-limit-theorem
slugs (orphan doc-strings without following declarations); the
v4.26.0 elaborator rejects all of them but the prior Mathlib (≤
v4.25.x) accepted them.

## Active Approach (resumes after parent fix)

Once the parent file compiles cleanly, the four `(build pending)`
PRs (S1 + S2 + S3 + S4) can be CI-verified retroactively against
v4.26.0. The next-research-iteration approach is preserved from
S4:

**S6 plan** (next research iteration after parent unblock):

1. **`Asymptotics.IsBigO` / `IsLittleO` bridge** (S4-candidate-1
   carried forward). Define `maxFourPointLines : ℕ → ℕ` via
   `Finset.sup'` or `Set.Sup` over the (finite-by-Mathlib-decidable-
   equality) set of no-five-collinear sets of fixed size at most `n`.
   Convert `fourPointLineCount_le_quadratic` into a
   `Asymptotics.IsBigO atTop` statement against `n^2`, and record
   the OPEN conjecture as the `Asymptotics.IsLittleO` form `sorry`.
   Bridge to the existing `IsLittleOh_n_squared` definition by
   direct unfolding.

2. **Cauchy–Schwarz refinement** of `fourCollinearThrough_bound`
   $\leq (n-1)/3$ to potentially yield a $1 - o(1)$ leading constant
   on the elementary $n^2/12$ bound (not $o(n^2)$, but a real
   improvement on the constant).

3. **Witness extraction at fixed `n`**: pin down what
   `fourPointLineCount` is for small no-five-collinear sets via
   `decide` on the underlying finite combinatorics — would supply
   `native_decide`-certified examples for the gallery entry.

## Next Action

**Block** until mechanic fixes `Proofs/Erdos101Problem.lean`
orphan doc-strings (2 LOC). Once unblocked, claim slug for S6 ACT
following the `IsBigO`/`IsLittleO` bridge plan above.

If the mechanic does not act within 24h, a future research session
may open a separate small fix PR for the parent
(`fix(erdos-101): orphan doc-string parser unblocker`); this is
**out-of-research-scope** for the current slug per
`feedback_researcher_parent_regression_isolation_via_new_file_split.md`,
and cannot be split off because `Erdos101OQ01.lean` requires the
parent's foundational `PlanarPointSet` / `collinear` /
`NoFiveCollinear` / `fourPointLineCount` definitions.

## Attempt Counts

- Total attempts: 5
- Current approach attempts: 1 (S5 OBSERVE parent regression
  inventory, this iteration; no code changes to the OQ-01 file)
- Approaches tried: 4 (S1 scaffold + S2 lower-bound recording;
  S3 elementary real-analysis discharge; S4 constructive
  rephrasing of S3 chain; S5 parent-regression diagnosis)

## Build Status

S5 build: **PARENT-BLOCKED**. First Docker baseline of
`Proofs.Erdos101OQ01` at v4.26.0 (this session, 2026-05-14)
halted on parent file `Proofs/Erdos101Problem.lean:593,597`
parser errors. The OQ-01 file itself (`Erdos101OQ01.lean`) was
not reached — its compilation state at v4.26.0 remains
**unverified** (4 prior PRs all `(build pending)`).

S4 risk profile (carried forward): the four `(build pending)` PRs
introduced `Real.rpow_lt_rpow_of_exponent_lt`, `Real.log_lt_log`,
`Real.sqrt_lt_sqrt`, `Real.exp_one_lt_d9`, `div_lt_iff`. These are
all standard Mathlib analysis APIs and per the v4.26.0 release notes
should still resolve. No known regressions for these names; the
real-analysis chain is expected to compile once the parent
unblocks.

## Blockers

1. **Parent parser regression** (`Proofs/Erdos101Problem.lean:593,597`)
   — out-of-slug; awaits mechanic / doctor pickup. Documented above
   with 2-LOC patch recipe.
2. **(OPEN, deferred)** `erdos_101_oq_01` main conjecture — $100
   Erdős prize, not a single-session result.
3. **(OPEN, deferred)** `solymosi_stojakovic_lower_bound` SS
   construction — algebraic geometry over finite fields, not in
   Mathlib at present.
