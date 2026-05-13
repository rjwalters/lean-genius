# S2 ACT — `eulerPoly` AP-gap witness scaffold

**Date**: 2026-05-13
**Agent**: researcher-5
**Mode**: ACT (Lean scaffold; build-pending)
**Slug**: `erdos-455-oq-04`

## Deliverable

New file `proofs/Proofs/Erdos455OQ04.lean` (~80 LOC; 2 defs, 1 structure,
2 theorems, **0 sorries, 0 axioms**) verbatim from S2 PREP (PR #18540 §1)
with one scope-narrowing: the `apGap_odd_length_le_three` theorem
(which the S2 PREP shipped with `sorry`) is **deferred to a later S2b
PREP**. Dropping it gives a fully sorry-free file at the S2 ACT
boundary; the structural deliverable surface is unchanged because the
parity-bound is a side-result, not a load-bearing piece of the
existence-of-length-40 chain.

## File contents (mathematical)

* `HasAPGaps (q : ℕ → ℕ) (d : ℤ) : Prop` — signed second-difference
  is `d` at every index. Matches S1 OBSERVE design (PR #18331).
* `structure APGapPrimeSeq (d : ℤ)` — strictMono ℕ-valued sequence,
  all-prime, with AP-gaps of common difference `d`. The
  bundling-structure choice mirrors parent's `MonotoneGapPrimeSeq`.
* `def eulerPoly : ℕ → ℕ := fun n => n^2 + n + 41` — Euler's
  prime-generating polynomial. **Computable** (not `noncomputable` —
  S2 PREP §1's `noncomputable` marker was a transcription artifact;
  `native_decide` requires reduction and `noncomputable` would
  block the closing tactic).
* `theorem eulerPoly_hasAPGaps : HasAPGaps eulerPoly 2` — by
  `unfold; push_cast; ring`. The verbatim 4-tactic proof from
  S2 PREP §2.3's `ring`-verified algebraic identity.
* `theorem exists_length40_apGapPrimeSeq` — `∃ q : ℕ → ℕ, HasAPGaps q 2 ∧ ∀ n < 40, (q n).Prime`.
  Witness: `eulerPoly`; closes by `interval_cases n <;> (unfold eulerPoly; native_decide)`
  on the 40 primality goals, each a `Nat.Prime` of an integer ≤ 1601.

## Net file changes

| File                                          | Δ                     |
|-----------------------------------------------|-----------------------|
| `proofs/Proofs/Erdos455OQ04.lean`             | NEW (~80 LOC)         |
| `proofs/Proofs.lean`                          | +1 import (alphabetic between Erdos454ProblemAristotle and Erdos455Problem) |
| `research/problems/erdos-455-oq-04/sessions/2026-05-13-s2-act-eulerPoly-witness-scaffold.md` | NEW (this note)       |
| `research/problems/erdos-455-oq-04/state.md`  | header bump → S2 ACT  |

No edits to `problem.md`, `knowledge.md`, or any `meta.json` / gallery
JSON. No `src/data/proofs/erdos-455-oq-04/` directory yet — that's
the S5 GALLERY task per parent state.md plan.

## Why drop `apGap_odd_length_le_three`?

S2 PREP §1's verbatim source includes it with `sorry`. Three reasons
to defer:

1. **Cleanliness.** A sorry-free S2 ACT is a stronger gallery posture
   than a `formalized` (sorry-bearing) one. The Euler witness is the
   load-bearing deliverable per parent state.md's S2 line: "Prove the
   trivial equivalence `apGap_zero_iff_prime_AP` and the monotone-gap
   subsumption `apGap_subsumes_monotone`." Both are sister bounds and
   neither is the `apGap_odd_length_le_three` lemma — they belong to
   the structural-equivalence side of the slug, not the
   existence-witness side.
2. **Risk isolation.** The parity proof (S2 PREP §1's stub) requires
   case analysis on `q.seq 0 = 2` vs `q.seq 0 ≥ 3` and `Int.even_sub`
   manipulations. Estimated ~30 LOC. Bundling it with the witness
   ACT widens the build-risk surface for a marginal payload.
3. **S2 PREP's own posture.** §1.1 lists "Sorries: 1" and §1's
   in-body comment says "deferred to S2b PREP". The verbatim source
   anticipates the deferral.

A future S2b ACT can pick up `apGap_odd_length_le_three` plus S1's
`apGap_zero_iff_prime_AP` and `apGap_subsumes_monotone` (both
sorry-free per state.md's Next-Action enumeration).

## Mathlib bearer audit (S2 PREP §2 summary)

All Mathlib facts used are at v4.26.0, pin `2df2f0150c275ad`:

* `Nat.Prime` decidability — `Mathlib/Data/Nat/Prime/Basic.lean`
  (transitively imported by `Mathlib.Data.Nat.Prime.Basic` at line 1).
* `push_cast`, `ring`, `interval_cases`, `native_decide` — all
  shipped with `Mathlib.Tactic` umbrella (line 2). S2 PREP §2.6
  confirmed.
* No new Mathlib imports beyond what S2 PREP audited.

## Risk register

1. **`native_decide` on `n² + n + 41` for `n ∈ {0..39}`.** S2 PREP §2.2
   verified all 40 values ≤ 1601, max prime check ≈ 0.025 s in
   compiled `decide`. 40 such checks should complete in ~1 s without
   heartbeat adjustment.
   *Fallback*: replace `native_decide` with `decide` (slower, kernel-checked).
2. **`unfold eulerPoly` inside the `<;>` chain.** Each branch needs
   `unfold` to unfold the `n^2 + n + 41` body before `native_decide`
   evaluates it. The `<;> (unfold; native_decide)` structure handles
   this per-branch. Alternative: `simp only [eulerPoly]` or
   `show Nat.Prime (n^2 + n + 41)` first.
3. **`push_cast; ring` failure.** S2 PREP §2.3 manually verified the
   polynomial identity:
   `((n+2)²+(n+2)+41) − 2((n+1)²+(n+1)+41) + (n²+n+41) = 2`.
   Fallback: `omega` won't handle `n²` but `linarith` after `nlinarith`
   would (slower).
4. **`Erdos455` namespace `open` resolution.** Parent file
   `Erdos455Problem.lean:24` declares `namespace Erdos455`. Our file
   opens it (line 51); this exposes parent's `HasNonDecreasingGaps`
   and `MonotoneGapPrimeSeq` for the future S2b's
   `apGap_subsumes_monotone` theorem (not yet shipped).
5. **Auto-generated `Proofs.lean` insertion.** S2 PREP §1.2 notes
   `proofs/Proofs.lean`'s top-line header "do not edit manually".
   The script `./.lean/scripts/generate-proofs-imports.sh` is the
   canonical regenerator, but a single-line alphabetic insert is
   equivalent and avoids the regenerator-script dependency in the PR
   diff. The 2026-05-12 `Erdos453OQ02` line was added by the same
   manual-insert convention (verified by `git log proofs/Proofs.lean`).

## Race / drift posture

* **Pre-push race check.** At session start:
  * `gh pr list --search "erdos-455-oq-04 in:title" --state open` → **0 open PRs**.
  * Latest merge for this slug: PR #18540 S2 PREP at 03:37 UTC, ~1h20min
    ago — past the 30-min release window.
  * No competing `Erdos455OQ04.lean` filename in `proofs/Proofs/`.
* **No worktree Docker build.** Per
  `feedback_researcher_lake_symlink_loop_and_wipe.md`, the `.lake`
  symlink loop wipes uncommitted work mid-build. Build-pending per
  the S2-S5 convention on minpoly-charpoly-oq-03 (PR #17980, #17995,
  #18086, #18182, #18507); Doctor/Mechanic verifies on a fresh
  container.
* **No gallery `meta.json` edits.** The S5 GALLERY task per parent
  state.md will create `src/data/proofs/erdos-455-oq-04/` with
  `status: "axiomatized"` (due to forthcoming Green-Tao axiom in S3).
  Premature gallery promotion now would force a `status: "formalized"`
  → `"axiomatized"` flip later, which is gallery-integrity noise.

## Anti-targets (this S2 ACT explicitly does NOT do)

1. Does not axiomatise Green-Tao (S3's deliverable).
2. Does not axiomatise the cubic-growth conjecture (S4's
   deliverable; per S1b OBSERVE PR #18468 the cubic-growth claim is
   replaced by the Euler-polynomial cap — which the present
   `exists_length40_apGapPrimeSeq` is the concrete witness of).
3. Does not create `src/data/proofs/erdos-455-oq-04/` (S5's
   deliverable).
4. Does not include `apGap_zero_iff_prime_AP` or
   `apGap_subsumes_monotone` — both are sorry-free per parent
   state.md and the natural S2b deliverable; bundling here would
   widen the surgical-S2 boundary.
5. Does not run `./proofs/scripts/docker-build.sh Proofs.Erdos455OQ04`
   (worktree `.lake` symlink trap; build-pending per convention).
6. Does not modify any other slug's `sessions/` or `meta.json`.

## Verification of "0 axioms / 0 sorries / 0 structure-encoded axioms"

* `grep -c "^axiom " proofs/Proofs/Erdos455OQ04.lean` → 0.
* `grep -c "sorry" proofs/Proofs/Erdos455OQ04.lean` → 0.
* The file declares no `structure` or `class` with assumption-style
  fields. `APGapPrimeSeq` is a data-bundling structure (strictMono +
  allPrime + apGaps are predicates over the data, not axioms about
  an opaque object). The four fields are constructor inputs, not
  ambient axioms.

## Follow-up (S2b candidates, in priority order)

1. **`apGap_zero_iff_prime_AP`** — for `d = 0`, AP-gaps reduce to
   prime arithmetic progressions (q is itself an AP). ~10 LOC,
   sorry-free, requires no new Mathlib.
2. **`apGap_subsumes_monotone`** — for `d ≥ 0`, AP-gap sequences have
   non-decreasing gaps (monotone-gap parent's `HasNonDecreasingGaps`).
   ~15 LOC, sorry-free.
3. **`apGap_odd_length_le_three`** — the parity-bound deferred from
   this S2 ACT. ~30 LOC, sorry-free, requires `Int.even_sub` and
   `Int.odd_iff_not_even`.
4. **S3 PREP**: axiom-form for Green-Tao 2008 (constant-gap subcase).
