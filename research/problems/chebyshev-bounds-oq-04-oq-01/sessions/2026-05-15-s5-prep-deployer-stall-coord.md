# S5 PREP — deployer-stall coordination + 3-way open-PR sequencing (doc-only)

**Date**: 2026-05-15T01:55Z
**Researcher**: researcher-9
**Phase**: PREP (no Lean / no JSON / no state.md edits)
**Scope**: single new file (this session doc); zero overlap with the 3 open PRs

## §0. Summary

`chebyshev-bounds-oq-04-oq-01` has 3 OPEN PRs and a system-wide deployer
stall. This PREP catalogues the 3-way file overlap, recommends a
post-stall merge sequence, and flags PR #17689 for close-as-superseded.

It is doc-only (single ADDED file, +250 LOC) and conflict-free with all
3 open PRs and with state.md / the slug JSON.

## §1. Deployer-stall context

- **Most recent merge in the repo**: PR #18980 (schroeder-bernstein-oq-01
  S6) at `2026-05-14T03:03:38Z`.
- **Now**: `2026-05-15T01:55Z`.
- **Zero-merge duration**: ~22.9 hours.
- **Stuck `CLEAN+MERGEABLE` PR count**: ≥ 100 (the `gh pr list --limit
  100` window is saturated at 99 CLEAN + 1 UNKNOWN — true count is
  larger).

This matches the system-wide stall pattern documented in
`feedback_researcher_deployer_stall_coordination_prep_pattern.md`
(researcher-8 2026-05-14 ~22:30–23:00 UTC, threshold ≥ 12h + ≥ 10
stuck mergeable). Several sibling coordination PREPs already exist
(see §8 for cross-references); this PREP completes the chebyshev slug.

## §2. Open-PR triage for this slug

`gh pr list -R rjwalters/lean-genius --search
"chebyshev-bounds-oq-04-oq-01 in:title" --state open` returns 3 PRs:

| PR | Title | Files | Status | Age (h) | Notes |
|---|---|---|---|---|---|
| #19092 | Iter 3 ACT — Selberg dual identity `Σ_{d∣n} Λ₂(d) = (log n)²` (build verified) | 4 (see §2.1) | CLEAN+MERGEABLE | 9.6 | researcher-9, 7744-job Docker clean |
| #19171 | S4 PREP — Iter 4 Möbius-inversion API pins + proof sketch (doc-only) | 1 (new sessions file) | CLEAN+MERGEABLE | 2.2 | researcher-8, 408 LOC, recommends Option A (wait for #19092) |
| #17689 | Iter 2 — prime values (build pending) | 1 (`ChebyshevBoundsOQ04OQ01.lean`) | DIRTY+CONFLICTING since 2026-05-12T22:13Z | 49.7 | Stale parallel attempt, content already merged via #17690 |

### §2.1 PR #19092 file delta (precise)

| Path | +/- | Role |
|---|---|---|
| `proofs/Proofs/ChebyshevBoundsOQ04.lean` | +1/-1 | parent regression fix (line 298: `by ring` → `by rw [pow_mul]; rfl` for `4^m = 2^(2*m)`) |
| `proofs/Proofs/ChebyshevBoundsOQ04OQ01.lean` | +91/-14 | slug Lean source (Iter 3 ACT: 3 new theorems + `Nat.divisors_prime` → `Nat.Prime.divisors` rename at line 191) |
| `research/problems/chebyshev-bounds-oq-04-oq-01/state.md` | +101/-40 | phase advance to `ACT (Iter 3 dual identity verified)` |
| `src/data/research/problems/chebyshev-bounds-oq-04-oq-01.json` | +28/-18 | knowledge + lastUpdated |

### §2.2 PR #19171 file delta

| Path | +/- | Role |
|---|---|---|
| `research/problems/chebyshev-bounds-oq-04-oq-01/sessions/2026-05-14-s4-prep-iter4-moebius-inversion.md` | +408/-0 | new sessions doc (Iter 4 Möbius-inversion API pins at SHA `2df2f015...`) |

### §2.3 PR #17689 file delta

| Path | +/- | Role |
|---|---|---|
| `proofs/Proofs/ChebyshevBoundsOQ04OQ01.lean` | +94/-15 | superseded-content (Iter 2 prime values, same content already merged via PR #17690 at 2026-05-12T00:48:30Z) |

## §3. Recommended post-stall merge sequence

Once the deployer resumes, the 3 PRs above should land in this order:

### Step 1 — Merge PR #19092 first

Reason: it is the substantive Lean ACT (Iter 3 dual identity), the only
PR among the three that touches `proofs/Proofs/**`, and the predecessor
that #19171 explicitly waits on (per #19171 §6 Option A).

Post-merge state:

- `ChebyshevBoundsOQ04OQ01.lean`: 312 LOC (was 230), 15 theorems (was
  12), 0 sorries, 0 axioms.
- `ChebyshevBoundsOQ04.lean`: parent regression cleared.
- `state.md`: phase `ACT (Iter 3 dual identity verified)`.
- JSON: `lastUpdate` ≈ 2026-05-14T16:22Z; knowledge bullets reflect
  Iter 3 ACT.

### Step 2 — Merge PR #19171 second

Reason: doc-only, ADDS-only (zero deletions), sole touchpoint is a new
file path. Conflict-free with #19092's diffs.

Verification (no `git merge` needed — disjoint paths):

```
PR #19092 paths ∩ PR #19171 paths = ∅
```

### Step 3 — Close PR #17689 with maintainer comment

Reason: stale 49.7 h parallel attempt, content merged via PR #17690 on
2026-05-12T00:48:30Z, has been in `CONFLICTING` state since
2026-05-12T22:13Z (~46 h). Keeping it open offers no value and clogs
the slug's open-PR window.

Recommended close-comment:

> Closing as superseded by merged PR #17690 (Iter 2 prime-value lemmas,
> merged 2026-05-12T00:48:30Z), which shipped the identical
> deliverables (`vonMangoldtConv_prime` + `selbergLambda2_prime`).
> `state.md` already documents this race in the Iter 2 section. The
> 2026-05-12T22:13Z `CONFLICTING` event was triggered by the merge.

This PR cannot resolve itself: its 94-LOC body is content-equivalent to
already-merged code, so a rebase would produce an empty diff. No
researcher should attempt rebase / fix-up — the right action is close.

### Step 4 — Iter 4 ACT can then proceed off main

Following #19171 §6 Option A: branch off the post-merge `main`, write
the literal Möbius–log identity `Λ₂(n) = Σ_{d|n} μ(d) · log²(n/d)` (≤
25 LOC body per #19171 §4 sketch), Docker-build, open Iter 4 ACT PR.

Estimated marginal Lean delta: +15–25 LOC, no new sorries, no new
axioms.

## §4. File-overlap matrix (conflict-free certification)

|   | #19092 | #19171 | #17689 | This PREP |
|---|---|---|---|---|
| `ChebyshevBoundsOQ04.lean` | ✓ +1/-1 | — | — | — |
| `ChebyshevBoundsOQ04OQ01.lean` | ✓ +91/-14 | — | ✓ +94/-15 (stale) | — |
| `state.md` | ✓ +101/-40 | — | — | — |
| slug JSON | ✓ +28/-18 | — | — | — |
| `sessions/2026-05-14-s4-prep-…md` | — | ✓ +408/-0 (new) | — | — |
| `sessions/2026-05-15-s5-prep-…md` (this) | — | — | — | ✓ +N/-0 (new) |

This PREP touches only its own new session doc — zero overlap with all
3 open PRs.

The single contested path (`ChebyshevBoundsOQ04OQ01.lean`, #19092 vs
#17689) is unresolvable in #17689's favour: #17689's content is already
merged via #17690, and #19092 builds on the merged state.

## §5. Expected post-merge state of slug

After Steps 1–3 land:

- 1 open PR (none) → 3 → 0 → 1 (Iter 4 ACT, when written).
- Lean LOC: 230 → 312.
- Theorem count: 12 → 15.
- Sorries: 0 (preserved).
- Axioms: 0 (preserved at slug; the parent `chebyshevPsi_asymptotic`
  axiom in `ChebyshevBounds.lean` remains the open target).
- Phase: `ACT (Iter 2 prime-value lemmas merged)` → `ACT (Iter 3 dual
  identity verified)`.
- Sessions docs added: 2 (`2026-05-14-s4-prep-…`, `2026-05-15-s5-prep-…`).

## §6. Cleanup recommendation for #17689 (detail)

`#17689 head: fcdfb6a2e0f733f793854186a6c65520dd78694f` (single
commit). The PR was created at 2026-05-12T00:12:38Z; PR #17690 (the
parallel successful attempt by the same researcher trail) was created
at 2026-05-12T00:12:39Z and merged at 2026-05-12T00:48:30Z. The race
note has been in `state.md` since the merge (line 39–40 of `state.md`
at `579a8437a0e`).

Confirmation that content is identical-in-effect:
- #17690 added 35 lines and removed 11 in `ChebyshevBoundsOQ04OQ01.lean`.
- #17689 adds 94 lines and removes 15 in the same file (denser-form
  variant of the same 2 lemmas with more explicit unfoldings).

The maintainer-comment-close is preferable to a researcher-comment
close (which would leave the PR open with no path to resolution). No
Lean / docs change is required to enable the close.

## §7. This PREP's conflict-free certification

This PREP adds exactly one file:

```
research/problems/chebyshev-bounds-oq-04-oq-01/sessions/2026-05-15-s5-prep-deployer-stall-coord.md
```

It does **not** touch:

- `proofs/Proofs/**` (would conflict with #19092)
- `research/problems/chebyshev-bounds-oq-04-oq-01/state.md` (would conflict with #19092)
- `src/data/research/problems/chebyshev-bounds-oq-04-oq-01.json` (would conflict with #19092)
- `src/data/proofs/chebyshev-bounds-oq-04-oq-01/**` (would conflict with hypothetical Iter 4 ACT gallery refresh)
- `research/problems/chebyshev-bounds-oq-04-oq-01/sessions/2026-05-14-s4-prep-…` (PR #19171's file; entirely disjoint)
- candidate pool

If the deployer resumes mid-PREP and lands #19092 + #19171 before this
lands, this PREP remains a clean fast-forward (its single new file
doesn't collide with anything either merge introduces).

## §8. Pattern + cross-references

This PREP follows
`feedback_researcher_deployer_stall_coordination_prep_pattern.md`
(MEMORY.md): doc-only sessions/ file, ~80–250 LOC, flags stuck PRs +
post-merge sequencing, no Lean / no JSON / no state.md edits.

Concurrent deployer-stall coordination PREPs from the same 22.9 h
stall (other slugs):

- PR #19205 (`circumference-via-differentiation-oq-03` S4, researcher-9, 2026-05-15T01:52Z)
- PR #19201 (`bounded-prime-gaps-oq-03-oq-02` S15, 2026-05-15T01:40Z)
- PR #19193 (`brouwer-fixed-point-oq-01-oq-02-oq-03-oq-02` S10, 2026-05-15T01:25Z)
- PR #19197 (`hilbert-10-oq-01-oq-02` S26, 2026-05-15T01:32Z)
- PR #19195 (`central-limit-theorem-oq-01-oq-01-oq-04-oq-01` S2, 2026-05-15T01:26Z)
- PR #19191 (`nth-root-irrational-oq-03` S5b, 2026-05-15T01:21Z)
- PR #19186 + #19188 (zsqrtd / hilbert-14, researcher-8, ~22:30–23:00Z 2026-05-14, the original write-up that anchors this wave)

Memory feedback (`feedback_researcher_preclaim_open_pr_check_avoids_s3_act_duplicate.md`):
ran the `gh pr list --search "<slug> in:title" --state open` check at
session start AND will re-run immediately before push (§9).

## §9. Pre-push re-check checklist

Per `feedback_researcher_preclaim_open_pr_check_avoids_s3_act_duplicate.md`,
re-run before `git push`:

```
gh pr list -R rjwalters/lean-genius --search "chebyshev-bounds-oq-04-oq-01 in:title" --state open
```

Expected: still the 3 PRs (#19092, #19171, #17689). If a 4th
coordination PREP from a peer researcher has appeared, kept this PR
open as supplement with cross-ref comment (since unique deliverables
here include the #17689 close-as-superseded recommendation).

## §10. Honest scope statement

This is NOT a substantive ACT or build-verify. It adds zero theorems,
zero sorry deltas, and zero proof content. Its value is operational:

- Reduces redundant PREP duplication during the deployer-stall window
  (peer researchers can read this and skip writing a 4th chebyshev
  coordination PREP).
- Provides a 1-paragraph close-comment template for #17689, removing
  ambient uncertainty about a 49.7 h stale PR.
- Pins post-stall merge ordering so the maintainer-merger has a
  ready-to-execute plan.

If the deployer resumes within minutes of this push, the value of this
PREP collapses to the #17689 cleanup recommendation alone — still
worth landing.

## §11. Cleanup TODOs (none required to land this PREP)

- [ ] Maintainer: when deployer resumes, merge #19092 → #19171 → close
      #17689 per §3.
- [ ] Future Iter 4 ACT author: follow #19171 §4 proof sketch off
      post-merge `main`.
- [ ] Future state.md refresher: after Iter 4 lands, add S5 PREP +
      Iter 4 ACT to the iteration log.
