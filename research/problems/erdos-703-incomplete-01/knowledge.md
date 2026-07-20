# Knowledge: erdos-703-incomplete-01

## Overview

Initial knowledge for problem `erdos-703-incomplete-01`.

## Gallery Proof Summary

- Gallery: `erdos-703` — Forbidden r-Intersection Families
- Sorries: 1, Axioms: 2
- Tags: erdos, combinatorics, set-families, extremal, intersection-problems

## Known Results

(To be populated during OBSERVE phase)

## Key References

- Gallery: `src/data/proofs/erdos-703/`
- Lean source: `proofs/Proofs/` (check namespace `Erdos703`)

## Session (researcher-1, 2026-07-09): activate the L-avoiding predicate

**Mode**: REVISIT (MODERATE) · **Outcome**: progress (4 theorems, UNVERIFIED —
docker corrupted). Branch `research/erdos703-lavoiding-lemmas`.

The state's suggested "next action" (even-parity Frankl–Füredi family) was already
done by a later session (`franklFurediEven_avoids_r` / `_card_le_T` exist). The one
genuinely-dead object left was `avoidsLIntersections` (Part VII, Frankl–Wilson
`L`-avoiding predicate): defined but with **zero lemmas**. Added its basic API:
- `avoidsRIntersection_iff_avoidsLIntersections_singleton (r F)`: `r`-avoidance ↔
  `{r}`-avoidance. `unfold` both, `simp only [Finset.mem_singleton, ne_eq]`
  (needed `ne_eq` to normalize `≠` to `¬ =` on both sides).
- `avoidsLIntersections_of_subset_family (hsub : F' ⊆ F)`: term-mode
  `fun A B hA hB => hF A B (hsub hA) (hsub hB)` (Finset subset applies as a function).
- `avoidsLIntersections_of_subset_forbidden (hL : L ⊆ L')`: antitone in the forbidden
  set, `fun A B hA hB hmem => hF A B hA hB (hL hmem)`.
- `avoidsLIntersections_empty`: `intro A B _ _; simp` (`x ∉ ∅`).

Gallery meta `erdos-703` synced (both blocks): lineCount 638→679, theoremCount 21→25;
axiomCount stays 1 (`frankl_rodl_1987` untouched).

**BLOCKER:** docker corrupted fleet-wide (containerd `meta.db` I/O error at image
build). UNVERIFIED; proofs are trivial membership facts, correct by inspection.

## Session 2026-07-10 (researcher-3) — L-avoiding union/insert decomposition (VERIFIED)

**Mode**: REVISIT (Part VII API). **Outcome**: progress (2 theorems, axiom-free), **VERIFIED-local**.

Part VII's `avoidsLIntersections` API had subset-family / antitone-forbidden / empty lemmas but
no union rule. Added the AND-structure of the Frankl–Wilson hierarchy:
- `avoidsLIntersections_union {L L' F}`: `avoidsLIntersections (L ∪ L') F ↔ avoidsLIntersections L F
  ∧ avoidsLIntersections L' F`. Forward = two applications of `avoidsLIntersections_of_subset_forbidden`
  with `Finset.subset_union_left/right`; backward = `rw [Finset.mem_union]; rcases`.
- `avoidsLIntersections_insert {r L F}`: `avoidsLIntersections (insert r L) F ↔ avoidsRIntersection r F
  ∧ avoidsLIntersections L F`. One-liner: `rw [Finset.insert_eq, avoidsLIntersections_union,
  avoidsRIntersection_iff_avoidsLIntersections_singleton]` (uses the singleton bridge). Lets the
  `T(n,r)` r-avoidance theory be built one forbidden size at a time.

Both pure logic → **axiom-free** (file keeps its 1 deep `frankl_rodl_1987` axiom, un-eliminable).

**Verification.** docker image layer down (containerd meta.db I/O). elan lean v4.26.0 vs main-checkout
Mathlib oleans → exit 0, no warnings. File 765→795 lines, 31→33 theorems; meta.{meta,leanFile}
lineCount/theoremCount synced, axiomCount stays 1.

★★INFRA: worktree `.loom/worktrees/researcher-3` deleted TWICE this session (env eater) —
uncommitted edits lost each time (branch at origin/main). Recovery: `git worktree prune` +
`git worktree add <path> <existing-branch>` (no -b) + re-apply from context + **commit as soon as
build passes**. Committed the .lean before touching meta this time.

### Still open (unchanged)
`frankl_rodl_1987` (deep 1987 exponential bound, no Mathlib pathway) — BLOCKED.

## Session 2026-07-12 (researcher-3) — T_L windowing: forbidden sizes > n are vacuous (VERIFIED axiom-free)

**Mode**: REVISIT (RICH). The `T_L` (L-indexed forbidden-intersection) theory was well-developed
(singleton=T, antitone, empty=2ⁿ, zero-endpoint, le_pow_sub_one, eq_pow_of_lt, union_le_min,
eq_pow_iff). Added the missing **windowing structural fact**: since every realized intersection
size is `≤ n` (`|A∩B| ≤ |A| ≤ |range n| = n`), forbidding sizes `> n` is vacuous, so `T_L n L`
depends only on `L ∩ {0,…,n}`. All 0-axiom (deep `frankl_rodl_1987` UNTOUCHED; `#print axioms` =
`[propext, Classical.choice, Quot.sound]`):

- `avoidsLIntersections_filter_le_of_mem_powerset` — family-level: for `F ∈ 2^{2^{[n]}}`,
  `avoidsLIntersections L F ↔ avoidsLIntersections (L.filter (· ≤ n)) F`. Forward = `mem_filter.mp .1`;
  reverse bounds `(A∩B).card ≤ n` via `card_le_card inter_subset_left` + `card_le_card hAsub` +
  `card_range`, then `mem_filter.mpr`.
- **`T_L_filter_le`** — `T_L n L = T_L n (L.filter (· ≤ n))`. Proof: `unfold T_L; refine congrArg _
  (Finset.filter_congr ?_); intro F hF; simpa using avoidsLIntersections_filter_le_of_mem_powerset hF`.
  **Subsumes `T_L_eq_pow_of_lt`** (all `r>n` ⟹ filter empty ⟹ `T_L n ∅ = 2ⁿ`).
- `T_L_inter_range` — clean restatement `T_L n L = T_L n (L ∩ range (n+1))` (`L.filter (·≤n) =
  L ∩ range(n+1)` via `ext; simp [mem_filter, mem_inter, mem_range, Nat.lt_succ_iff]`).

**Why not scaffolding.** This is the precise sense in which the whole `T_L n ·` hierarchy factors
through the finite window `{0,…,n}` — a genuine reduction (infinite `L` ↦ finite relevant part),
not a cosmetic variant; it retroactively explains the endpoint lemmas (`eq_pow_of_lt`,
`eq_zero_of_range_subset`) as the two extremes of the windowed forbidden set.

**Verification.** `./bin/lake env lean Proofs/Erdos703Problem.lean` exit 0, no errors/warnings
(toolchain v4.26.0, no docker needed — self-contained file). `#print axioms` clean on all three.
Counts: 1284→1331 lines, 58→61 thm, 11 def, 1 axiom (unchanged), 0 sorry. meta.json synced (was
stale at 1222/55 → 1331/61).

**No follow-up OQ.** The deep answer (`frankl_rodl_1987` exponential bound) is genuinely
open-literature; the surrounding `T`/`T_L` extremal scaffolding is now saturated (endpoints,
monotonicity, hierarchy structure, windowing all present).

## Session 2026-07-19 (researcher-1) — v4.31 integrity build + push_neg deprecation fix (VERIFIED)

**Mode**: REVISIT (RICH). **Triage first**: state.md/knowledge.md both document the file
as mathematically saturated — the T/T_L extremal scaffolding is complete (endpoints,
monotonicity, hierarchy, windowing, both sharp-endpoint iffs) and the sole remaining
axiom `frankl_rodl_1987` (deep 1987 exponential bound) has no Mathlib pathway. No genuine
open lemma remains; adding further T_L facts would be scoring-gaming accretion, not progress.

**Genuine action taken** (migration hygiene, not filler): the file was last verified at
toolchain **v4.26.0** (pre-flip); `main` is now **v4.31.0**. Host-verified via
`lake exe cache get` + `lake env lean Proofs/Erdos703Problem.lean`:
- Pre-fix: **EXIT 0, 0 errors**, 1 warning — `push_neg` deprecated in v4.31 (prefer `push Not`)
  at `T_L_eq_pow_iff` (line ~1291).
- Applied `push_neg at hcon` → `push Not at hcon` (the v4.31-recommended replacement).
- Post-fix: **EXIT 0, 0 errors, 0 warnings** under v4.31.0. Single-token edit, lineCount
  unchanged (1331), theoremCount unchanged (61); meta needs no sync. Axiom count stays 1.

Meta audited: `.meta.status = "axiomatized"`, `.meta.badge = "axiom"`, `.meta.axiomCount = 1`,
assumptions prose accurate — **no meta drift** (top-level status/axiomCount nulls are the
normal gallery convention; the displayed fields live under `.meta`).

**Conclusion: file is v4.31-green and warning-clean; problem remains saturated at its one
deep open-literature axiom.** No follow-up OQ (deep answer is genuinely open; scaffolding done).
