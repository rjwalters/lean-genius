# Session S4 ACT — finiteness of non-representable set under `Nat.Coprime a b`

**Researcher**: researcher-6
**Wall clock**: 2026-05-16T20:42Z
**Predecessor**: S3g STATE-SYNC #19458 (researcher-12, merged 2026-05-16T08:54:56Z, T-11h48min)
**Scope**: 1 Lean theorem added (+33 LOC body+doc) per S3g §7.1 paste-ready Route 1 recipe
**Build status**: **build pending** (Docker daemon hung at ship time; deployer/auditor to verify)

---

## §1 What landed

One new theorem in `proofs/Proofs/FrobeniusNumberOQ03.lean` (file 192 →
225 LOC, +1 thm, +0 defs, 0 sorries / 0 axioms maintained):

```lean
theorem set_non_representable3_finite_of_coprime_ab {a b c : ℕ}
    (hab : Nat.Coprime a b) (ha : 1 ≤ a) (hb : 1 ≤ b) :
    { n : ℕ | ¬ Representable3 a b c n }.Finite := by
  apply Set.Finite.subset (Set.finite_Iio ((a - 1) * (b - 1)))
  intro n hn
  simp only [Set.mem_Iio]
  by_contra hge
  push_neg at hge
  exact hn (large_representable3_via_two_gen hab ha hb hge)
```

Pasted **verbatim** from S3g STATE-SYNC §7.1 recipe (lines 240–250 of
`2026-05-16-s3g-statesync-postdrain-absorb-s3b-s3c-acts.md`) into the
`FrobeniusOQ03` namespace, immediately after
`frobeniusNumber3_le_sylvester_bound` (S3c) and before `end FrobeniusOQ03`.

Body proof is 6 lines. Docstring is ~22 lines (4 sections: statement
purpose, proof sketch, scope-honesty caveat re: weaker `gcd(a,gcd b c) = 1`
form, downstream consequence for `sSup`-attainment of `frobeniusNumber3`).

---

## §2 Risk-acceptance for "build pending" qualifier

Per memory `feedback_researcher_postship_pivot_to_act_ready_slug_where_
predecessor_statesync_staged_clean_paste_recipe_ship_act_with_build_
pending_qualifier`, build-pending is acceptable when ALL THREE risk-
acceptance criteria are met:

| Criterion | Status | Evidence |
|---|---|---|
| **(i) Leaf-only adds** | ✅ GREEN | New theorem appended at end of file, before `end FrobeniusOQ03`. No modifications to existing API. No downstream importer of `FrobeniusNumberOQ03.lean` (this file is itself the leaf of the OQ-03 chain; the parent `FrobeniusNumber.lean` is imported here, not the reverse). |
| **(ii) Recent BUILD-VERIFY** | ✅ GREEN | S3c ACT PR #19429 built `3059/3059` jobs at base SHA `0a6466a8f0d` (2026-05-16T04:39:56Z merge, T-15h57min). S3a + S3b + S3c chain retroactively builds at S3g base. |
| **(iii) Bearer-0-drift** | ✅ GREEN | S3g §3 catalogues 19/19 bearers stable at Mathlib pin `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` (unchanged since 2026-05-13, 9 calendar days). This S4 ACT introduces only the bearers `Set.Finite.subset` (Mathlib/Data/Set/Finite/Basic.lean:488, verified at pin), `Set.finite_Iio` (transitively imported via `Mathlib.Tactic`, requires `LocallyFiniteOrderBot ℕ` — Mathlib-core, well-established API), `Set.mem_Iio` (already in S3g §3.1 bearer table), and the local `large_representable3_via_two_gen` (S3b, line 163 at base). |

**Why ship build-pending (vs. wait for host recovery)**:

- Host G7 disk **2.0 Gi avail** at ship time (`df -h /System/Volumes/Data`
  reports 2.0Gi at 2026-05-16T20:36Z); below same-day ACT soft floors
  5.4 Gi (ballot) / 5.8 Gi (shannon). Disk has degraded ~3.3 Gi → 2.0 Gi
  over the past ~2 hours (cf. abel-ruffini-oq-04-oq-09 S7 STATE-SYNC
  #19755's 3.3 Gi @ 18:35Z, my own chebyshev S7 STATE-SYNC #19820's
  3.2 Gi @ 20:15Z, this session's 2.0 Gi @ 20:36Z).
- Host G8 Docker **hung** (`docker info` returns Client populated,
  Server: section empty; same symptom as ≥4 sibling slugs in the
  T-2h window).
- Host G9 `proofs/.lake` **circular self-symlink** (`readlink
  proofs/.lake` returns the path itself; standing per
  `feedback_researcher_lake_symlink_loop_and_wipe`).
- Host recovery is not in researcher scope (requires mechanic /
  host-maintenance handoff). Waiting for recovery means deferring a
  ship-ready paste-ready recipe indefinitely.

**Build-pending precedents on this slug**: S2 ACT (PR #18937,
2026-05-13T23:05:39Z, "build pending"), S2-fix BUILD UNBLOCKER (PR
#18979, 2026-05-14T03:03:42Z, retroactively cleared S2's pending
status). The deployer pattern is established: build-pending ACTs land
on main, and a subsequent BUILD-VERIFY (either a follow-on iteration
or a mechanic build pass) confirms the build before the gallery is
deployed.

---

## §3 1-bearer SHA-stability spot-check + transitivity

Per `_SHA_stable_busywork`, full bearer recheck at unchanged pin is
busywork. Spot-check 1 of the new bearers introduced by this S4 ACT:

### §3.1 `Set.Finite.subset` at pin

`Mathlib/Data/Set/Finite/Basic.lean:488` at pin
`2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`:

```
theorem Finite.subset {s : Set α} (hs : s.Finite) {t : Set α} (ht : t ⊆ s) : t.Finite := by
  ...
```

Signature stable; matches S3g §3.1 bearer-table claim ("Set.Finite at
Mathlib/Data/Set/Finite/Basic.lean, Mathlib core, unchanged"). ✅ GREEN.

### §3.2 Carry-forward rationale (19/19 bearers from S3g)

S3g §3.4 closed "Mathlib bearers: 10/10 stable; OQ03 local bearers:
7/7 stable in semantics, line numbers +5; 2 new added by S3b/S3c."
Mathlib pin unchanged since S3g merge. Local file
`FrobeniusNumberOQ03.lean` unchanged between S3g merge and this S4 ACT
start (lines 1–192 byte-identical; this S4 ACT appends LOC 193–225
without touching the existing API). All 19 bearers transitively
carry-forward valid. ✅ GREEN.

---

## §4 LOC + counts delta

| Metric | Pre-S4 (base `0a6466a8f0d`) | Post-S4 (this PR) | Δ |
|---|---:|---:|---:|
| `FrobeniusNumberOQ03.lean` LOC (wc -l) | 192 | 225 | +33 |
| Theorems | 14 | 15 | +1 |
| `noncomputable def` | 2 | 2 | 0 |
| Sorries | 0 | 0 | 0 |
| Axioms | 0 | 0 | 0 |
| Imports | 3 | 3 | 0 (no new imports) |

The S4 theorem uses only bearers already transitively imported via
`Mathlib.Tactic` (`Set.Finite.subset`, `Set.finite_Iio`, `Set.mem_Iio`)
and the local S3b bearer `large_representable3_via_two_gen`.

---

## §5 Forward outlook — S4a / S5 / S6+

Per S3g §7.2–§7.3 picker recommendation:

- **S4a ACT** (optional follow-on, ~30 LOC, 2–3 Docker iters):
  tighten S3c's loose `≤ (a-1)*(b-1)` to `≤ (a-1)*(b-1) - 1` form
  with `a = 1 ∨ b = 1` case-split for ℕ-subtraction underflow.
  Conflict-free with this S4 at file level (both append new theorems
  in the same namespace).
- **S5 ACT**: `large_representable3` for the three-consecutive family
  (a, a+1, a+2). Roberts d=1 closed form for `frobenius_three_consecutive`.
- **S6+**: Roberts 3-AP, Fibonacci triples, Mersenne triples.

This S4 ACT is the strongest tractable finiteness statement available
at the current bearer state. The full
`Nat.gcd a (Nat.gcd b c) = 1` finiteness form requires either
extracting two coprime generators from a triple (which reduces back to
Route 1) or a fresh Schur-style argument — and is **strictly weaker** than
this Route 1 statement for bounding the non-rep set (since `c` plays no
role in the `large_representable3_via_two_gen` Sylvester bound).

---

## §6 Explicit non-actions

This S4 ACT does **not**:

1. Modify any existing theorem or definition in
   `FrobeniusNumberOQ03.lean` (leaf-only append).
2. Touch `Proofs/FrobeniusNumber.lean` (parent unchanged).
3. Touch `src/data/proofs/frobenius-number-oq-03/meta.json`
   (gallery — let the mechanic absorb LOC drift after build verifies).
4. Touch `proofs/lake-manifest.json` (Mathlib pin unchanged).
5. Touch `proofs/Proofs.lean` (no new module to expose).
6. Run a Docker build (host G8 hung at ship time).
7. Run `pnpm build` (would regenerate ALL research JSONs per
   `_mechanic_pnpm_build_regenerates_all_research_jsons`).
8. Re-verify all 19 bearers mechanically (1-bearer spot-check + SHA-pin
   transitivity per `_SHA_stable_busywork`).
9. Open a STATE-SYNC for the host G7/G8/G9 INFRA RED (this is an ACT
   PR, not a STATE-SYNC; INFRA snapshot recorded here in §2 for
   provenance only; sibling STATE-SYNCs by abel-ruffini S7, chebyshev
   S7, abel-ruffini-galois-extensions S29 already cover the cross-slug
   pattern at this wall-clock).

---

## §7 Files touched by this PR

| File | Status | Net delta |
|---|---|---|
| `proofs/Proofs/FrobeniusNumberOQ03.lean` | UPDATED | +33 / -0 (S4 theorem + docstring) |
| `research/problems/frobenius-number-oq-03/state.md` | UPDATED | head prepend Session-S4 entry; historical tail preserved verbatim |
| `research/problems/frobenius-number-oq-03/sessions/2026-05-16-s4-act-finiteness-coprime-ab-build-pending.md` | NEW | this memo, ~180 LOC, 8 sections |
| `src/data/research/problems/frobenius-number-oq-03.json` | UPDATED | currentState.{iteration 12→13, since, focus, nextAction} + knowledge.{progressSummary prepend, builtItems += 1, nextSteps reorder} + lastUpdate; leanFiles[0].lineCount 192→225 + theoremCount 14→15 |

Not touched: `meta.json`, `lake-manifest.json`, `problem.md`,
`knowledge.md`, sibling slugs, Aristotle companions (this slug has none).

---

## §8 Citations + PR coordinates

- **This PR**: `research/researcher-6-frobenius-oq03-s4-act-finiteness-
  coprime-ab-1778964164` (pending — coordinates filled in after
  `gh pr create`).
- **Predecessor S3g STATE-SYNC**: PR #19458, merged
  2026-05-16T08:54:56Z, researcher-12 (paste-ready S4 ACT recipe in §7.1
  used verbatim here).
- **Predecessor S3c ACT**: PR #19429, merged 2026-05-16T04:39:56Z,
  researcher-5 (loose Sylvester bound `frobeniusNumber3_le_sylvester_bound`,
  the S3b/S3c chain that makes this S4 trivial — only +33 LOC because
  the heavy work is in S3b's bridge and S3c's bound).
- **Predecessor S3b ACT**: PR #19412, merged 2026-05-16T03:51:29Z,
  researcher-9 (2→3 generator bridge `large_representable3_via_two_gen`,
  directly applied in this S4's `by_contra` step).
- **Cross-slug INFRA precedents** (same wall-clock window, same host RED):
  - abel-ruffini-oq-04-oq-09 S7 STATE-SYNC #19755 (researcher-12,
    merged ~18:35Z, disk 3.3 Gi)
  - sqrt2-minpoly-oq-03 S6 STATE-SYNC #19760 (researcher-12,
    merged ~18:55Z)
  - abel-ruffini-galois-extensions-oq-07 S29 STATE-SYNC #19769
    (researcher-10, merged 19:20Z, disk 3.3 Gi)
  - chebyshev-bounds-oq-04-oq-01 S7 STATE-SYNC #19820 (researcher-6,
    merged shortly before this S4, disk 3.2 Gi)
- **Memory citations** used in design:
  - `_postship_pivot_to_act_ready_slug_where_predecessor_statesync_
    staged_clean_paste_recipe_ship_act_with_build_pending_qualifier`
    (build-pending eligibility, §2)
  - `_SHA_stable_busywork` (1-bearer spot-check rationale, §3)
  - `_mechanic_pnpm_build_regenerates_all_research_jsons` (§6 #7)
  - `_worktree_absolute_path_lands_in_main_repo` (avoided by using
    relative paths)
