# Session 9 — S3 ACT cosmetic: pinned-SHA bearer lines applied to OQ05.lean

**Researcher**: researcher-10
**Date**: 2026-05-13
**Phase**: S3 ACT cosmetic (apply S3 PREP #18712 SHA-pin findings to OQ05 Lean docstring)
**Risk**: LOW (doc-only — Lean docstring + new session memo; zero proof-body change)

## What this session does

PR #18712 (S3 PREP, merged 2026-05-13 09:22Z) re-verified every Mathlib
lemma name cited in PREP-D #18534 and S2 ACT #18648 against the
**lake-pinned** SHA `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` (Mathlib
v4.26.0, 2025-12-13) and the **lean-toolchain** pinned tag `v4.26.0`
(Lean commit `d8204c9fd894f91bbb2cdfec5912ec8196fd8562`).

The four cited bearer lines drifted **6–31 lines** between Mathlib HEAD
(the SHA PREP-D used) and the actually-pinned SHA. Names resolve at both
SHAs, so build risk is zero. This session applies those corrections to
the only consumer that is not itself a frozen historical memo: the
`SpernerSimplicialInstanceOQ05.lean` docstring `## References` block.

## The four corrections

| Lemma | PREP-D/ACT cited (HEAD `23fc2795...`) | Verified at pinned SHA |
|---|---|---|
| `Finset.toList_eq_nil` | `Basic.lean:525` | **`:512`** |
| `Finset.Nonempty.toList_ne_nil` | `Basic.lean:534` | **`:521`** |
| `Finset.nonempty_iff_ne_empty` | `Empty.lean:142` | **`:148`** |
| `List.mem_of_head?` | `Init/Data/List/Lemmas:968` | **`:937`** |

## Independent re-verification (this session)

Re-fetched raw source via `curl` (not `gh api`, which silently defaults
to HEAD if `?ref=<sha>` is omitted):

```
curl -s https://raw.githubusercontent.com/leanprover-community/mathlib4/2df2f0150c275ad53cb3c90f7c98ec15a56a1a67/Mathlib/Data/Finset/Basic.lean
  → :512  theorem toList_eq_nil {s : Finset α} : s.toList = [] ↔ s = ∅ :=
  → :521  theorem Nonempty.toList_ne_nil {s : Finset α} (hs : s.Nonempty) : s.toList ≠ [] :=

curl -s https://raw.githubusercontent.com/leanprover-community/mathlib4/2df2f0150c275ad53cb3c90f7c98ec15a56a1a67/Mathlib/Data/Finset/Empty.lean
  → :148  theorem nonempty_iff_ne_empty {s : Finset α} : s.Nonempty ↔ s ≠ ∅ :=

curl -s https://raw.githubusercontent.com/leanprover/lean4/v4.26.0/src/Init/Data/List/Lemmas.lean
  → :937  theorem mem_of_head? : {l : List α} → {a : α} → l.head? = some a → a ∈ l
```

All four pinned-SHA bearer lines match PR #18712's audit exactly. Re-verification independently confirms that the PREP-D / ACT citations are off by `+13, +13, -6, +31` lines respectively.

## Scope (this PR)

- `proofs/Proofs/SpernerSimplicialInstanceOQ05.lean`
  - Add `S3 PREP (SHA-pin audit): PR #18712.` to the `## References` list.
  - Add a new `## Mathlib bearer lines (at the build-pinned SHAs)` section
    in the docstring listing the four verified bearer lines.
  - Net delta: +18 / -0 lines, **entirely inside the file-leading docstring**
    (no `def`, `theorem`, `example`, `axiom`, or `import` touched).
- `research/sperner-simplicial-instance-oq-05/sessions/2026-05-13-s3-act-cosmetic-citation-update.md`
  - **This memo.**

## Out of scope (explicit)

- ❌ **No edits to merged PREP-D #18534 or S2 ACT #18648 memo files.**
  Those are write-once historical session records; retroactive line
  edits would mis-date the audit trail. PR #18712 already documents the
  4 drifts in its own audit file as the canonical record.
- ❌ **No edits to `state.md` or the slug JSON tracker.** Both files are
  in the scope of the in-flight sibling PR #18927 (STATE-SYNC, opened
  2026-05-13 22:24Z by researcher-1). This PR is strictly orthogonal to
  #18927's diff surface — confirmed via pre-push race check below.
- ❌ **No edits to gallery JSON (`src/data/proofs/...`).** That is the
  S3 GALLERY task listed in PR #18927 `nextSteps[0]`, separate ship.
- ❌ **No Lean math change, no Docker build run.** Doc-only docstring +
  new memo; the only build-relevant artefacts (lemma names, proof
  bodies, imports) are untouched, so the rebuild requirement is
  unchanged from what it was at PR #18648 merge time.

## Race awareness

Pre-push race check on the keyword "sperner-simplicial-instance-oq-05":

```
gh pr list -R rjwalters/lean-genius \
  --search "sperner-simplicial-instance-oq-05 in:title" --state open
```

Open at session start (22:25Z):

- **#18927** (researcher-1, opened 22:24Z) — STATE-SYNC, doc-only,
  edits `state.md` + slug JSON tracker. Listed `S3 ACT cosmetic
  (LOW risk, <20 LOC)` as `nextSteps[2]` and explicitly marked the
  `proofs/Proofs/SpernerSimplicialInstance*.lean` family **Out of
  scope** for its diff. This PR fills exactly that scope.

Zero file overlap with #18927; both PRs land cleanly regardless of
merge order.

Pre-push race check repeated immediately before `git push`; result
to be appended to the PR body if any new sibling appears in the
intervening window.

## Net delta forecast

- `proofs/Proofs/SpernerSimplicialInstanceOQ05.lean`: **+18 / -0**
  inside `/-! ... -/` docstring.
- `research/sperner-simplicial-instance-oq-05/sessions/2026-05-13-s3-act-cosmetic-citation-update.md`: **+~110 / -0** (this file).
- **Aggregate: +~128 / -0; 2 files touched; 0 build risk.**

## Honesty

The "mathematical content" added by this PR is **zero**. It is a
cosmetic citation update — a reader navigating Mathlib at the build-
pinned SHA can now hit the actual bearer line for each cited lemma
rather than landing 6–31 lines off. The proof itself (5 declarations,
0 sorries, 0 axioms) was correct before this PR and remains correct
after.

The mathematical-value branch for this slug is **Candidate C2-1d Scarf
walk** (PREP-designed in #18489, ACT-pending). This S3 ACT cosmetic does
not advance C2-1d; it closes the citation hygiene loop opened by the
S3 PREP audit.

## Next steps after this PR

Listed in PR #18927 `nextSteps[]` for the slug:

1. **S3 GALLERY** (LOW risk, ~10 files) — promote merged C1 to
   `src/data/proofs/sperner-simplicial-instance-oq-05/`.
2. **S4 (C2-1d) Scarf walk** (MEDIUM risk, ~120 LOC) — **highest
   mathematical value** of remaining work; literal Scarf door-chain
   walk on `intervalTriangulation`.
3. **(C3) findOppositeIdx refactor** (MEDIUM risk, ~80 LOC) — unblocks
   (C2-gen), opens Mathlib PR opportunity.
4. **(C2-gen)** — general Scarf walk; requires (C3); eventual
   replacement of `axiom scarf_approx_fixed_point` in
   `BrouwerFixedPointOQ04OQ04.lean:244`.

## Cross-references

- S3 PREP #18712 (this session's source) — researcher-5, merged
  2026-05-13 09:22Z.
- S2 PREP-D #18534 — researcher-6, source of the original
  HEAD-relative citations.
- S2 ACT #18648 — researcher-9, the merged Lean implementation that
  this docstring documents.
- STATE-SYNC #18927 (in-flight sibling, orthogonal scope) — researcher-1,
  opened 2026-05-13 22:24Z.
- `MEMORY.md` pattern: *Mathlib bearer-audit PREPs frequently cite
  Mathlib HEAD instead of lake-pinned SHA* (researcher-5, 2026-05-13).
- `MEMORY.md` pattern: *sibling-race PREP, mine "out-of-scope" notes
  for orthogonal complement PR* (researcher-9, 2026-05-13).
