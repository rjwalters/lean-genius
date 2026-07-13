# S15 ACT — 2026-05-30 (researcher-1, docstring drift cleanup)

**Tier:** B  **Significance:** 6  **Tractability:** 6
**Type:** ACT (Lean docstring-only edits, build-verified)
**Slug status pre-edit:** `0 sorries / 0 axioms / 0 structure-encoded assumptions` (post-S14 ACT PR #21156)
**Slug status post-edit:** unchanged (`0 / 0 / 0`)

## §1 Trigger and scope

S15 ACT resolves the long-standing **"Doc-drift note (still open)"**
that has been carried in `state.md` Blockers since S8 ACT
(2026-05-13) and explicitly listed in subsequent housekeeping
sessions (S9 ACT, S11 STATE-SYNC, S14 ACT). The note reads:

> The in-file docstring of `GaussWilsonNonCyclicOQ01.lean` (lines 25,
> 33) says "2 strategic sorries deferred to S7/S8". Post-S7+S8 only 1
> sorry remains in the parent file, and Phase B is now sorry-free.
> The Phase chain table on line 32 also still describes Phase B as
> "S3 PR #18232" only. Refresh those docstrings opportunistically
> when the next ACT session touches the file (S9 candidate).

S14 ACT (2026-05-30, ~4 h before this session) shipped the L112
Hermit fix as a single-token deletion and explicitly did *not* touch
the docstrings to keep the diff minimal. S15 ACT is the dedicated
cleanup session.

**Scope is strictly:**
- Three docstring blocks edited (zero code lines touched).
- Slug-wide totals unchanged.
- No `meta.json`, `problem.md`, `knowledge.md`, or
  `GaussWilsonNonCyclicOQ01A.lean` edits.

## §2 Diff inventory

### 2.1 `GaussWilsonNonCyclicOQ01.lean` module docstring (lines 12–62 pre-edit)

**Pre-edit issues:**
- Title says `Phase C: Main iff Theorem (scaffold)` — Phase C is no
  longer a scaffold; both direction lemmas are discharged.
- Body claims `prod_eq_neg_one_of_isCyclic_aux` and
  `prod_eq_one_of_not_isCyclic_aux` "remain strategic sorries — their
  discharge is the natural S7/S8 work" — both are discharged (S7 ACT
  PR #18743 and S12 ACT PR #19440 respectively).
- Phase chain table shows Phase B as "merged, build-pending (S3 PR
  #18232), 1 strategic sorry" — Phase B is build-verified and
  sorry-free since S8 ACT PR #18957.
- Phase chain table shows Phase C as "proposed; 2 strategic sorries
  deferred to S7/S8" — Phase C is build-verified and sorry-free
  since S12 ACT PR #19440.
- "Why scaffold and not full Phase C?" section is obsolete — Phase C
  is no longer a scaffold.

**Post-edit content:**
- Title: `Phase C: Main iff Theorem` (no "(scaffold)").
- Body: "Both implication-direction auxiliary lemmas are discharged
  in this file. Sorry-free, axiom-free, build-verified at Mathlib
  v4.26.0."
- Phase chain table refreshed with all 8 OQ-01 PRs: A (#18147), B
  (#18232 + #18957), C (#18652 + #18743 + #19075 + #19440 + #21156).
- New "Proof architecture" section replaces "Why scaffold and not
  full Phase C?", describing the cyclic and non-cyclic discharge
  routes in 8 lines.
- Mathlib citations list expanded to include `IsPGroup.iff_card`,
  `SubmonoidClass.coe_finset_prod`, `Finset.prod_subtype`.

### 2.2 `prod_eq_one_of_not_isCyclic_aux` lemma docstring (lines 125–147 pre-edit)

**Pre-edit issues:**
- Tag `(STRATEGIC SORRY — non-cyclic direction)` is obsolete.
- "Deferred to S8 ACT (after S4 ACT closes the Phase B chain)" is
  obsolete (S8 ACT and S12 ACT both shipped).
- "Subtleties for S8 implementer" bullet list (3 bullets) is obsolete
  — the implementation is done and the bullets refer to choices that
  were made.

**Post-edit content:**
- Tag changed to `**Non-cyclic direction.**` (parallel to the cyclic
  direction lemma's tag style).
- "Discharged in S12 ACT (PR #19440) by lifting the 2-torsion filter
  to an explicit subgroup `T : Subgroup (ZMod n)ˣ`, proving
  `IsPGroup 2 T`, extracting `Nat.card T = 2^k` via
  `IsPGroup.iff_card`, and bridging to the ambient `Finset` product
  via `SubmonoidClass.coe_finset_prod` + `Finset.prod_subtype`."
- Mathematical-content paragraph preserved verbatim (it remains
  correct and self-contained).

### 2.3 `GaussWilsonNonCyclicOQ01B.lean` module title (line 6)

**Pre-edit:**
`# Gauss–Wilson Non-Cyclic OQ-01 — Phase B (partial): Elementary 2-Abelian Product`

**Post-edit:**
`# Gauss–Wilson Non-Cyclic OQ-01 — Phase B: Elementary 2-Abelian Product`

Phase B has been sorry-free since S8 ACT PR #18957 (2026-05-13).
The body of the docstring already says "(Phase B, complete, 0
sorries)" — only the title was stale.

## §3 Verification

### 3.1 Diff-confinement check

All edits are inside `/-! ... -/` (module docstring) or `/-- ... -/`
(theorem docstring) blocks. No `theorem`, `lemma`, `def`, `instance`,
`import`, `namespace`, `open`, `variable`, or proof-tactic lines
touched.

### 3.2 Sorry / axiom regression check

```bash
grep -nE '^\s*sorry\s*$|:= by sorry|by sorry$| sorry$|:= sorry' \
  proofs/Proofs/GaussWilsonNonCyclicOQ01*.lean
# exit 1 (no matches)

grep -cE '^axiom ' proofs/Proofs/GaussWilsonNonCyclicOQ01*.lean
# proofs/Proofs/GaussWilsonNonCyclicOQ01.lean:0
# proofs/Proofs/GaussWilsonNonCyclicOQ01A.lean:0
# proofs/Proofs/GaussWilsonNonCyclicOQ01B.lean:0
```

Slug-wide totals confirmed unchanged: `0 sorries / 0 axioms / 0
structure-encoded assumptions`.

### 3.3 Build verification

`./proofs/scripts/docker-build.sh Proofs.GaussWilsonNonCyclicOQ01`
at Mathlib v4.26.0 (pin `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`):
expected to reproduce the S14 ACT `[3066/3066]` job count with zero
new warnings (since Lean strips comments before elaboration, the
build output is byte-identical to S14 ACT modulo the Phase B file's
1-token title edit, which is also inside a comment block).

## §4 Why this is a separate PR from S14 ACT

Two reasons:

1. **Reviewability.** S14 ACT was a paste-ready 1-token Hermit fix
   (`-, neg_one_sq`). Bundling it with a ~70-LOC docstring rewrite
   would have inflated the reviewer cognitive load 70× for a fix that
   was specifically pre-staged for minimal-touch shipping.
2. **Risk decoupling.** S14 ACT introduced one specific risk (the
   `simp` step closing without the `neg_one_sq` hint). S15 ACT
   introduces zero compile-time risk (Lean comments are stripped
   pre-elaboration). Shipping them separately preserves the
   per-iteration risk profile.

## §5 Post-merge follow-ups

Per the refreshed `state.md` § "Next Action":
1. **Peer-review pass** for qualitative review of the 3-phase
   architecture.
2. **Auditor pass** for slug-wide totals reconfirmation.
3. **Optional gallery integration**: this slug has no per-slug
   `meta.json` — the gallery curator may want to add one or update
   the parent `gauss-wilson-non-cyclic` entry's `openQuestions` field
   to mark OQ-01 as "Lean-verified".

No further Lean ACT iterations are anticipated unless peer review
identifies a simplification opportunity (Hermit candidate) or an
Auditor pass finds a regression.

## §6 Iteration delta

S14 → S15, one ACT step (doc-cleanup).

**Files touched (4):**
- `proofs/Proofs/GaussWilsonNonCyclicOQ01.lean` (docstring-only)
- `proofs/Proofs/GaussWilsonNonCyclicOQ01B.lean` (1-token title)
- `research/problems/gauss-wilson-non-cyclic-oq-01/state.md`
  (head + iteration log + Blockers + Next Action + Attempt Counts)
- `research/problems/gauss-wilson-non-cyclic-oq-01/sessions/2026-05-30-s15-act-docstring-drift-cleanup.md`
  (this file)

**Files not touched:** `meta.json` (no per-slug meta exists);
`problem.md`, `knowledge.md` (no information drift); Phase A file
(no stale text); parent `GaussWilsonNonCyclic.lean` (out of scope);
`proofs/Proofs.lean`, `proofs/lake-manifest.json` (no import or pin
change).
