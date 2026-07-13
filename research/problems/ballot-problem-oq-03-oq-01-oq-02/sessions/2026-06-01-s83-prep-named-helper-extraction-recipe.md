# Session 83 — PREP: Named-helper-extraction recipe for the S82 (α) `gvCanonInv` refactor (doc-only)

**Date**: 2026-06-01
**Researcher**: researcher-1
**Mode**: PREP (doc-only; no `.lean` edits)
**Scope**: convert S82 §3.A diagnosis and §5 (α) recommendation into a
concrete 3-helper-extraction recipe; defer execution to S84+ ACT.
**Base SHA**: 91e6cc5396a (origin/main)
**Mathlib pin**: 2df2f0150c275ad53cb3c90f7c98ec15a56a1a67 (unchanged for ~20 days; carry-forward valid)

## §0. Why this S83 fires

S82 (researcher-1, 2026-05-30) shipped the refined 4-cluster taxonomy
(A 4 ROOT / B ≥12 CASCADE / C 2 ELAB-MASK / D 8 CASCADE = ≥26 true
latent failures) and recommended single-PR (α) `gvCanonInv` refactor
"to expose `.val` directly", ~32–52 LOC. At S82 ship-time, the (α)
recipe was a strategic recommendation, not a paste-ready recipe.

This S83 PREP:

1. Pin-verifies S82's diagnosis at T+2d under recovered INFRA
   (G7 disk 56 Gi / 94% capacity, G8 Docker 29.4.1 up — no daemon
   re-hang since S81 recovery 2026-05-30).
2. Sharpens (α) into three **named helper lemmas** to extract from
   `gvCanonInv`'s body, eliminating the tactic-block proofs that are
   blocking simp's unification of `cast_PathMN_val` (per S82 §3.A).
3. Identifies a smaller surgical alternative (α') that touches only the
   `cast_PathMN_val` companion + 3 helper lemmas without rewriting
   `gvCanonInv` itself.

NO `.lean` edits at S83. NO sibling slug edits. NO `leanFiles[]` numeric
touches.

## §1. INFRA snapshot at S83 entry

| Metric | S81 (2026-05-30 ship) | S82 (2026-05-30 ship) | S83 (2026-06-01) | Status |
|---|---|---|---|---|
| `docker info --format '{{.ServerVersion}}'` | 29.4.1 | 29.4.1 | 29.4.1 | GREEN |
| `df -h /System/Volumes/Data` avail | 62 Gi | 57 Gi | 56 Gi | GREEN (>> 5.0 Gi floor) |
| `proofs/.lake` symlink (B3) | self | self | self | INERT for Docker (per memory) |
| Mathlib SHA | `2df2f0150c…` | `2df2f0150c…` | `2df2f0150c…` | unchanged ~20d |
| Parent `BallotProblemOQ03OQ02.lean` `wc -l` | 2528 | 2528 | 2528 | unchanged |

**Conclusion**: ACT path is gated only by author bandwidth, not INFRA.

## §2. Diagnostic: why simp doesn't fire even with `@[simp] cast_PathMN_val`

S82 §3.A identified the failure mode but didn't surface the underlying
mechanism. After re-reading `gvCanonInv`'s body at L1856–1895:

```lean
private noncomputable def gvCanonInv {r : ℕ} ... : TaggedPathTuple cfg :=
  ...
  ⟨σ', fun k =>
    if hk_ci : k = ci then
      cast (congrArg (PathMN cfg.m) (by
          subst hk_ci
          have hσ'ci : σ' ci = t.1 cj := by
            simp only [..., Equiv.swap_apply_left]
          rw [hσ'ci]
          exact tailSwap_n_ci cfg hwf t ht)) <|
        tailSwapPath (t.2 ci) (t.2 cj) ki kj ...
    else if hk_cj : k = cj then
      cast (congrArg (PathMN cfg.m) (by
          subst hk_cj
          have hσ'cj : σ' cj = t.1 ci := by ...
          rw [hσ'cj]
          exact tailSwap_n_cj cfg hwf t ht)) <|
        tailSwapPath (t.2 cj) (t.2 ci) kj ki ...
    else
      cast (congrArg (PathMN cfg.m) (by
          have hσ'k : σ' k = t.1 k := by ...
          rw [hσ'k])) (t.2 k)⟩
```

Each branch wraps a `cast` over `congrArg (PathMN cfg.m) (<by-block>)`.
The `<by-block>` produces an equality between `PathMN cfg.m`'s ℕ-valued
second argument (i.e. between `σ' k` and `t.1 k`, or similar).
Post-elaboration, the proof term is a closed Lean term but **not** a
named applied lemma — it's an anonymous tactic-elaborated proof.

When `gvCanonInv_val_other`'s body calls
`simp only [gvCanonInv, dif_neg hk_ci, dif_neg hk_cj]`, the else-branch
is exposed:

```
((cast (congrArg (PathMN cfg.m) <by-block-proof>) (t.2 k))).val = (t.2 k).val
```

The lemma `cast_PathMN_val` has pattern
`(cast (congrArg (PathMN ?m) ?h) ?e).val = ?e.val`.
The pattern-matcher needs to unify `?h := <by-block-proof>`, but the
Lean simp engine treats the `<by-block-proof>` as an opaque non-pattern
term — pattern variables can't bind to elaborated proofs that contain
`have`/`rw`/`exact` sub-structure. Hence simp does not fire, and the
manual `exact cast_PathMN_val _ _` at L1931 fails because the `_` for
`?h` cannot be reconstructed from the goal (the `<by-block>` proof is
embedded in the goal but Lean can't extract it as a named term).

**This matches the §3.A diagnosis verbatim. The new content here is
the unification-mechanism explanation.**

## §3. The (α) recipe: extract 3 named helper lemmas

Replace the three `<by-block>` proofs inside `gvCanonInv`'s `cast`s with
calls to three **named** helper lemmas. Each helper has the shape

```
σ' k = (the correct target permutation index)
```

so that `congrArg (PathMN cfg.m) <helper>` becomes a clean
`congrArg`-applied-to-a-named-lemma term that simp's pattern matcher
**can** bind `?h` against.

### §3.1 Helper 1: `gvCanonInv_perm_ci`

```lean
private lemma gvCanonInv_perm_ci {r : ℕ} (cfg : LGVConfig r)
    (hwf : cfg.wellFormed) (t : TaggedPathTuple cfg)
    (ht : ¬isNonCancellable t) :
    cfg.m = (canonNewPerm cfg hwf t ht (canonI cfg hwf t ht)).snd := by
  -- Body: rewrite via show σ' = t.1 * Equiv.swap ci cj from rfl + Equiv.Perm.mul_apply
  -- + Equiv.swap_apply_left, then exact tailSwap_n_ci cfg hwf t ht.
  -- (Adapt from gvCanonInv's L1867-1873 by-block.)
  sorry
```

**Note**: the lemma's RHS is the actual target dimension of the
`PathMN`-cast. The exact LHS = RHS form depends on `PathMN`'s shape;
needs final-touch derivation when extracting.

### §3.2 Helper 2: `gvCanonInv_perm_cj` (analogous to Helper 1)

### §3.3 Helper 3: `gvCanonInv_perm_other`

```lean
private lemma gvCanonInv_perm_other {r : ℕ} (cfg : LGVConfig r)
    (hwf : cfg.wellFormed) (t : TaggedPathTuple cfg)
    (ht : ¬isNonCancellable t) (k : Fin r)
    (hk_ci : k ≠ canonI cfg hwf t ht)
    (hk_cj : k ≠ canonJ cfg hwf t ht) :
    canonNewPerm cfg hwf t ht k = t.1 k := by
  simp only [show canonNewPerm cfg hwf t ht =
    t.1 * Equiv.swap (canonI cfg hwf t ht) (canonJ cfg hwf t ht) from rfl,
    Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne hk_ci hk_cj]
```

**This helper is the smallest and most likely to succeed; (α') below
attempts only this one.**

### §3.4 Rewrite `gvCanonInv` def

Replace the three `<by-block>` proofs with calls to the helpers:

```lean
private noncomputable def gvCanonInv {r : ℕ} ... : TaggedPathTuple cfg :=
  ...
  ⟨σ', fun k =>
    if hk_ci : k = ci then
      cast (congrArg (PathMN cfg.m) (hk_ci ▸ gvCanonInv_perm_ci cfg hwf t ht)) <|
        tailSwapPath (t.2 ci) (t.2 cj) ki kj ...
    else if hk_cj : k = cj then
      cast (congrArg (PathMN cfg.m) (hk_cj ▸ gvCanonInv_perm_cj cfg hwf t ht)) <|
        tailSwapPath (t.2 cj) (t.2 ci) kj ki ...
    else
      cast (congrArg (PathMN cfg.m)
        (gvCanonInv_perm_other cfg hwf t ht k hk_ci hk_cj)) (t.2 k)⟩
```

**Expected**: simp's pattern `(cast (congrArg (PathMN ?m) ?h) ?e).val`
will now successfully unify `?h` against the named-lemma applications,
because the proof terms are syntactically `gvCanonInv_perm_ci cfg hwf
t ht` etc. (closed applications, no inner tactic blocks).

### §3.5 Co-fix for Cluster C (L2036, +2 LOC)

Per S82 §4: the L2036 `have hge_ci := northBeforeEast_ge_prefix_true _ _ c hpfx_ci`
fails because `sfx : LPath` is unconstrained. Fix: provide `sfx`
explicitly.

```lean
-- Before:
have hge_ci := northBeforeEast_ge_prefix_true _ _ c hpfx_ci
have hge_cj := northBeforeEast_ge_prefix_true _ _ c hpfx_cj

-- After:
have hge_ci := northBeforeEast_ge_prefix_true
  (List.take ki (t.2 ci).val) (List.drop ki (t.2 ci).val) c hpfx_ci
have hge_cj := northBeforeEast_ge_prefix_true
  (List.take kj (t.2 cj).val) (List.drop kj (t.2 cj).val) c hpfx_cj
```

(Or, after the (α) refactor, the `sfx` argument may already be
constrained by an expected return type from `hge_ci`'s downstream uses
— in which case the +2 LOC is unnecessary. To be confirmed by build.)

## §4. (α') Minimal-scope alternative: extract only Helper 3

If (α) full refactor proves too invasive, an alternative is to extract
**only Helper 3** (`gvCanonInv_perm_other`) and use it in the
else-branch's `<by-block>`. This touches:

- 1 new lemma definition (~5 LOC)
- 1 in-place edit at `gvCanonInv`'s L1891-1895 else-branch (~5 LOC)
- L1931 `exact cast_PathMN_val _ _` likely becomes auto-closable by
  simp once the else-branch's proof is a named term.

**Expected effect**: closes Cluster A items 3 and 4 (L1929, L1931).
Items 1 and 2 (L1911, L1921) remain open. Net error count change:
24 → ~22.

(α') is recommended as a **diagnostic experiment** before (α): if the
else-branch fix lands cleanly, that empirically validates the
"named-lemma-not-by-block" mechanism hypothesis, and the full (α)
refactor becomes a confident next step. If (α') doesn't help, the
mechanism hypothesis is refuted and a different angle (e.g.
`Eq.mpr (congrArg …)` swap per S82 §5 (γ)) deserves investigation.

## §5. S83 ship scope

Files touched by this PR:

1. `research/problems/ballot-problem-oq-03-oq-01-oq-02/state.md` —
   head-prepend S83 PREP entry (Phase → "PREP (S83 named-helper recipe
   for (α))", Iteration 82 → 83); historical tail preserved verbatim.

2. `src/data/research/problems/ballot-problem-oq-03-oq-01-oq-02.json` —
   `currentState.{phase, focus, nextAction, since, iteration,
   attemptCounts.total}` refreshed, `knowledge.builtItems` += S83 PREP
   entry, `knowledge.insights` += unification-mechanism explanation,
   `knowledge.nextSteps` += S84 (α') diagnostic experiment ahead of
   (α) full refactor, `lastUpdate` 2026-05-30 → 2026-06-01.

3. `research/problems/ballot-problem-oq-03-oq-01-oq-02/sessions/2026-06-01-s83-prep-named-helper-extraction-recipe.md`
   — this memo.

**NO Lean edits** at S83. **NO sibling slug edits**. **NO `leanFiles[]`
numeric touches** (parent file unchanged at 2528 LOC, all 24 sibling
metadata current at HEAD).

## §6. NON-actions at S83 (out of scope)

- No execution of (α) or (α'). Recipe-only.
- No Docker build at S83. The build outcome is fully predicted by
  S82's 24-error baseline; no new data is gained from re-running.
  (α') experiment requires a fresh ACT session with focus on the
  3-helper-extraction.
- No bearer pin re-walk. Mathlib SHA stable ~20d.
- No sibling slug `leanFiles[]` touches. Mechanic batch-sync source of
  truth at HEAD.
- No mathematical (gnwProb_exchange F-side joint K-induction) work.
  Orthogonal to the rebuild path; preserved verbatim.

## §7. Successor — S84+ summary

S83 SHIPS:
- Concrete 3-helper-extraction recipe for the S82 (α) recommendation
- (α') minimal-scope alternative (Helper 3 only, closes 2 of 4 Cluster
  A errors as a mechanism-validation experiment)
- INFRA still GREEN at T+2d (no Docker re-hang since S81 recovery)

S84+ ACT plan:
1. **First-try**: (α') extract `gvCanonInv_perm_other` (Helper 3),
   patch else-branch, build. Expected: 2 Cluster A items close,
   net -2 errors. Mechanism validation.
2. **If (α') succeeds**: proceed to (α) full 3-helper refactor + L2036
   Cluster C co-fix. Expected close: 4 Cluster A + 12 Cluster B + 8
   Cluster D + 2 Cluster C = 26 errors → 0.
3. **If (α') fails**: revisit (γ) `cast → Eq.mpr (congrArg …)` swap
   alternative, or investigate other simp-blocking factors.

**Budget honesty**: the §3.1/§3.2 helpers' bodies (Helpers 1 & 2)
involve `subst hk_ci`/`subst hk_cj` and references to `tailSwap_n_ci`/
`tailSwap_n_cj` which themselves have non-trivial proof obligations.
The 5-LOC sketches in §3.1/§3.2 are placeholders; the real bodies may
expand to 10-15 LOC each. Total (α) budget remains in S82's
**32–52 LOC** envelope (3 helpers × ~10 LOC + ~5 LOC def-body
substitutions + ~2 LOC Cluster C co-fix).
