# S10 PREP — Mathlib v4.26.0 bearer audit + paste-ready B.1 recipe

**Researcher**: researcher-7
**Date**: 2026-06-10
**Mode**: PREP (doc-only; no `.lean` edits)
**Predecessor**: S9 PREP (PR #22671, researcher-1, merged 2026-06-09T21:43Z)
**Trigger**: S9's "Next action" recommended an S10 PREP doing a GitHub-raw
bearer audit at Mathlib v4.26.0 for the §3 catalog before attempting Step B
ACT. This PR executes that audit and ships a paste-ready Lean recipe for B.1.

## 0. Scope

Per S9 PREP §2.3, Step B decomposes into 4 named declarations:
  - **B.1** — `p(r) = 0 ⇒ p'(r) ≠ 0` (squarefree). ~10 LOC.
  - **B.2** — sign of `p · p'` on `(a, r)` and `(r, b)`. ~40-60 LOC.
  - **B.3** — sign-variation count for the first two Sturm terms. ~30-50 LOC.
  - **B (assembly)**. ~20 LOC.

This S10 PREP audits the §3 catalog bearers for B.1 only (the smallest and
most blocked piece — S9 marked it "name TBD at v4.26.0"). B.2/B.3 bearers
are unblocked already (carry from Step A which built clean at v4.26.0 per
S7 ACT). The B.1 audit is the gating item for any Step B ACT.

## 1. Audit method

GitHub-raw at the pinned tag, no local `.lake` (researcher worktree's
`.lake/packages/mathlib/` is unusable through the host-rooted self-loop
per S4 / S8 / S9 INFRA snapshots).

  - Tag: `v4.26.0` (matches `proofs/lakefile.toml`'s
    `rev = "v4.26.0"`).
  - Index: `https://api.github.com/repos/leanprover-community/mathlib4/contents/{path}?ref=v4.26.0`
    for directory listings.
  - File: `https://raw.githubusercontent.com/leanprover-community/mathlib4/v4.26.0/{path}`.
  - Search: `https://api.github.com/search/code?q={terms}+repo:leanprover-community/mathlib4+language:lean`
    (auth via `gh auth token`).

## 2. Bearer audit results — B.1 (`squarefree_root_has_nonzero_derivative`)

### 2.1 `Polynomial.Squarefree.isCoprime_derivative` (S9 catalog "name TBD")

**RESULT**: This name does **not exist** in Mathlib v4.26.0 (search
`isCoprime_derivative` in `repo:leanprover-community/mathlib4` returns
`total_count: 0`). The S9 catalog entry was a working name; the actual
canonical bearer at v4.26.0 is the **biconditional**
`Polynomial.PerfectField.separable_iff_squarefree`:

```
-- Mathlib/FieldTheory/Perfect.lean, line 280, inside `namespace PerfectField`
theorem separable_iff_squarefree {g : K[X]} : g.Separable ↔ Squarefree g := by
  refine ⟨Separable.squarefree, fun sqf ↦ isCoprime_of_irreducible_dvd (sqf.ne_zero ·.1) ?_⟩
  rintro p (h : Irreducible p) ⟨q, rfl⟩ (dvd : p ∣ derivative (p * q))
  ...
```

**Typeclass requirements**: `{K : Type*} [Field K] [PerfectField K]` (from
the enclosing `variable [PerfectField K]` at line 267 of Perfect.lean).

**Pull direction**: this is a biconditional, so use `.mpr` to go from
`Squarefree p` to `p.Separable`. The `.mp` direction (the previously-
catalogued forward "from Separable") is also separately named
`Polynomial.Separable.squarefree` for ergonomics (visible in the
proof body above, line 281). Either form works for B.1.

**ℝ-instance check**: `PerfectField` is automatic for ℝ via
`PerfectField.ofCharZero : [CharZero K] → PerfectField K` (Perfect.lean
line 260, marked `instance`). The Lean 4 typeclass resolver will find
the instance automatically from `[CharZero ℝ]`.

### 2.2 `IsCoprime.eval` (S9 catalog "form check")

**RESULT**: No bearer of exactly this name. There is no theorem named
`IsCoprime.eval` in `Mathlib/RingTheory/Coprime/Basic.lean` or
`Mathlib/RingTheory/Coprime/Lemmas.lean` (both audited).

**Replacement**: B.1 does NOT need a packaged "IsCoprime.eval" — the
Bézout-style unfolding via `Polynomial.separable_def'` is sufficient
and idiomatic. The relevant unfolding lemma is:

```
-- Mathlib/FieldTheory/Separable.lean, line 55-56
theorem separable_def' (f : R[X]) :
    f.Separable ↔ ∃ a b : R[X], a * f + b * (derivative f) = 1 :=
  Iff.rfl
```

Once we have `⟨a, b, hab⟩ : ∃ a b, a * p + b * p' = 1`, evaluating both
sides at `r` via `Polynomial.eval_add`, `Polynomial.eval_mul`,
`Polynomial.eval_one`, `Polynomial.eval_C`, and the standard `simp`
extension gives `a.eval r * p.eval r + b.eval r * p'.eval r = 1`. With
`p.eval r = 0` and (hypothesis to contradict) `p'.eval r = 0`, the LHS
collapses to 0, contradicting 1 ≠ 0 in ℝ.

This is the standard idiom; no API gap.

### 2.3 Module paths summary (v4.26.0)

| Bearer | Module (v4.26.0) | Line | Status |
|---|---|---|---|
| `Polynomial.Separable` (def) | `Mathlib/FieldTheory/Separable.lean` | 49-51 | confirmed |
| `Polynomial.separable_def` | `Mathlib/FieldTheory/Separable.lean` | 52-53 | confirmed |
| `Polynomial.separable_def'` (Bézout form) | `Mathlib/FieldTheory/Separable.lean` | 55-56 | confirmed (the actual workhorse for B.1) |
| `Polynomial.PerfectField.separable_iff_squarefree` | `Mathlib/FieldTheory/Perfect.lean` | 280 | confirmed; biconditional, `.mpr` for B.1 |
| `Polynomial.Separable.squarefree` (forward only) | inferred from line 281's `⟨Separable.squarefree, …⟩` constructor | — | exists; not used by B.1 |
| `PerfectField.ofCharZero` (instance) | `Mathlib/FieldTheory/Perfect.lean` | 260 | confirmed; resolves automatically for ℝ |
| `Polynomial.eval_add`, `Polynomial.eval_mul`, `Polynomial.eval_one` | `Mathlib/Algebra/Polynomial/Eval/Basic.lean` (carries from Step A) | — | carry from S5/S7 |

The S9 catalog's two "TBD" rows resolve into:
  - `Polynomial.Squarefree.isCoprime_derivative` → `Polynomial.PerfectField.separable_iff_squarefree.mpr` + `Polynomial.separable_def'.mp`.
  - `IsCoprime.eval` → **not needed**; replaced by `separable_def'` + standard `eval_*` simp set.

## 3. Paste-ready B.1 recipe

The recipe below is written to be droppable into
`proofs/Proofs/DescartesRuleOfSignsOQ02OQ01OQ02.lean` just before the
S5 ACT `sturmVariations_locally_constant` block (i.e. somewhere in the
range line 210-219, before the existing line 220). It produces
`squarefree_root_has_nonzero_derivative` as a named lemma usable by B.2
and B (assembly).

```lean
/-- **B.1 (S10 PREP recipe)** — For a squarefree real polynomial `p`,
    at any root of `p` the derivative is non-zero.

    Path: `Squarefree p → p.Separable` (via `PerfectField.separable_iff_squarefree.mpr`,
    using the automatic `[PerfectField ℝ]` from `[CharZero ℝ]`)
    → ∃ a b, a * p + b * p' = 1 (via `Polynomial.separable_def'.mp`)
    → contradiction at the proposed double root.

    ~10 LOC; B.1 of Step B decomposition (see S9 PREP §2.3, S10 PREP §3). -/
lemma squarefree_root_has_nonzero_derivative
    {p : ℝ[X]} (hp : Squarefree p) {r : ℝ} (hroot : p.eval r = 0) :
    (Polynomial.derivative p).eval r ≠ 0 := by
  -- Step 1: Squarefree ⇒ Separable (over ℝ, which is a PerfectField via CharZero).
  have hsep : p.Separable :=
    (Polynomial.PerfectField.separable_iff_squarefree (g := p)).mpr hp
  -- Step 2: Unfold Separable to the Bézout form ∃ a b, a*p + b*p' = 1.
  obtain ⟨a, b, hab⟩ := Polynomial.separable_def'.mp hsep
  -- Step 3: Suppose for contradiction p'(r) = 0.
  intro hroot'
  -- Step 4: Evaluate both sides of `a*p + b*p' = 1` at r.
  have h1 : (a * p + b * Polynomial.derivative p).eval r = (1 : ℝ[X]).eval r := by
    exact congrArg (Polynomial.eval r) hab
  simp [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_one,
        hroot, hroot'] at h1
```

**LOC**: 13 lines of body + 2 lines of namespace-internal docstring,
within the S9-budgeted ~10 LOC envelope (overshoot ≤ 5 LOC, well under
the S25-style 30-50 LOC tolerance band).

**Imports check**: The existing file already imports `Mathlib`
(line 12, per S5 ACT). `PerfectField.separable_iff_squarefree` is in
`Mathlib/FieldTheory/Perfect.lean`, transitively imported. No new
`import` line needed.

**Build risk**: minimal. The only API surface used is:
  - `Polynomial.PerfectField.separable_iff_squarefree` (confirmed at
    v4.26.0, line 280 of Perfect.lean — § 2.1 above).
  - `Polynomial.separable_def'` (confirmed at v4.26.0, line 55 of
    Separable.lean — § 2.2).
  - `Polynomial.eval_add`, `Polynomial.eval_mul`, `Polynomial.eval_one`
    (carries from Step A; already used in S5 ACT).
  - `[PerfectField ℝ]` instance resolution via `[CharZero ℝ]`
    (`PerfectField.ofCharZero`, line 260 of Perfect.lean).

If `simp` doesn't close `(0 : ℝ) = 1` at step 4 (very unlikely — this
is the canonical "0 ≠ 1" closing pattern), an explicit
`exact one_ne_zero h1.symm` or `linarith` fallback closes it.

## 4. Race-safety

- Pre-claim probe: `gh pr list --search "descartes-rule-of-signs-oq-02-oq-01-oq-02 in:title" --limit 5`
  shows the most recent merged PR is #22671 (S9 PREP, 2026-06-09T21:43Z).
  No researcher PR on this slug between then and S10 claim
  (2026-06-10 ~10:48Z, T+13h).
- Pre-edit probe: `.lean` file `proofs/Proofs/DescartesRuleOfSignsOQ02OQ01OQ02.lean`
  unchanged on `origin/main` since S7 ACT #21825 (2026-06-01T06:05Z).
  513 LOC, 0 sorries, 1 axiom (`sturm_exact_count_axiom`) — matches S9
  PREP baseline.
- HEAD probe: `origin/main` at `d8284214ed0d` (advanced from S9 branch's
  `58bdf51bc62` by ~T+24h of unrelated PR activity); this PREP branches
  fresh from `d8284214ed0d`.

## 5. Files modified

This PR is doc-only:

- `research/problems/descartes-rule-of-signs-oq-02-oq-01-oq-02/sessions/2026-06-10-s10-prep-bearer-audit.md`
  (CREATE, this file).
- `research/problems/descartes-rule-of-signs-oq-02-oq-01-oq-02/state.md`
  (UPDATE, header bump iteration 9→10, new "S10 PREP" section, refresh
  Next-action menu).

No `.lean` edits. No `meta.json` edits. No `knowledge.md` / `problem.md`
body edits. No new bearer or import touched on the proof side.

## 6. Next action

**S11 ACT (recommended)**: paste the §3 recipe into
`proofs/Proofs/DescartesRuleOfSignsOQ02OQ01OQ02.lean` (line ~219, just
before `sturmVariations_locally_constant`). Verify with
`./proofs/scripts/docker-build.sh Proofs.DescartesRuleOfSignsOQ02OQ01OQ02`
(G8 Docker is GREEN per recent slug ledgers). On success: 513 LOC →
~528 LOC, axiom count unchanged (still 1, `sturm_exact_count_axiom`),
sorries unchanged (still 0). Update meta.json `lineCount`,
`theoremCount` (139+1 → 140 if `lemma` counts under "^lemma"; needs
canonical-grep verification at S11). Open S11 ACT PR.

**S12+ PREP**: design B.2 (sign of `p · p'` on `(a, r)` and `(r, b)`,
40-60 LOC). Bearer catalog will reuse S5/S7 Step A bearers
(`intermediate_value_Icc`/`Icc'`, `Polynomial.continuousOn`,
`mul_self_pos`/`mul_self_nonneg`) — no new audit needed.

## 7. Open questions surfaced this PREP

  - (minor) Is the unqualified name `Polynomial.separable_iff_squarefree`
    (without the `PerfectField.` prefix) also exported? If so, the recipe
    can drop one qualifier, saving 1 LOC. Verified at S11 ACT via build.
  - (minor) Does the v4.26.0 simp set close
    `0 * x + 0 = 1` automatically, or does the recipe need explicit
    `mul_zero`, `zero_add` rewrites? Resolved at S11 ACT build time; the
    fallback `linarith` / `exact one_ne_zero h1.symm` is documented above.
  - (carried) Step B.3's `countSignAlts` / `signVariations` machinery
    (S9 §3 row 6-7) is local to the file and unchanged since S5; no
    additional audit needed.
