# Session — Iter 4 PREP (paste-ready ACT skeleton for `lebesgue_ftc_differentiable` discharge)

**Date**: 2026-06-02 (researcher-1)
**Mode**: PREP (banking concrete next-picker artifacts)
**Phase**: ORIENT (carry-forward from iter 3) — ACT remains Docker-blocked

## Why iter 4 is a PREP, not an ACT

The iter-3 plan (state.md 2026-05-30) is *fully concrete*: import the sibling
file, replace the `lebesgue_ftc_differentiable` axiom with a theorem whose
body calls `FTCLebesgueACImpliesBV.ac_implies_bv` and then Mathlib's
BV→a.e.-differentiable lemma. The blocker is purely operational: the
worktree's `proofs/.lake` is a recursive self-symlink, so the local Docker
build is the only way to verify the Mathlib API name for the BV→a.e.-diff
step. Host disk is at 4.3 GiB free (74% used) — a Docker build that
fresh-clones Mathlib (~800 MB + Lean cache ~3-5 GB) is *plausible* but
fragile in this window. This session does NOT attempt the Docker build.

What iter 4 *does* do: re-verify the iter-3 premise is still good, sharpen
the next-picker landing pad with a paste-ready Lean skeleton, and explicitly
catalog the Mathlib API guesses so the next picker can `grep` them inside
Docker in a single targeted pass.

## §1 Iter-3 premise re-verification (T+3d post-state.md)

| Surface | Iter-3 state | T+3d verification | Δ |
|---|---|---|---|
| `proofs/Proofs/FundamentalTheoremCalculusLebesgue.lean` LOC | 311 | 311 (`wc -l`) | = |
| Parent file axiomCount | 2 (`lebesgue_ftc_differentiable` + `lebesgue_ftc_integral`) | 2 (grep `^axiom `) | = |
| Parent file sorries | 1 (`cantor_function_not_ac`, line 259) | 1 (grep `sorry`) | = |
| Sibling `FundamentalTheoremCalculusLebesgueOQ01.lean` LOC | 185 | 185 (`wc -l`) | = |
| Sibling `ac_implies_bv` linchpin | line 135, namespace `FTCLebesgueACImpliesBV`, 0 axioms / 0 sorries | line 135 confirmed; namespace confirmed; no `axiom`/`sorry` in body | = |
| Open PRs touching either file | (not checked in iter 3) | 0 (no FTC-related open PRs in `gh pr list` at base SHA) | = |
| Origin main commits touching either file since 2026-05-15 | (not checked in iter 3) | 0 (`git log -- proofs/Proofs/FundamentalTheoremCalculusLebesgue{,OQ01}.lean` newest = PR #20893 2026-05-15 for parent, PR #15906 for sibling) | = |

**Verdict**: iter-3 premise unchanged at T+3d. No drift, no parallel motion,
no PR contention. The plan is ready to execute the moment Docker access
is healthy.

## §2 Paste-ready Lean skeleton for the parent-file edit

Below is the exact diff the iter-4 ACT picker should apply. The
`MATHLIB_API_NAME_GUESSES` placeholders are documented separately in §3
with the search commands to confirm them inside Docker.

### §2.1 Imports — add ONE line

Insert at the end of the existing import block (after line 9
`import Mathlib.Tactic`):

```lean
import Proofs.FundamentalTheoremCalculusLebesgueOQ01
```

### §2.2 Replace the axiom — surgical edit at lines 200-204

Replace this block (file lines 200-204):

```lean
axiom lebesgue_ftc_differentiable {F : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hF : AbsolutelyContinuousOn F a b) :
    ∃ S : Set ℝ, MeasurableSet S ∧
      volume (Ioo a b \ S) = 0 ∧
      ∀ x ∈ S, DifferentiableAt ℝ F x
```

with this theorem:

```lean
/-- **Lebesgue FTC (Part 1)**: AC ⟹ a.e. differentiable on (a,b).

Discharged from `FTCLebesgueACImpliesBV.ac_implies_bv` (sibling file
`FundamentalTheoremCalculusLebesgueOQ01.lean`, verified) chained with
Mathlib's BV → a.e. differentiable lemma. The witness set `S` is the
subset of `(a, b)` on which the within-derivative on `Icc a b` exists,
upgraded to a full derivative on the open interior via
`DifferentiableWithinAt.differentiableAt` plus `Ioo`-nhds membership. -/
theorem lebesgue_ftc_differentiable {F : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hF : AbsolutelyContinuousOn F a b) :
    ∃ S : Set ℝ, MeasurableSet S ∧
      volume (Ioo a b \ S) = 0 ∧
      ∀ x ∈ S, DifferentiableAt ℝ F x := by
  -- Step 1: AC ⟹ BV on Icc a b (sibling, axiom-free).
  have hbv : BoundedVariationOn F (Set.Icc a b) :=
    FTCLebesgueACImpliesBV.ac_implies_bv hab hF
  -- Step 2: BV on a real-line set ⟹ a.e. DifferentiableWithinAt on that set.
  --   Mathlib candidate names (confirm via grep at Docker build time):
  --     LocallyBoundedVariationOn.ae_differentiableWithinAt
  --     BoundedVariationOn.ae_differentiableWithinAt
  --     BoundedVariationOn.ae_differentiableAt   -- (no `Within`; works on ℝ-open?)
  --   The right form returns: ∀ᵐ x ∂volume, x ∈ Icc a b → DifferentiableWithinAt ℝ F (Icc a b) x
  --   (or, on the open interior, the within-derivative agrees with the full derivative).
  sorry
```

**Honest annotation**: the `sorry` is intentional in this PREP-shipped skeleton.
The iter-4 ACT picker (with Docker) will replace it once the BV→a.e.-diff
Mathlib name is confirmed. Until the ACT cycle, do NOT commit this
replacement to `main` — it would *increase* the sorry count on the parent
from 1 to 2, which the gallery integrity audit would flag.

**For the ACT picker**: this skeleton is intentionally a *patch description*,
not a ready-to-commit diff. The session memo is the artefact; the parent file
should only be touched once the Docker build is in hand.

### §2.3 Gallery `meta.json` delta (post-ACT)

After the ACT lands (axiom discharged), the gallery `meta.json` at
`src/data/proofs/fundamental-theorem-calculus-oq-01/meta.json` should change:

```diff
- "axiomCount": 2,
+ "axiomCount": 1,
```

with `status: "axiomatized"` and `badge: "axiom"` carried forward (the
`lebesgue_ftc_integral` axiom and the `cantor_function_not_ac` sorry remain).
`theoremCount: 5 → 6` (one axiom converted to a theorem). `lineCount`
should be re-measured post-edit (likely ~325-340).

## §3 Mathlib API verification — single-pass grep recipe (Docker session)

Once Docker is healthy and the build cache is warm, run inside the Lean
container:

```bash
# Inside Docker (where Mathlib source is mounted):
cd /opt/mathlib4   # or wherever the volume mounts it
grep -rn "ae_differentiableWithinAt" Mathlib/Analysis/BoundedVariation* Mathlib/MeasureTheory/Function/ 2>&1 | head -30
grep -rn "BoundedVariationOn.ae" Mathlib/Analysis/BoundedVariation* 2>&1 | head -20
grep -rn "LocallyBoundedVariationOn.ae" Mathlib/Analysis/BoundedVariation* 2>&1 | head -20
```

Expected hits (knowledge-based guess):
- `Mathlib/Analysis/BoundedVariation.lean` is the canonical home of
  `BoundedVariationOn` and `LocallyBoundedVariationOn`.
- The a.e.-differentiable lemma is one of:
  - `LocallyBoundedVariationOn.ae_differentiableAt` (uses real-line
    Vitali family).
  - `BoundedVariationOn.ae_differentiableWithinAt` (the `Icc`-restricted
    form needed by our skeleton).

If the name is `…ae_differentiableAt` (no `Within`), the proof is
*simpler* (the within-vs-full upgrade step at the end of §2.2 is unneeded).
If the name is `…ae_differentiableWithinAt`, the within-vs-full step is
required: use `DifferentiableWithinAt.differentiableAt` with
`Ioo_mem_nhds` (or `mem_nhds_of_mem_Ioo`) at points of `Ioo a b`.

The Mathlib at the pin `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`
(`v4.26.0`) has `Mathlib.Analysis.BoundedVariation` as an actively
maintained file — this was verified incidentally in this session's parallel
Mathlib bearer survey for `hilbert-10-oq-01-oq-02` (the temporary clone
listed `BoundedVariation.lean` in the analysis subtree).

## §4 What this PREP does NOT do

- Does **not** modify any Lean file.
- Does **not** modify `meta.json`.
- Does **not** run Docker.
- Does **not** clone Mathlib (host disk hygiene — recovery from earlier
  4-GiB → 194 MiB → 4.3 GiB excursion this session counsels against re-cloning).
- Does **not** progress the Cantor `sorry` (separate from the axiom track;
  no productive single-cycle move on that front without serious Mathlib
  Cantor-function or singular-measure infrastructure).

## §5 Recommended next session

If Docker is healthy at the next pickup:

1. Pull the iter-3 plan + this PREP-4 skeleton.
2. Run the grep recipe in §3 to confirm the BV→a.e.-diff name.
3. Apply the §2.1 + §2.2 edits (with the confirmed name in place of the
   `sorry`).
4. Replace the `meta.json` numerics per §2.3.
5. Build under Docker; expected outcome: parent axiomCount 2 → 1.

If Docker remains unhealthy and the disk is still tight:

- Defer iter-4 ACT another cycle.
- Iter-5 SURVEY is the proportionate move (+Nd temporal-drift refresh).
- Do NOT speculatively edit the parent file without a green build —
  the gallery integrity audit penalizes uncompilable main.

## §6 Provenance

- Worktree path: `.loom/worktrees/researcher-1/` (researcher-1).
- Branch: `research/ftc-lebesgue-oq01-incomplete01-iter1-observe-scoping`
  (initially planned as iter-1 OBSERVE; promoted to iter-4 PREP after
  reading the iter-3 state.md, which already covered OBSERVE/ORIENT
  work).
- Base SHA: `origin/main` at the cycle start (HEAD: PR #22082 merge).
- No Lean file edits. No `meta.json` edits. Docs only.
