# S43b — Strategic-gap audit of S43 PREP §3.4 + lemma-name corrections (doc-only)

**Author**: researcher-4 (2026-05-13 ~03:35 UTC)
**Type**: PREP audit-correction (markdown only; no Lean changes, no new axioms,
no new sorries)
**Builds on**: S43 PREP `2026-05-12-s43-fuel-generic-induction-strategy.md`
(merged) — fuel-generic induction strategy for S32b
**Audits**: S43 §3.4 "Strategy: outer-guard-fires propagates down all levels by
PART XXIV" + S43 §3.3.B "lehmerCofactors_id_apply_natAbs_max_le" name claim
**Anti-target**: solving S32b. This PREP only audits S43's strategic claim against
the actual PART XXIV statement and parent-file API surface; it does not propose
a replacement strategy beyond identifying the missing propagation lemma.

## §0. TL;DR

S43 PREP §3.4 proposes the strategy:

> Replace S32b's hypothesis `hfires` (level-(f+1) inner) with the
> **outer-guard-fires** predicate, which by PART XXIV propagates down all
> levels.

Direct read of PART XXIV (`BinaryGcdOQ03OQ02PathA.lean:1988–2016`,
`schonhageOuterGuardFires_above_imp_inner_fires`) shows it states the implication
**only at the operational fuel `a + b`** for the specific input `(a, b)`. It does
NOT propagate to inner sub-recursions on the reduced input pair `(u, v)`.

The propagation lemma the S43 strategy needs is:

```lean
-- HYPOTHETICAL (not in file): outer-fires-propagation
theorem outerFires_propagates_to_inner_reduced
    (a b : ℕ) (hab : ¬ max a b < hgcdThresholdSafe)
    (hfires : schonhageOuterGuardFires a b = true) :
    let s := hgcdShiftSafe a b
    let M_inner := hgcdMatrixSafe (a + b) (a / 2^s) (b / 2^s)
    let u := (M_inner.apply (↑a) (↑b)).1.natAbs
    let v := (M_inner.apply (↑a) (↑b)).2.natAbs
    schonhageOuterGuardFires u v = true
```

**This propagation lemma does NOT exist in the file** (grep returns 0 hits for any
`outer.*propagat`, `outerFires.*outer`, etc., across all 80 theorems of
`BinaryGcdOQ03OQ02PathA.lean`). Proving it is essentially as hard as the original
S32b deliverable, because it asks "does the algorithm's outer-guard hold for the
once-reduced input pair", which is the **non-expansion invariant** of Schönhage's
algorithm — exactly the open question the S43 strategy was meant to bypass.

**Audit conclusion.** The S43 strategy is **circular at §3.4**: the proposed
hypothesis-strengthening from level-(f+1) inner-guard to outer-guard-fires
does not actually unlock the induction unless an additional propagation lemma
is supplied, and that propagation lemma is essentially the open S32b
problem in a different guise.

S43's §1, §2, §3.1–§3.3, and §4's skeleton (with the `sorry` markers
named) remain useful as **mechanical structure** for the eventual S44 ACT.
The deficiency is specifically in §3.4's "by PART XXIV propagates" claim.

This PREP is doc-only. Pristine new file in `sessions/`. No Lean changes,
no edits to `state.md` / `knowledge.md` / `problem.md` / `meta.json`.

## §1. Direct verification of PART XXIV's statement

`proofs/Proofs/BinaryGcdOQ03OQ02PathA.lean:2000–2016` (S36, PR #17846,
merged):

```lean
theorem schonhageOuterGuardFires_above_imp_inner_fires {a b : ℕ}
    (hab : ¬ max a b < hgcdThresholdSafe)
    (hfires : schonhageOuterGuardFires a b = true) :
    max
      ((hgcdMatrixSafe (a + b)
          (a / 2 ^ hgcdShiftSafe a b)
          (b / 2 ^ hgcdShiftSafe a b)).apply (a : ℤ) (b : ℤ)).1.natAbs
      ((hgcdMatrixSafe (a + b)
          (a / 2 ^ hgcdShiftSafe a b)
          (b / 2 ^ hgcdShiftSafe a b)).apply (a : ℤ) (b : ℤ)).2.natAbs
      < max a b
```

**Three observations.**

1. **Fuel is `(a + b)`, NOT a general `f`.** The conclusion bounds the natAbs-max
   of the inner recursion **at the specific operational fuel `a + b`**. This is
   the level-(a+b+1) inner-guard firing condition for `hgcdMatrixSafeOf a b`,
   which equals `hgcdMatrixSafe ((a+b)+1) a b`. The statement does NOT say
   anything about the inner recursion at fuel `f < a + b`.

2. **Input is `(↑a, ↑b)`, the canonical positive cast.** The signed-input form
   that S43 §3.3.A's `hgcdMatrixSafe_apply_natAbs_sign_symm` lemma would handle
   is NOT exercised by PART XXIV directly.

3. **The contrapositive structure is preserved.** PART XXIV is the
   contrapositive of S30's `hgcdMatrixSafe_inner_abort_imp_outer_fails`
   (PART XX). Both are at the same operational fuel.

## §2. Direct verification of `schonhageOuterGuardFires`'s definition

`proofs/Proofs/BinaryGcdOQ03OQ02PathA.lean:788–793`:

```lean
def schonhageOuterGuardFires (a b : ℕ) : Bool :=
  if max a b < hgcdThresholdSafe then
    false
  else
    decide (max (hgcdSafeApply a b).1.natAbs (hgcdSafeApply a b).2.natAbs
              < max a b)
```

**The predicate is defined at operational fuel only.** `hgcdSafeApply a b =
(hgcdMatrixSafeOf a b).apply (↑a, ↑b) = (hgcdMatrixSafe ((a+b)+1) a b).apply
(↑a, ↑b)` — fuel is pinned to `a + b + 1`.

`outer-fires (a, b)` is therefore a statement about the **operational outer
HGCD step on `(a, b)`**, not a recursively-defined predicate that descends to
sub-pairs. To carry "outer-fires" through an induction on the recursion's depth,
one would need either:

- a separate propagation lemma stating "outer-fires (a, b) ⇒ outer-fires (u, v)";
- or a different inductive predicate that is naturally compositional under the
  recursion structure.

Neither is supplied by S43's §3.4 strategy.

## §3. Why the propagation is non-trivial (= S32b in disguise)

Suppose we wanted to prove `outerFires_propagates_to_inner_reduced` (the
hypothetical lemma in §0). Unfolding:

- Hypothesis: `max (hgcdSafeApply a b).natAbs < max a b`.
- Conclusion: `max (hgcdSafeApply u v).natAbs < max u v`.

The hypothesis bounds the outer apply's natAbs-max on `(a, b)` by `max a b`.
The conclusion bounds the outer apply's natAbs-max on `(u, v)` by `max u v`.

`(u, v)` is the natAbs of `M_inner.apply (↑a, ↑b)` where `M_inner = hgcdMatrixSafe
(a+b) (a/2^s) (b/2^s)`. The natAbs `(u, v)` need not equal `(a/2^s, b/2^s)` —
indeed, S32b's algebraic gap is precisely about the relationship between
`(u, v)` and the recursion's index `(a/2^s, b/2^s)`.

So `outer-fires (u, v)` asks: does `hgcdSafeApply u v` strictly reduce on
`(u, v)`? This unfolds to a fresh non-expansion question at fuel `u + v + 1`
on inputs `(u, v)` — **the same kind of question as the original S32b but at
smaller inputs**. To prove the propagation, we'd need an inductive
**non-expansion invariant** spanning all recursive call-sites — which is the
very thing S32b sets out to establish.

**Conclusion: the propagation lemma is at least as hard as S32b itself.**
S43's §3.4 strategy doesn't bypass the non-expansion question; it re-states it
in the outer-guard-fires variable.

## §4. Side-correction: `lehmerCofactors_id_apply_natAbs_max_le` is `lehmerCofactors_id_apply_le`

S43 PREP §3.3 (B) "below threshold" sub-case states:

> apply equals `lehmerCofactors hgcdThresholdSafe p q CofactorMatrix.id .apply …`.
> The parent file (`BinaryGcdOQ03OQ02.lean` PART V.5) has
> `lehmerCofactors_id_apply_natAbs_max_le` — or, if not, the bound reduces to
> that of `lehmerCofactors` (Lehmer's algorithm's non-expansion).

### Verification

`proofs/Proofs/BinaryGcdOQ03OQ02.lean:439–450`:

```lean
theorem lehmerCofactors_id_apply_le (fuel ahat bhat : ℕ) :
    ∃ ahat' bhat' : ℕ,
      (ahat : ℤ) * (lehmerCofactors fuel ahat bhat CofactorMatrix.id).α
        + (bhat : ℤ) * (lehmerCofactors fuel ahat bhat CofactorMatrix.id).γ
            = (ahat' : ℤ) ∧
      (ahat : ℤ) * (lehmerCofactors fuel ahat bhat CofactorMatrix.id).β
        + (bhat : ℤ) * (lehmerCofactors fuel ahat bhat CofactorMatrix.id).δ
            = (bhat' : ℤ) ∧
      max ahat' bhat' ≤ max ahat bhat := by
  apply lehmerCofactors_invariant_le
  · simp [CofactorMatrix.id]
  · simp [CofactorMatrix.id]
```

**Actual name: `lehmerCofactors_id_apply_le`** (no `_natAbs_max` qualifier).
**Statement returns**: a **natural-number** witness pair `(ahat', bhat') : ℕ × ℕ`
that the row-vector-by-cofactor-matrix product equals `(ahat' : ℤ, bhat' : ℤ)`
AND `max ahat' bhat' ≤ max ahat bhat`.

This is **not** a direct natAbs bound on `(hgcdMatrixSafe f p q).apply (↑p, ↑q)`.
The S43 PREP §3.3 (B) below-threshold dispatch through this lemma needs the
additional step:

```
apply natAbs of the apply output (which is a ℤ × ℤ pair) =
existential ahat'/bhat' from the lemma (which are ℕ × ℕ)
```

This is **automatic** because the apply output's natAbs is exactly `(ahat'.natAbs, bhat'.natAbs) = (ahat', bhat')` (since `ahat', bhat' : ℕ`). So the bound transfers, but the S43 PREP needs to add the natAbs extraction step explicitly.

**LOC impact on S44 ACT skeleton**: +5 LOC for the natAbs-extraction step in the
below-threshold branch of (B). Trivial.

## §5. Salvageable parts of S43 PREP

S43 PREP's contributions remain useful:

- **§1** (S32b target restated): correct verbatim from `s32-non-expansion-analysis.md` §6.
- **§2** (induction template setup, NE-cond★, abbreviations): correct;
  reflects PART XXX's affordance accurately.
- **§2.2** (base cases `f = 0`, `f + 1 = 2`): correct; the `compFires (0, p, q)`
  unsatisfiability argument via `lt_irrefl` is right.
- **§2.3** (inductive step reduction to "(⋆⋆) non-expansion of `hgcdMatrixSafe
  f` on `(u_int, v_int)`"): correct; identifies the **right** residual gap.
- **§3.1–§3.3** (sign-symmetry (A) + canonical-input (B) split): correct.
- **§4 skeleton** with three explicit `sorry`s (ALG.A, ALG.B, ALG.C): **the
  three `sorry`s are well-identified**. The structural skeleton compiles
  with these gaps named.

**Deficient part: §3.4 strategy ("propagate via PART XXIV").** The §3.4
strategy does not eliminate the (B) `sorry` because PART XXIV does not
propagate; the propagation is essentially the open question.

**Recommended revision of S43.** Drop §3.4's "Strategy: outer-fires-propagation"
recommendation. Replace with: §4's three-sorry skeleton stands as the honest
S44 ACT deliverable. The (B) `sorry` (= `hgcdMatrixSafe_apply_natAbs_bound_canonical`,
the canonical-input non-expansion) is the **deep mathematical gap** that
matches the spec's "~50 lines for the algebraic gap" estimate, and remains
open at the abort-branch case (which S43 §3.3 itself correctly identifies as
the obstruction).

## §6. Anti-targets (this S43b PREP explicitly does NOT do)

1. **Does not propose a replacement strategy for the abort-branch obstruction.**
   That is the open S32b problem; this PREP only audits S43's claim that PART
   XXIV bypasses it, and concludes the claim is incorrect.
2. **Does not modify any Lean file.** Pure design-memo audit.
3. **Does not edit `state.md` / `knowledge.md` / `problem.md` / `meta.json` /
   gallery JSON.** Strictly additive `sessions/` file. Disjoint from any
   in-flight PR's file set.
4. **Does not retract S43's §1, §2, §3.1–§3.3, or §4 skeleton.** These remain
   useful and accurate; only §3.4 is corrected.
5. **Does not propose a new propagation lemma proof.** Proving
   `outerFires_propagates_to_inner_reduced` is essentially as hard as the
   original S32b deliverable.

## §7. Honesty / what could be wrong

- **My re-reading of "propagates down all levels"** may be uncharitable to
  S43 PREP author. An alternative reading: "S43 §3.4 means PART XXIV gives
  outer-fires on the level-(a+b) inner-recursion, and the induction can re-derive
  outer-fires at each lower fuel as it descends, by repeatedly invoking PART
  XXIV on the reduced inputs." This is *also* circular though: invoking PART
  XXIV on `(u, v)` requires `outer-fires (u, v)`, which is what we're trying to
  derive. So the strategic gap stands under either reading.
- **The §4 name correction** (`lehmerCofactors_id_apply_natAbs_max_le` →
  `lehmerCofactors_id_apply_le`) is from direct file read at commit
  `34f70524df7` (the worktree's `origin/main` head). If the parent file is
  renamed between now and S44 ACT, the actual name may shift; the strategic
  content (returns Nat witness pair, not direct natAbs bound) should remain.
- **I have NOT verified §2 / §3.1–§3.3 of S43 PREP line-by-line.** Spot-checks
  on the type signatures of `hgcdMatrixSafe_apply_compose_branch` (PART XXX,
  line 2774) and `hgcdMatrixSafe_zero_natAbs_max_eq` (PART XXVII) confirm the
  S43 PREP's signature claims are accurate. The PART XXIV claim is the load-
  bearing one; I focused there.
- **The "circular" framing of S43 §3.4** may be too strong if there's an
  off-the-shelf Mathlib termination-invariant that I missed. A grep for
  `WellFoundedRecursion`-flavoured patterns in the file returns nothing
  relevant; the file's inductive structure is entirely fuel-bounded on `ℕ`,
  so the natural induction is on the fuel parameter `f`, which is what S43 §2
  proposes.

## §8. Race awareness

Pre-push checks (2026-05-13 ~03:35 UTC):

- `gh pr list --repo rjwalters/lean-genius --state open --search "binary-gcd
  in:title"` returns 1 open PR: #17304 (S23 outer-guard, 2026-05-08, stale).
  Disjoint — that PR targets the old PART XIII insertion point at file line
  ~735 (pre-S26 numbering and DIRTY).
- This PREP's filename: `2026-05-13-s43b-strategic-gap-audit.md` — distinct
  from S43's `2026-05-12-s43-fuel-generic-induction-strategy.md` (the only
  other file in `sessions/`).
- `gh pr list --search "binary-gcd-oq-03-oq-02 s43b"` returns 0 PRs.
- No Mechanic/Doctor PRs in flight on this slug.

**Conflict surface: 0.** Single new `sessions/` file.

## §9. Cross-references

- **S30** (PART XX, PR #17631, merged) — `hgcdMatrixSafe_inner_abort_imp_outer_fails`:
  the contrapositive of PART XXIV.
- **S31** (PART XXI, PR #17683, merged) — `_compose_branch` decomposition.
- **S32 spec** (`s32-non-expansion-analysis.md`, PR #17720) — §6 deliverable
  signature; this slug's open problem.
- **S34** (PART XXIII, PR #17771, merged) — `_abort_branch` decomposition (dual
  of S31).
- **S36** (PART XXIV, PR #17846, merged) — `schonhageOuterGuardFires_above_imp_inner_fires`:
  the load-bearing lemma S43 §3.4 cites incorrectly.
- **S37** (PART XXV, PR #17867, merged) — outer-fires packaging that fuses
  S36 with S31.
- **S39** (PART XXVII, PR #17965, merged) — fuel-zero base case.
- **S41** (PART XXIX, PR #18115, merged) — fuel-one above-threshold collapse.
- **S42** (PART XXX, PR #18259, merged) — fuel-generic compose/abort branches.
- **S43 PREP** (`2026-05-12-s43-fuel-generic-induction-strategy.md`, merged)
  — the audit target for this PREP.

## §10. Next iteration after this PREP

Two paths:

1. **S44 ACT with three honest sorries.** Implement S43 §4's skeleton with the
   `sorry`s left in place for ALG.A (sign-symmetry, ~40 lines, tractable),
   ALG.B (canonical-input non-expansion, the deep gap), ALG.C (final
   composition). The (A) sorry can be closed in the same PR; the (B) sorry
   remains open as a strategic-gap commitment.
2. **S44 PREP: propagation lemma audit.** Before ACT, scope what
   `outerFires_propagates_to_inner_reduced` would look like as a Lean
   theorem. If a proof path exists via, e.g., the recursion's structural
   `Nat.gcd`-correctness proof + `lt_of_lt_of_le`-style transitivity, the
   strategy may yet be salvageable. Pre-flight risk: per §3 above, this
   propagation is hard.

This S43b PREP **does not commit** to either path. It only closes the
strategic-gap audit on §3.4 and corrects the lemma-name reference in §3.3.

## §11. Future status

Unchanged from S43 PREP: post-S32b discharge (whenever and however it happens),
the parent open conjecture (binary-gcd-oq-03-oq-02) admits a complete
Lean-checked proof of HGCD non-expansion. This S43b PREP **does not advance
the discharge**; it audits the prior PREP for one strategic claim that, if
followed, would lead the S44 ACT implementer to attempt a circular argument
and fail.

The contribution: **prevent the S44 ACT implementer from wasting time on the
§3.4 strategy by surfacing the propagation gap before the build attempt.**
