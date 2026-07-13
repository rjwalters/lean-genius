# Session 3 — OQ-01-A.2 `resampleAt` PMF construction analysis (researcher-5, 2026-05-12)

**Mode.** ANALYSIS-ONLY (no `.lean` edits in this PR).

**Scope.** Doc-only roadmap for closing the single deferred sorry in
`proofs/Proofs/MoserTardos.lean` introduced by S2 ACT (PR #18213, branch
`research/prob-method-lovasz-local-oq-01-s2-moser-tardos-skeleton-1778605965`):
the `resampleAt` product-PMF construction (lines 130-140 of the S2 file).

This session does **not** modify the parent `state.md`, `knowledge.md`,
`problem.md`, the gallery JSON, or any Lean file. It is a pure session
note that lays the algebraic groundwork for the next iteration so that
the S3 ACT PR can land a compact (~10–20 line) Lean patch with high
confidence.

## 1. Target sorry (verbatim from S2)

From PR #18213, `MoserTardos.lean` lines ~125–140:

```lean
noncomputable def resampleAt (S : Finset (Fin P.numVars)) (v : P.State) :
    PMF P.State := by
  -- Full construction (deferred):
  --   Let `q j := if j ∈ S then PMF.uniformOfFintype (P.alphabet j) else PMF.pure (v j)`
  --   and produce the dependent product `PMF ((j : Fin P.numVars) → P.alphabet j)`
  --   via iteration over `Finset.univ : Finset (Fin P.numVars)`.
  exact sorry
```

Recall `P.State` abbreviates `(j : Fin P.numVars) → P.alphabet j`, with
field-encoded instances `alphabetFintype j : Fintype (P.alphabet j)` and
`alphabetNonempty j : Nonempty (P.alphabet j)` for every `j`. These are
already attached as local instances at the top of the `MTProblem`
namespace via `attribute [instance] alphabetFintype alphabetNonempty`.

The target is a `PMF P.State`, i.e. a probability mass function whose
sample space is the full assignment space. Mathematically, conditional
on `v` and the resampling set `S`,

  `resampleAt S v` samples each variable `j ∈ S` independently from the
  uniform distribution on `P.alphabet j`, while leaving each variable
  `j ∉ S` deterministically equal to `v j`.

## 2. Three candidate constructions

### 2.1 Approach A — `Finset.fold` over `S` with `PMF.bind` + `Function.update`

```lean
noncomputable def resampleAt (S : Finset (Fin P.numVars)) (v : P.State) :
    PMF P.State :=
  S.fold (· >>= ·) (PMF.pure v)
    (fun (j : Fin P.numVars) (acc : PMF P.State) =>
      acc.bind (fun w =>
        (PMF.uniformOfFintype (P.alphabet j)).map
          (fun a => Function.update w j a)))
```

**Issue.** `Finset.fold` requires the binary operation to be left-
commutative and right-commutative, i.e. the two updates `Function.update
w j a` and `Function.update w' j' a'` must commute when `j ≠ j'`. This
*is* true point-wise, but the bookkeeping at the `PMF` level needs the
auxiliary identity

  `(PMF.bind (PMF.bind μ f) g)` reorders to `(PMF.bind (PMF.bind μ g) f)`

whenever `f a` and `g a'` touch disjoint indices via `Function.update`.
This is provable from `PMF.bind_comm` (commutativity of independent
`PMF.bind`) but requires nontrivial wiring at the `Finset.fold`
hypothesis level (~30 extra Lean lines proving the commutativity hypothesis).

**Verdict.** Mathematically clean, structurally cumbersome. Not
recommended for OQ-01-A.2.

### 2.2 Approach B — `PMF.uniformOfFintype` on the dependent product type

```lean
noncomputable def resampleAt (S : Finset (Fin P.numVars)) (v : P.State) :
    PMF P.State :=
  (PMF.uniformOfFintype (∀ j : S, P.alphabet j.val)).map
    (fun (a : ∀ j : S, P.alphabet j.val) (j : Fin P.numVars) =>
      if h : j ∈ S then a ⟨j, h⟩ else v j)
```

**Why this works.** The coercion `↥S` from `Finset.instCoeHTCSort` makes
`(j : S)` a subtype of `Fin P.numVars` carrying the membership proof.
The type `∀ j : S, P.alphabet j.val` is a finite dependent product of
finite nonempty types, and uniform-on-a-product equals product-of-uniforms
by construction of `PMF.uniformOfFintype` together with
`Fintype.card_pi`. The `map`'s gluing function is total (the `if h :
j ∈ S` uses `Finset.decidableMem`).

**Typeclass synthesis.**

* `Fintype (∀ j : S, P.alphabet j.val)` — from `Fintype.subtype` on the
  Finset `S` plus `Pi.fintype` and the local instance
  `alphabetFintype j.val : Fintype (P.alphabet j.val)`. Mathlib has this
  as `Pi.instFintype` (in `Mathlib.Data.Fintype.Pi`).
* `Nonempty (∀ j : S, P.alphabet j.val)` — from `Pi.instNonempty` and
  the local instance `alphabetNonempty j.val : Nonempty (P.alphabet j.val)`.

Both are auto-synthesized via `inferInstance` in `noncomputable def`
position.

**Lines.** ~6–10 Lean LOC including the `Function.update`-style glue.

**Verdict.** Recommended. Most direct.

### 2.3 Approach C — Mathlib's `MeasureTheory.Measure.pi` lift to `PMF`

Mathlib has `MeasureTheory.Measure.pi` (the product measure on a
dependent Pi-type) which produces a `Measure` (not a `PMF`). To recover
a `PMF` we would need:

```lean
PMF.ofFinset (∀ j : S, P.alphabet j.val) ⟨…⟩
```

or convert via `Measure.toPMF` (does not exist as a single API surface).
The `PMF` ↔ `Measure` bridge in Mathlib goes through `PMF.toMeasure` in
one direction only; the reverse direction requires `Measure.ennrealToReal`
plus a finite-support certificate.

**Verdict.** Strictly more general than Approach B but loses ~3× lines
to packaging. Not recommended.

## 3. Independence and the LLL faithfulness clause

A crucial sanity check: the `vblFaithful` field of `MTProblem` says

  `(∀ j ∈ vbl i, v j = w j) → (P.isBad i v ↔ P.isBad i w)`

i.e. `isBad i` depends only on the variables in `vbl i`. When the
Moser–Tardos analysis (OQ-01-B + OQ-01-C) appeals to "the resampled
variables are independent of the variables in `vbl(A_k)` for
`k ∉ Γ(i)`", the formal statement is

  for `S = vbl i` and `T ⊆ Fin numVars \ vbl i` with `T ∩ S = ∅`,
  the marginals of `(resampleAt S v)` on `T` are deterministic at `v ↾ T`.

This follows immediately from Approach B's construction because the
`map`'s glue function returns `v j` (deterministic) whenever `j ∉ S`.
**Approach B preserves the necessary measurable structure for OQ-01-B/C
"for free".** Approach A would need an additional lemma; Approach C
would need a measure-theoretic conditional.

## 4. Three follow-on lemmas anticipated for OQ-01-B

After Approach B lands, the following three sorry-free lemmas are
expected to be useful immediately:

```lean
lemma resampleAt_apply_outside (S : Finset (Fin P.numVars))
    (v : P.State) (w : P.State) (j : Fin P.numVars) (hj : j ∉ S) :
    -- The marginal at j ∉ S equals v j with probability 1.
    (P.resampleAt S v).map (· j) = PMF.pure (v j)

lemma resampleAt_apply_inside (S : Finset (Fin P.numVars))
    (v : P.State) (j : Fin P.numVars) (hj : j ∈ S) :
    -- The marginal at j ∈ S equals the uniform on alphabet j.
    (P.resampleAt S v).map (· j) = PMF.uniformOfFintype (P.alphabet j)

lemma resampleAt_indep (S : Finset (Fin P.numVars)) (v : P.State)
    (T : Finset (Fin P.numVars)) (hT : Disjoint T S) :
    -- Restricted to T ⊆ Fin numVars \ S, the resampleAt distribution
    -- is deterministically v ↾ T.
    (P.resampleAt S v).map (fun w => (fun j : T => w j.val)) =
      PMF.pure (fun j : T => v j.val)
```

The first two are corollaries of `PMF.map_uniformOfFintype_fst/snd` and
`Function.update`-on-index. The third is a `Finset.map` lift.

## 5. Build-verification risks

Three potential traps for the S3 ACT implementer:

### 5.1 `(∀ j : S, P.alphabet j.val)` — instance synthesis pitfalls

The coercion `↥S : Type` is `{x : Fin P.numVars // x ∈ S}`. `Fintype`
on this is derived from `S.fintypeCoeSort` (in `Mathlib.Data.Finset.Basic`).
The Pi-Fintype `Pi.instFintype` then needs each fiber's `Fintype`. Both
should synthesize with no manual instance arguments; if synthesis fails,
the workaround is

```lean
have : Fintype (∀ j : S, P.alphabet j.val) := by
  apply Pi.instFintype
exact (PMF.uniformOfFintype _).map _
```

but this defeats `noncomputable def` ergonomics. Better to add an
explicit `attribute [instance] Finset.fintypeCoeSort` near the top of
the file if needed (it should already be a global instance).

### 5.2 `Function.update` vs `if h : j ∈ S` style

The `if h : j ∈ S then a ⟨j, h⟩ else v j` form uses dependent `if`,
which requires `Decidable (j ∈ S)`. This is auto-synthesized via
`Finset.decidableMem`. If a future refactor switches to `Function.update
... v` style (folded over `S`), the resulting term may compute differently
at definitional equality — preserves the `Decidable` discipline but
breaks `simp` lemmas that pattern-match on the `if`. Recommend keeping
the `if h : j ∈ S` form for OQ-01-A.2.

### 5.3 `PMF.uniformOfFintype` requires `Nonempty`, not `Fintype.card > 0`

Mathlib v4.26.0 ships `PMF.uniformOfFintype (α : Type*) [Fintype α]
[Nonempty α] : PMF α`. The signature requires `Nonempty α` explicitly
(not just `Fintype.card α ≠ 0`). Both `Nonempty (∀ j : S, P.alphabet j.val)`
and the field-encoded `P.alphabetNonempty` are stocked correctly.

If `S = ∅`, the type `∀ j : (∅ : Finset _), P.alphabet j.val` is a
singleton (the unique function from the empty type), automatically
`Nonempty` and `Fintype` of cardinality 1. The `resampleAt ∅ v` then
correctly produces `PMF.pure v`. This is a useful sanity-check the S3
ACT PR should verify with a one-line `@[simp]` lemma:

```lean
@[simp] lemma resampleAt_empty (v : P.State) : P.resampleAt ∅ v = PMF.pure v
```

## 6. Recommended S3 ACT PR shape

* **One file changed**: `proofs/Proofs/MoserTardos.lean`.
* **Diff**:
  - Delete the 4-line `by` block and `exact sorry`.
  - Insert ~6 lines: Approach B's `(PMF.uniformOfFintype _).map (fun a j => if h : j ∈ S then a ⟨j, h⟩ else v j)`.
  - Add the `resampleAt_empty` simp lemma (3 lines).
* **Build verification**: required (Docker wrapper). `lake build
  Proofs.MoserTardos` should pass cleanly.
* **Net sorry delta**: `MoserTardos.lean` 1 → 0 sorries (excluding the
  two `True`-shell theorems `mt_expected_step_bound` /
  `mt_terminates_as`, which remain placeholder).
* **Net `axiomCount` delta**: 0.

## 7. Out of scope for S3 ACT

The following are explicitly deferred and **must not** be bundled into
the S3 ACT PR:

1. Closing the `mt_expected_step_bound` and `mt_terminates_as`
   placeholders. These require the full OQ-01-B (witness tree) and
   OQ-01-C (Galton–Watson) infrastructure, ~500–800 Lean lines.
2. Adding a `MeasureTheory.Measure`-level reformulation. The `PMF`-level
   formulation is the canonical Moser–Tardos statement and stays
   `PMF`-native throughout.
3. Sibling-slug deduplication with `lovasz-local-lemma-oq-03`. Tracked
   separately; do not block S3 on this.
4. Wiring `resampleAt` into the parent `Proofs/LovaszLocalLemma.lean`
   (which uses the algebraic LLL, not the algorithmic Moser–Tardos
   form). Deferred to OQ-01-B's `WitnessTree` introduction.

## 8. Race-safety acknowledgment

This session note is created **while PR #18213 (S2 ACT) is still open**.
The note deliberately:

* does NOT modify `state.md`,
* does NOT modify `knowledge.md`,
* does NOT modify `problem.md`,
* does NOT modify `src/data/research/problems/prob-method-lovasz-local-oq-01.json`,
* does NOT modify any `.lean` file,
* and is placed under a unique session-file name (`-s03-resampleAt-pmf-construction`)
  so it cannot collide with a future "Session 3" file authored by the
  S2 PR's follow-on.

Once PR #18213 lands, the *next* researcher (S3 ACT) can pull this note
forward, implement Approach B, build-verify, and update `state.md` +
`knowledge.md.nextSteps` to reflect the closure of OQ-01-A.2.

## 9. Files added (this session)

* `research/problems/prob-method-lovasz-local-oq-01/sessions/2026-05-12-s03-resampleAt-pmf-construction.md` — this file.

No other files modified. Zero Lean changes. Zero gallery-JSON changes.

## 10. Build status

No `.lean` changes. Build not attempted (no diff to verify). The S2 PR
#18213 carries the build-pending status for the underlying
`MoserTardos.lean`.

## 11. References

* Moser, Robin A., and Gábor Tardos. **"A constructive proof of the
  general Lovász local lemma."** *J. ACM* 57.2 (2010), Theorem 1.2
  and §4 (witness-tree construction).
* Mathlib `Mathlib.Probability.ProbabilityMassFunction.Basic` — the
  `PMF` definition, `PMF.bind`, `PMF.pure`, `PMF.map`.
* Mathlib `Mathlib.Probability.ProbabilityMassFunction.Uniform` —
  `PMF.uniformOfFintype` and its `apply`-rewrite lemmas.
* Mathlib `Mathlib.Data.Fintype.Pi` — `Pi.instFintype` and
  `Finset.fintypeCoeSort`.
