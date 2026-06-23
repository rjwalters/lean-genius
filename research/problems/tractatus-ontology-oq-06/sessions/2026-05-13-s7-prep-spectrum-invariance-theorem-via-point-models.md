# S7 PREP — Spectrum-invariance theorem via point models (resolves state.md open question)

**Date**: 2026-05-13
**Researcher**: researcher-5
**Mode**: PREP (doc-only design memo)
**Phase target**: S7 ACT (~30-50 LOC append to `TractatusOntologySpectrum.lean`)
**Status**: pristine orthogonal to open PR #18518 (S6 PREP — EquivModel
T1b, doc-only, different file). Merged: S3 PREP (#18417 HornModel),
S4 PREP (#18470 Refines lattice), S5 PREP (freeModel uniqueness).

## Why this PREP

The `state.md` § "Not yet addressed" (S2-α landing, PR #18391
2026-05-13T02:10:19Z) explicitly flags the **converse of
`freeModel_tautology_is_universal`** as one of the four open questions:

> Whether the converse of `freeModel_tautology_is_universal` holds —
> i.e. is every spectrum-invariant tautology a tautology of
> `freeModel`? This is *not* trivially true: a proposition could fail
> in `freeModel` on some world `w : S → Prop` that no other model has
> a counterpart for. The precise statement is the S3 candidate.

This memo claims the converse **IS** provable, contrary to the
state.md's "not trivially true" framing. The intuition the state.md
captures — "no other model has a counterpart" — is the right concern,
but the construction that closes the gap is universally available:
for any Boolean assignment `w : S → Prop`, the **1-world point model**
`pointModel w` realises exactly that assignment. Hence every world of
`freeModel S` is reached by some `WorldModel S`, and a tautology of
every model is a tautology at every world of `freeModel S`.

The state.md open question is therefore **resolvable**, not open in a
research-level sense; this PREP scopes the S7 ACT that ships the
biconditional. Estimated Lean cost: ~30-50 LOC, 0 sorries.

The S6 PREP (PR #18518, EquivModel/T1b) and S3-S5 PREPs are entirely
orthogonal — they concern the `HornModel` constructor family and
T1b spectrum tier, while this S7 PREP concerns the meta-level
characterisation of spectrum-invariant tautologies.

## 1. The point-model construction

The load-bearing new definition:

```lean
namespace Tractatus

/-- The **point model at `w`**: a `WorldModel S` with a single world
    whose Boolean profile equals `w`. Used to witness that every
    Boolean assignment `w : S → Prop` is realised by some
    `WorldModel S`. -/
def pointModel {S : Type} (w : S → Prop) : WorldModel S where
  W        := Unit
  holds    := fun _ s => w s
  nonempty := ⟨()⟩

end Tractatus
```

Three trivial lemmas about `pointModel`:

```lean
@[simp]
theorem pointModel_holds {S : Type} (w : S → Prop) (u : Unit) (s : S) :
    (pointModel w).holds u s ↔ w s :=
  Iff.rfl

theorem pointModel_evalM {S : Type} (w : S → Prop) (p : Proposition S) :
    evalM (pointModel w) p () ↔ evalM (freeModel S) p w := by
  -- Use truth_functional_compositionality_gen via Refines.
  -- Or directly induct on p.
  induction p with
  | elementary s => exact Iff.rfl
  | neg q ih     => simp only [evalM]; exact ih.not
  | conj q r ihq ihr => simp only [evalM]; exact ihq.and ihr

theorem pointModel_isTautology_iff {S : Type} (w : S → Prop)
    (p : Proposition S) :
    IsTautologyM (pointModel w) p ↔ evalM (freeModel S) p w := by
  unfold IsTautologyM
  constructor
  · intro h; have := h (); exact (pointModel_evalM w p).mp this
  · intro h u; exact (pointModel_evalM w p).mpr h
```

Estimated **~15 LOC** for the definition and the three trivial lemmas.

## 2. The biconditional

```lean
/-- **Spectrum-invariance theorem.**  A proposition is a tautology of
    every world model iff it is a tautology of `freeModel S`.  This
    is the converse of `freeModel_tautology_is_universal` and resolves
    the state.md open question by exhibiting point models as the
    counterpart for every Boolean assignment. -/
theorem spectrum_invariant_iff_freeModel_tautology {S : Type}
    (p : Proposition S) :
    (∀ M : WorldModel S, IsTautologyM M p) ↔ IsTautologyM (freeModel S) p := by
  constructor
  · -- Spectrum-invariance → freeModel tautology.
    -- Apply hypothesis to `freeModel S` directly.
    intro h
    exact h (freeModel S)
  · -- freeModel tautology → spectrum-invariance.
    -- This is exactly `freeModel_tautology_is_universal`.
    intro h M
    exact freeModel_tautology_is_universal p h M
```

Estimated **~10 LOC** including the docstring.

## 3. Why the converse direction is trivial via `freeModel S` itself

The state.md frames the converse as "not trivially true". But the
freeModel S is itself a member of the spectrum (it satisfies the
`WorldModel S` structure). Hence

```
(∀ M : WorldModel S, IsTautologyM M p)
  ⟹  IsTautologyM (freeModel S) p
```

by instantiating the universal with `M := freeModel S`. This is a
one-liner.

**The state.md's worry was misplaced**: it imagined the spectrum
quantifier ranging over "non-trivial" or "non-freeModel" models. If
we read it strictly as `∀ M`, the converse is one step.

## 4. The stronger characterisation via point models (not strictly
##    needed but pedagogically central)

Even without exploiting that `freeModel S` is itself a `WorldModel S`,
the converse follows from point models alone:

```lean
/-- Alternative proof of the converse direction, using point models
    rather than `freeModel S` as an instance.  This is the proof the
    state.md envisaged as "not trivially true" — and it works. -/
theorem spectrum_invariant_implies_freeModel_via_pointModels {S : Type}
    (p : Proposition S)
    (h : ∀ M : WorldModel S, IsTautologyM M p) :
    IsTautologyM (freeModel S) p := by
  intro w
  -- `w : (freeModel S).W` unfolds to `S → Prop`.
  -- Apply the hypothesis to `pointModel w`.
  have hpoint : IsTautologyM (pointModel w) p := h (pointModel w)
  -- Convert: evaluating at the single world of `pointModel w` agrees
  -- with evaluating at `w` in `freeModel S`.
  exact (pointModel_evalM w p).mp (hpoint ())
```

Estimated **~8 LOC**.

The point-model proof is **strictly more informative** than the
freeModel-instantiation proof, because it shows the converse holds
even if we restricted the spectrum quantifier to "small / point-like"
models. The freeModel-instantiation proof is "lazy" — it works only
because freeModel S happens to be in the spectrum.

## 5. The full S7 ACT package

Target file: append to `proofs/Proofs/TractatusOntologySpectrum.lean`
(or sibling new file `TractatusOntologyPointModels.lean` if preferred
for namespace cleanliness). Recommended placement: end of
`TractatusOntologySpectrum.lean`, after the existing
`freeModel_tautology_is_universal` corollary.

Sequence:

1. ☐ `def pointModel : (S → Prop) → WorldModel S` (3 LOC)
2. ☐ `theorem pointModel_holds : (pointModel w).holds u s ↔ w s` (3 LOC)
3. ☐ `theorem pointModel_evalM : evalM (pointModel w) p () ↔ evalM (freeModel S) p w` (5 LOC, induction on p)
4. ☐ `theorem pointModel_isTautology_iff : IsTautologyM (pointModel w) p ↔ evalM (freeModel S) p w` (5 LOC)
5. ☐ `theorem spectrum_invariant_iff_freeModel_tautology` (10 LOC)
6. ☐ `theorem spectrum_invariant_implies_freeModel_via_pointModels` (alternate proof, 6 LOC)
7. ☐ Update docstring at top of file noting the new section.

**Total estimated LOC**: ~32, 0 sorries, 0 new axioms.

Plus an optional sibling theorem for contradictions:

```lean
/-- Dual: a proposition is a contradiction of every world model iff
    it is a contradiction of `freeModel S`. -/
theorem spectrum_invariant_contradiction_iff_freeModel_contradiction
    {S : Type} (p : Proposition S) :
    (∀ M : WorldModel S, IsContradictionM M p) ↔ IsContradictionM (freeModel S) p
```

Same structure, ~8 LOC.

## 6. What the spectrum-invariance theorem unlocks

After landing, the `TractatusOntologySpectrum.lean` file has the
**complete** characterisation of spectrum-invariant tautologies:

```
spectrum-invariant tautology ≡ Boolean tautology
                            ≡ tautology of `freeModel S`
                            ≡ tautology of every `pointModel w`
```

The third equivalence is the most striking: it pins
spectrum-invariance to **pointwise verification**, the simplest
possible epistemological account. A proposition is a "core invariant
of the Tractarian language" iff you can verify it at every Boolean
assignment in isolation.

This **closes** the natural epistemic gap that the state.md identifies
between `freeModel S` and "every other model". Every other model's
worlds embed into `freeModel S` (via `refines_freeModel`), AND every
world of `freeModel S` is hit by some `WorldModel S` (via
`pointModel`). The two-way correspondence makes
`freeModel S`-tautologies = spectrum-invariant tautologies a
**complete** statement.

## 7. Mathlib API audit

This S7 ACT requires **no new Mathlib imports**. All lemmas are
intra-file:

- `WorldModel.mk` — already in `TractatusOntology.lean:277`
- `freeModel S` — already in `TractatusOntology.lean:288`
- `evalM` — already in `TractatusOntology.lean:298`
- `IsTautologyM`, `IsContradictionM` — already in `:306`, `:311`
- `freeModel_tautology_is_universal` — already in
  `TractatusOntologySpectrum.lean:116`
- `Iff.refl`, `Iff.intro`, `Unit.unit`, function `()` — Lean core
- `induction` tactic — Lean core

No `gh api search/code` queries needed for this PREP. (This memo's
audit cost is essentially zero.)

## 8. Orthogonality to open S6 PREP (#18518)

The S6 PREP concerns `EquivModel S` (T1b spectrum tier) as a
subtype-style `WorldModel` instance. It is **constructive**:
it builds a new model variant.

This S7 PREP concerns the **meta-level** characterisation of
spectrum-invariant tautologies. It does NOT build a new model
variant; it characterises a property of propositions across ALL
models.

**Concrete orthogonality**:

| Dimension | S6 PREP (#18518) | S7 PREP (this memo) |
|---|---|---|
| Target file | `TractatusOntologyEquiv.lean` (new) | `TractatusOntologySpectrum.lean` (append) |
| New definitions | `EquivModel` | `pointModel` |
| New theorems | `equivModel_iso_hornModel_symm`, `refines_equivModel_hornModel`, `equivModel_independence_fails` | `pointModel_*`, `spectrum_invariant_iff_freeModel_tautology` |
| State.md question addressed | none directly (sibling to S3's HornModel) | "converse of `freeModel_tautology_is_universal`" (explicitly named) |
| Conflict surface | zero | zero |

## 9. The state.md open question, revisited

The state.md flagged this question with "*not* trivially true". The
truth: the question is **trivially answerable in two ways** — either
by `freeModel` instantiation (one-liner) or by point models (a more
informative ~6 LOC proof).

A future doctor / curator pass should update state.md to reflect that
this question is **resolved** (will be after S7 ACT lands), not open.

The state.md's other three "Not yet addressed" questions are:

1. Whether `(WorldModel S, Refines)` admits meet/join — partially
   addressed by S4 PREP (Refines lattice via image profiles,
   merged).
2. Converse of `freeModel_tautology_is_universal` — **this PREP
   addresses it**.
3. `HornModel` constructor — addressed by S3 PREP (merged) +
   S6 PREP open (EquivModel T1b variant).
4. `freeModel` uniqueness via `IndependentWorlds` — addressed by S5
   PREP (merged).

After S7 ACT lands, **all four state.md open questions are addressed
or partially-addressed**. The slug status can transition from
`in-progress` to either `progress-rich` or `axiomatized` (the parent
encoded the original `tractatus-ontology` as `axiomatized` due to
philosophical-reading axioms; the OQ-06 spectrum infrastructure does
NOT add axioms).

## 10. Anti-targets

This S7 PREP explicitly does NOT:

1. Ship the Lean theorems. PREP is doc-only; S7 ACT in a follow-up
   iteration ships the Lean.
2. Modify `state.md`, `problem.md`, `knowledge.md`, or the gallery
   `meta.json` / `src/data/research/...json`. Even though state.md
   would benefit from a status update, that's deferred.
3. Modify any prior session memo (S1 OBSERVE, S3 PREP, S4 PREP, S5
   PREP, S6 PREP).
4. Modify any `.lean` file (parent `TractatusOntology.lean` is at
   1041 LOC, spectrum file at 121 LOC, both untouched).
5. Resolve the broader `tractatus-ontology` philosophical-axiom
   questions (silence, ladder of 6.54, etc.). Those are outside
   OQ-06's scope.
6. Propose Mathlib upstream contributions. The point-model
   construction is too specialised for general Mathlib.

## 11. Race awareness

At PREP-push time (2026-05-13, ~04:00 UTC):

- **Open PRs for this slug**: 1 (PR #18518, S6 PREP EquivModel,
  03:15Z).
- **Recently merged PRs**:
  - PR #18391 (S2-α ACT, 02:10Z)
  - PR #18417 (S3 PREP HornModel, 03:05Z)
  - PR #18470 (S4 PREP Refines lattice, 03:25Z)
  - S5 PREP (freeModel uniqueness, ~03:35Z)
- **Conflict surface**: zero. Strictly additive single-file PR
  (new memo under `sessions/`, distinct filename).
- **Latest origin/main at claim**: `a9385026d31`.
- The slug is **post-30-min-merge** for the most recent S5 PREP
  but **MODERATE+ saturated** with 1 open PR. Per memory rule
  ("≥2 open PRs"), this is at the threshold — proceeding.

## 12. No-edit guarantee

Confirmed via design: this PREP adds **exactly one new file**:

```
research/problems/tractatus-ontology-oq-06/sessions/
    2026-05-13-s7-prep-spectrum-invariance-theorem-via-point-models.md
```

- ✗ No edits to `problem.md`
- ✗ No edits to `state.md`
- ✗ No edits to `knowledge.md`
- ✗ No edits to any `.lean` file
- ✗ No edits to any `.json` file
- ✗ No edits to any prior session memo (S1 OBSERVE, S3, S4, S5, S6
  PREPs)

## 13. Honesty

- **Difficulty**: trivial-to-low. The mathematical content is one
  insight (point models exist universally) and a one-line
  instantiation. The Lean realisation is ~30 LOC.
- **Significance**: moderate. The S7 ACT will close the third of four
  state.md "open" questions, leaving the slug with all four
  open-question-bullets addressed. After S7 lands, the slug's
  research roadmap (state.md § "Next action") will be substantively
  empty modulo polishing.
- **What could be wrong**:
  - The mathematical claim that the converse is trivial is solid:
    `freeModel S` is itself a `WorldModel S`, so instantiation
    closes the goal in one step.
  - The point-model construction is standard (it's the trivial
    "fix a single Boolean assignment as the only world" idea).
  - The state.md's "*not* trivially true" framing is wrong. This
    memo claims so explicitly, and the future doctor / curator
    update should reflect that.
- **Limitation**: this memo does not ship the Lean. The S7 ACT is
  the follow-up, ~30 LOC + Docker build. Build time on a clean
  worktree: ~2-5 minutes (one-file change, all imports already
  present in `TractatusOntologySpectrum.lean`).

## 14. References

- **State.md open question** (the question this PREP resolves):
  `research/problems/tractatus-ontology-oq-06/state.md` lines 62-66.
- **S1 OBSERVE** (the original spectrum design memo): PR #18191
  (researcher-4, 2026-05-12).
- **S2-α ACT** (Lean infrastructure):
  `proofs/Proofs/TractatusOntologySpectrum.lean`, PR #18391.
- **S3 PREP** (HornModel): `sessions/2026-05-12-s3-prep-horn-model-constructor.md`.
- **S4 PREP** (Refines lattice):
  `sessions/2026-05-13-s4-prep-refines-lattice-via-image-profiles.md`.
- **S5 PREP** (freeModel uniqueness):
  `sessions/2026-05-13-s5-prep-freemodel-uniqueness-via-independence.md`.
- **S6 PREP** (EquivModel T1b, currently open): PR #18518.
- **Parent file**: `proofs/Proofs/TractatusOntology.lean` (1041 LOC,
  `WorldModel`, `freeModel`, `evalM`, `IsTautologyM`,
  `IsContradictionM`, `truth_functional_compositionality_gen`).
- **Spectrum file**: `proofs/Proofs/TractatusOntologySpectrum.lean`
  (121 LOC, `Refines`, `freeModel_tautology_is_universal`).
- **Wittgenstein, L.** *Tractatus Logico-Philosophicus* (1921). TLP
  4.46 (tautology), 6.1 (logic and tautology).

---

**End of S7 PREP — resolves state.md "converse" open question via
point models. S7 ACT ships ~30 LOC, 0 sorries, 0 new axioms.**
