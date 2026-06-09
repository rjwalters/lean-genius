# S2 ACT — `coloringSetoid` + `coloringQuotientFintype` discharged via `AddAction.orbitRel`

**Date**: 2026-06-09
**Researcher**: researcher-1
**Type**: ACT — axiom discharges, Docker-verified.
**Scope**: Discharge the two abstract group-action API axioms
(`coloringSetoid`, `coloringQuotientFintype`) that S1b STATE-SYNC pinned
as the highest-priority next deliverable. Reduces `BurnsideCounting.lean`
from 4 axioms to 2.

## §1 Result

`BurnsideCounting.lean`: 370 → 387 LOC, axioms 4 → 2, theorems 7 → 7,
defs 7 → 9 (+`coloringSetoid`, +`coloringQuotientFintype`; the new
`coloringSetoid_decidableRel` is an `instance`, not a `def`). Sorries:
0 → 0. Docker: 3058 / 3058 jobs clean (same job count as S1 — the
new declarations all compile against the cached prefix).

Axioms remaining: `fixed_point_sum_binary_4` (S3 candidate via
`native_decide`) and `binary_necklaces_4` (S4 candidate via
`burnside_lemma`).

## §2 Surprise: no `Multiplicative` bridge needed

S1b STATE-SYNC §2 pinned an `AddAction → MulAction` bridge as the S2
plan:

> The S2 ACT needs to bridge `AddAction (ZMod n) → MulAction (Multiplicative (ZMod n))`
> so that `orbitRel.Quotient (Multiplicative (ZMod n)) (Coloring n k)` is
> a defined type and `coloringSetoid` becomes `MulAction.orbitRel _ _`.

That plan was over-engineered for the actual goal of discharging the
*setoid* axiom. Direct check against `Mathlib/GroupTheory/GroupAction/Defs.lean`
(line 279) shows:

```lean
/-- The relation 'in the same orbit'. -/
@[to_additive /-- The relation 'in the same orbit'. -/]
def orbitRel : Setoid α where
  r a b := a ∈ orbit G b
  iseqv := ⟨mem_orbit_self, ..., ...⟩
```

`orbitRel` carries `@[to_additive]`, so `AddAction.orbitRel (G : Type*) (α : Type*) [AddMonoid G] [AddAction G α] : Setoid α`
exists directly. The discharge collapses to a 2-line `def`:

```lean
def coloringSetoid (n k : ℕ) [NeZero n] : Setoid (Coloring n k) :=
  AddAction.orbitRel (ZMod n) (Coloring n k)
```

The `Multiplicative` bridge would only become necessary downstream in S4
when *applying* `burnside_lemma` (which is stated in `MulAction` form).
For the setoid axiom alone, it was unnecessary scaffolding.

## §3 The `Fintype` instance

For the quotient `Fintype`, `Quotient.fintype` (`Mathlib/Data/Fintype/Basic.lean:163`)
requires:

```lean
instance Quotient.fintype [Fintype α] (s : Setoid α)
    [DecidableRel ((· ≈ ·) : α → α → Prop)] : Fintype (Quotient s)
```

So we need (1) `Fintype (Coloring n k)` — automatic, since
`Coloring n k = Fin n → Fin k` and Lean's `Pi.fintype` handles
`Fin n → Fin k`; (2) decidability of the orbit equivalence relation.

The relation unfolds: `a ≈ b` in our setoid = `(coloringSetoid n k).r a b`
= `a ∈ AddAction.orbit (ZMod n) b`. By `AddAction.mem_orbit_iff`
(`@[to_additive]` on `MulAction.mem_orbit_iff` at `Defs.lean:54`), that's
`∃ x : ZMod n, x +ᵥ b = a`. Since `ZMod n` is `Fintype` for
`[NeZero n]` and `Coloring n k` has decidable equality (Pi over finite
indices), `Fintype.decidableExistsFintype` discharges it.

Implementation:

```lean
instance coloringSetoid_decidableRel (n k : ℕ) [NeZero n] :
    DecidableRel (coloringSetoid n k).r := fun a b =>
  decidable_of_iff (∃ x : ZMod n, x +ᵥ b = a) AddAction.mem_orbit_iff.symm

def coloringQuotientFintype (n k : ℕ) [NeZero n] :
    Fintype (Quotient (@coloringSetoid n k _)) := by
  letI : Setoid (Coloring n k) := coloringSetoid n k
  haveI : DecidableRel (α := Coloring n k) (· ≈ ·) := coloringSetoid_decidableRel n k
  exact Quotient.fintype _
```

The `letI` + `haveI` dance is needed because `Quotient.fintype` looks
up `(· ≈ ·)` via the `HasEquiv` instance derived from the in-scope
`Setoid`. With `letI` providing the setoid, `(· ≈ ·)` resolves to
`(coloringSetoid n k).r`, and the explicit `haveI` provides the
matching `DecidableRel` instance for instance search to find.

## §4 Why this didn't break `binary_necklaces_4`

The third remaining axiom (`binary_necklaces_4`) references both
discharged symbols explicitly:

```lean
axiom binary_necklaces_4 :
  @Fintype.card (Quotient (@coloringSetoid 4 2 _)) (coloringQuotientFintype 4 2) = 6
```

Both names continue to resolve: `coloringSetoid` was `axiom` →
`def`, `coloringQuotientFintype` was `axiom` → `def`. Both have the
same signature as before, so the explicit `@`-application call site is
unchanged. The `binary_necklaces_4` axiom is now stating that
`Fintype.card (Quotient (AddAction.orbitRel (ZMod 4) (Coloring 4 2))) = 6`
(with the specific Fintype instance derived from `Quotient.fintype`),
which is a strictly stronger / more concrete statement than the old
one over abstract axiomatic setoid + Fintype — and still axiomatic
until S4 wires it through `burnside_lemma`.

## §5 Build verification

```
$ ./proofs/scripts/docker-build.sh Proofs.BurnsideCounting
...
✔ [3058/3058] Built Proofs.BurnsideCounting (35s)
Build completed successfully (3058 jobs).
```

Three `linter.unusedSimpArgs` warnings in pre-existing code at lines
77, 299, 301 (`rotatedIndex_zero`, `period2_count` — both untouched by
this PR). No new warnings introduced. No new sorries. No new axioms.

## §6 Files modified

1. `proofs/Proofs/BurnsideCounting.lean` (UPDATE):
   - Lines 349–354: replaced 2 axioms (`coloringSetoid`,
     `coloringQuotientFintype`) with a `def` + `instance` + `def` block
     (~25 LOC including docstrings). Net +17 LOC.
2. `src/data/proofs/burnside-counting/meta.json` (UPDATE):
   - `axiomCount`: 4 → 2
   - `lineCount`: 370 → 387
   - `definitionCount`: 7 → 9
   - `assumptions`: rewritten to list the 2 remaining axioms + note S1
     and S2 discharges
   - `originalContributions`: +3 entries (coloringSetoid,
     coloringSetoid_decidableRel, coloringQuotientFintype)
   - `proofStrategy`: updated to reflect S2 progress
   - `openQuestions`: trimmed to just the S3/S4 + Polya/dihedral items
   - Mirror in `.leanFile` block: `lineCount`, `axiomCount`,
     `definitionCount` synced
3. `research/problems/burnside-counting-oq-01/state.md` (UPDATE):
   - Head phase + iteration + Last Updated bumped to S2 ACT / 2 / 2026-06-09
   - Lean inventory section recounted
   - Axiom inventory restructured into "remaining (after S2)" +
     "discharged in earlier iterations"
   - What's Next narrowed to S3 / S4 specifically
   - Session Log: new top entry for this iteration
4. `research/problems/burnside-counting-oq-01/sessions/2026-06-09-s2-act-orbitrel-bridge.md`
   (NEW, this file).
5. `src/data/research/problems/burnside-counting-oq-01.json`:
   - `currentState.phase`: OBSERVE → ACT
   - `currentState.iteration`: 1 → 2
   - `knowledge.progressSummary`, `knowledge.builtItems`,
     `knowledge.insights`, `knowledge.nextSteps`: synced with this
     iteration's deliverables.

## §7 Race / saturation

```
$ gh pr list --search "burnside-counting-oq-01 in:title" --state open
(no open PRs)
```

0 open PRs on slug at PR-creation time.

## §8 Honest scope

* **Discharges**: 2 axioms (`coloringSetoid`, `coloringQuotientFintype`).
* **Does NOT discharge**: `fixed_point_sum_binary_4` (S3) or
  `binary_necklaces_4` (S4). Both remain explicit axioms.
* **Does NOT** ship the `Multiplicative`-bridge that S1b STATE-SYNC
  pinned — that work turned out to be unnecessary for these two
  specific axioms, but may still be useful for S4's `burnside_lemma`
  application. The S1b STATE-SYNC §2.1 bearer-API pin is therefore
  partially superseded (still relevant for S4, no longer relevant for
  S2).
* **Does NOT** modify any other parent gallery file, any sibling proof
  file, or any test infrastructure.
* No new sorries. No new axioms. No new `lake-manifest.json` touches.

## §9 References

* Predecessor PRs: #21148 (S1 ACT, 2026-05-30), S1b STATE-SYNC PR
  (2026-06-03, doc-only).
* Mathlib v4.26.0 anchors:
  - `Mathlib/GroupTheory/GroupAction/Defs.lean:279-284` —
    `@[to_additive] def orbitRel`.
  - `Mathlib/GroupTheory/GroupAction/Defs.lean:54-55` —
    `@[to_additive] theorem mem_orbit_iff`.
  - `Mathlib/Data/Fintype/Basic.lean:163-165` —
    `instance Quotient.fintype`.
* Companion file `BurnsideCountingOQ03OQ03.lean` (sibling slug) sketches
  the `MulAction` connection chain; S4 may revisit it.
