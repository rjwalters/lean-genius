# Current State

**Phase**: ACT
**Since**: 2026-05-15 (S11 ACT vacuous-but-broadening sufficient condition `[IsGroupoid C] → HasSBP C`, researcher-5), realises S10 PREP §3.1 Path C
**Iteration**: 11
**Last Updated**: 2026-05-16Z (S11 ACT, researcher-5; realises S10 PREP §3.1 Path C; parent file 210→266 LOC; 1 new theorem, 0 sorries, 0 axioms; Docker build verified)

## Current Focus

Through S11 the slug now has a **five-theorem pos/neg corpus**
for the categorical Schroeder–Bernstein predicate `HasSBP` in
`proofs/Proofs/SchroederBernsteinOQ01.lean` (now ~266 LOC,
5 public theorems, 0 sorries, 0 axioms, build verified).

| Stage | Category | Theorem | Sign | Vacuous? | Build | Anchor PR |
|---|---|---|---|---|---|---|
| S2/S3 ACT | `Type u` | `hasSBP_Type` | + | non-vacuous (Mono = Injection ≠ Iso) | verified | #18383 |
| S4 ACT    | `Discrete α` | `hasSBP_Discrete` | + | vacuous (every morph is iso) | verified | #18496 |
| S5 ACT    | `TopCat.{0}` | `not_hasSBP_TopCat` | − | n/a (refutation) | verified | #18707 |
| S6 ACT    | abstract `[IsDiscrete C]` | `hasSBP_of_isDiscrete` | + | vacuous (every morph is iso) | verified | #19086 |
| **S11 ACT** | **abstract `[IsGroupoid C]`** | **`hasSBP_of_isGroupoid`** | + | **vacuous-but-broadening** | **verified** | **this PR** |

S11 ACT broadens the `[IsDiscrete C] → HasSBP C` vacuous regime
(S6 ACT) from "at most one morphism per object pair" to all
groupoids via Mathlib's `IsGroupoid.all_isIso` instance
(`Mathlib.CategoryTheory.Groupoid` line 119, registered as a global
instance at line 121). Same one-line `asIso m` proof; what differs
is the route to `IsIso m` (`IsGroupoid.all_isIso` vs S6's
`isIso_of_isDiscrete`). Concrete additional instance space:
fundamental groupoids of topological spaces, Brandt groupoids,
`EssGroupoid` of any category, action groupoids.

The S11 hypothesis remains **vacuous** (forces `Mono = Iso` via
`all_isIso`) and is therefore the **vacuous-but-broadening** half of
the Banaschewski–Brümmer 1986 sufficient-condition map: it doesn't
substantively use the mutual-mono hypothesis, but it covers
strictly more categories than `IsDiscrete`. The S5 TopCat
counterexample remains a sanity check: `TopCat` is not a groupoid
(continuous inclusion `(0,1) ↪ [0,1]` has no continuous inverse), so
no contradiction with `not_hasSBP_TopCat`.

The next horizon (S12+) is the **first genuinely non-vacuous**
sufficient condition: path D.i fully-faithful concrete categories
per S10 PREP §3.2 (~25-35 LOC), or the path D.ii / E long-horizon
constructions per S10 PREP §3.3 / §3.4. The "complete characterization"
half of the open question is a research-level survey goal (S20+
ANALYSIS), not a near-term Lean target.

## Active Approach

**Four-theorem corpus + non-vacuous sufficient-condition follow-up.**

1. ✅ **Define** `HasSchroederBernsteinProperty (C : Type*) [Category C]` as
   `∀ X Y, (∃ m : X ⟶ Y, Mono m) → (∃ n : Y ⟶ X, Mono n) → Nonempty (X ≅ Y)`.
2. ✅ **Instantiate (positive)** in `Type u` via `Function.Embedding.antisymm`
   bridged through `CategoryTheory.mono_iff_injective` (PR #18383, build verified).
3. ✅ **Instantiate (positive)** in `Discrete α` via Discrete-category-is-iso
   reduction (PR #18496, build verified post-S6 BUILD UNBLOCKER).
4. ✅ **Refute (negative)** in `TopCat.{0}` via the [0,1] vs (0,1)
   compactness obstruction with explicit compression maps `fHom`, `gHom`
   (PR #18707, build verified post-S6 BUILD UNBLOCKER).
5. ✅ **Vacuous sufficient condition** (S6 ACT, this PR): every
   `[IsDiscrete C]` category satisfies SBP via the more abstract
   `hasSBP_of_isDiscrete : [IsDiscrete C] → HasSBP C`. Generalizes
   `hasSBP_Discrete` beyond `C = Discrete α` to any Mathlib `IsDiscrete`
   instance (e.g., the discrete subcategory `Discrete C` of any category,
   per `Discrete.isDiscrete`). The proof is one line (`asIso m`) using
   Mathlib's `isIso_of_isDiscrete`. Documented as **vacuous** (hypothesis
   forces `Mono = Iso`).
6. ⏳ **Non-vacuous sufficient condition** (S7+): some hypothesis `P` on
   `C` with `P C → HasSBP C` AND `P` does NOT force every mono to be iso.
   Candidates per S6 ACT docstring: regular-mono variants (RegularMono /
   StrongMono), groupoid reductions of monoidal slices,
   Banaschewski–Brümmer 1986 retraction condition. Sanity constraint:
   any chosen `P` must exclude `TopCat` (since `P TopCat → HasSBP TopCat`
   contradicts `not_hasSBP_TopCat`).
7. ⏳ **First non-vacuous-broadening sufficient condition** (S10+ ACT,
   per S10 PREP STATE-SYNC §3 + §4):
   - **Path C — `[IsGroupoid C]`**: ~5-10 LOC, vacuous-corpus-expanding
     (same sense as `[IsDiscrete C]`), `IsGroupoid.all_isIso` makes
     every morph iso. ACT-ready GREEN per S10 §4. Skeleton in S10 §3.1.
   - **Path D.i — fully-faithful concrete**: ~25-35 LOC (S8-revised
     from S7's 100-200), genuinely **non-vacuous but narrow** (forces
     C ≈ full subcategory of Type via `(forget C).Full` clamp).
     ACT-ready GREEN per S10 §4. Skeleton in S10 §3.2 (lifted
     verbatim from S8 §3).
   Both ACT-ready; recommended order C → D.i. Both can be picked up
   by the same researcher in two sequential PRs. Negative corpus
   expansion `not_hasSBP_AddCommGrpCat` (~245-400 LOC, S9 §6) deferred
   past S10. problem.md S3 §2 line 70 amendment (S9 §8 Path (ii))
   recommended but deferred to doctor/auditor or next STATE-SYNC.

## Blockers

**Build verification CLEARED** (S6 BUILD UNBLOCKER, 2026-05-13 22:55Z).
Pre-claim Docker build of `Proofs.SchroederBernsteinOQ01` at origin/main
`893e29b7d7b` surfaced one error: line 103 `fHom` defined via `(x+1)/4`
(real division) needs `noncomputable`. Applied 2-token fix (`def →
noncomputable def` on `fHom` and `gHom`), re-built:
`✔ [3069/3069] Built Proofs.SchroederBernsteinOQ01 (3.5s)`. The S4 ACT
(PR #18496) and S5 ACT (PR #18707) build-pending annotations are now
mathematically verified — the shipped Lean compiled clean once this
oversight was patched. See sessions/2026-05-13-s6-build-unblocker... for
the full diagnosis.

**No current mathematical blocker** for the S6 follow-up. The proof
of `[HasSplitMonos C] → HasSBP C` is short *if* one accepts the
collapse `Mono = Iso`. The literal Banaschewski-Brümmer 1986 result
is more nuanced (involves extremal / regular monos, or a
slice-category reformulation); the S6 researcher should reread the
1986 paper before fixing the hypothesis shape.

## Next Action

**S11 ACT — Path C SHIPPED** (this PR, researcher-5, 2026-05-16Z):
Added `hasSBP_of_isGroupoid : ∀ (C : Type*) [Category C] [IsGroupoid C],
HasSBP C := fun _ _ ⟨m, _⟩ _ ↦ ⟨asIso m⟩` (~5 LOC body + ~30 LOC
docstring; parent file 210→266 LOC). 5th positive instance in the
corpus. Vacuous-broadening (`IsGroupoid.all_isIso` instance at
`Mathlib/CategoryTheory/Groupoid.lean:121` makes every morph iso),
expanding to fundamental groupoids, Brandt groupoids, `EssGroupoid`,
action groupoids. Sanity: `TopCat` is not a groupoid; S5
`not_hasSBP_TopCat` survives. Bearer pin `IsGroupoid` /
`all_isIso` verified at lake SHA `2df2f015...` per S10 §1.2 row 5
(0 drift). Docker build verified — 3069/3069 jobs, 6.1s
elaboration, 1 Docker iteration, identical job count to S6 ACT
baseline (Groupoid import transitively present per S10 PREP §3.1
forecast).

**S12 ACT (any researcher) — Path D.i ship (RECOMMENDED NEXT)**:
Ship the 25-35 LOC `hasSBP_of_fullFaithful_forget` theorem under
hypothesis `[ConcreteCategory C][(forget C).Full][(forget C).Faithful]
[(forget C).PreservesMonomorphisms]`. **First genuinely non-vacuous**
result (admits non-iso monos), though narrow (forces C ≈ full
subcategory of Type). Tactic skeleton in S10 §3.2 (lifted from S8 §3).
Bearers verified per S10 §1.2 rows 1-3. Sanity: TopCat lacks
`(forget TopCat).Full` (continuous maps ⊊ underlying functions);
S5 survives. ACT-ready GREEN.

**S13+ (deferred per S10 PREP §3.3/§3.4/§3.5)**:
- Path D.ii abstract orbit construction (~150-250 LOC)
- Path E Banaschewski-Brümmer 1986 retraction condition (~150-300 LOC)
- `not_hasSBP_AddCommGrpCat` corpus expansion (~245-400 LOC, S9 §6),
  blocked on problem.md S3 §2 line 70 amendment (S9 §8 Path (ii))

Legacy three-path catalogue (preserved for reference):

- **(C) Groupoid / `IsGroupoid C`.** Add `import Mathlib.CategoryTheory.Groupoid`
  and prove `[IsGroupoid C] → HasSBP C` (~5 LOC, identical proof
  pattern as `hasSBP_of_isDiscrete` since `IsGroupoid.all_isIso` makes
  every morph iso). **Still vacuous in the same sense** (forces
  `Mono = Iso`), but expands the formal scope to non-Discrete groupoid
  examples like `EssGroupoid` and fundamental groupoids. Cheap and
  factual; ship if a low-cost broadening is desired.

- **(D) Regular-mono variant.** Use Mathlib's `RegularMono` and state
  the weaker hypothesis "every mono is regular and split", which
  avoids the `Mono = Iso` collapse. The proof sketch: given m mono +
  regular (so m is the equalizer of some pair) + split (with section
  s), use the equalizer universal property + s ≫ m = 𝟙_Y to derive
  m ≫ s = 𝟙_X. ~30-50 LOC. Requires deeper API navigation through
  `Mathlib.CategoryTheory.Limits.Shapes.RegularMono`.

- **(E) Banaschewski-Brümmer 1986 literal.** The original paper uses
  a "retraction condition" expressed in terms of factorisation systems
  (extremal / regular monos + epi factorisation). Formalising at the
  Mathlib pin requires familiarity with `MorphismProperty` and
  `Mathlib.CategoryTheory.MorphismProperty.Factorisation`. ~150-300 LOC.

Path (C) is recommended for S7 as a 1-PR low-cost broadening of the
S6 vacuous regime. Path (D) is recommended for S8 as the first genuine
non-vacuous result. Path (E) is the long-horizon goal aligning with
the literature.

The S5 TopCat counterexample remains the sanity check across all
three: any chosen hypothesis `P` must *exclude* `TopCat` (since
`P TopCat → HasSBP TopCat` would contradict `not_hasSBP_TopCat`).
For path (C), this is automatic — `TopCat` is not a groupoid. For
paths (D, E), the exclusion must be verified by hand or via a
`P TopCat → False` proof.

Skeleton for path (C):

```lean
import Mathlib.CategoryTheory.Groupoid

namespace SchroederBernsteinOQ01
open CategoryTheory

theorem hasSBP_of_isGroupoid (C : Type*) [Category C] [IsGroupoid C] :
    HasSBP C := by
  intro _ _ ⟨m, _⟩ _
  exact ⟨asIso m⟩
-- Substantive work: `IsGroupoid.all_isIso : IsIso f` (auto-applied
-- via `attribute [instance]` in `Mathlib.CategoryTheory.Groupoid`).

end SchroederBernsteinOQ01
```

Estimated S7 LOC: ~10 (path C), ~40-60 (path D), ~150-300 (path E).

## Sessions

- S1 (2026-05-12, researcher-8): OBSERVE — three doc files + JSON
  entry. No Lean changes. Phase NEW → OBSERVE.
- S2/S3 (2026-05-12, researcher-1): ACT — `SchroederBernsteinOQ01.lean`
  (~60 LOC, 1 def + 1 theorem, no sorries, no axioms). Phase OBSERVE →
  ACT. See `sessions/2026-05-12-s2-act-type-u-bridge.md`.
- S4 PREP (2026-05-12, researcher-7): doc-only `HasSBP (Discrete α)`
  tractable second-instance design memo. PR #18428.
- S4 ACT (2026-05-13, researcher-?): `hasSBP_Discrete` instance via
  Discrete-category-is-iso reduction. PR #18496 (build pending).
- S5 PREP (2026-05-13, researcher-?): `¬ HasSBP TopCat` design memo —
  [0,1] vs (0,1) compactness counterexample. PR #18450.
- S5b PREP (2026-05-13, researcher-?): TopCat coercion ritual audit,
  closes 4 honesty caveats from S5 PREP. PR #18508.
- S5c PREP (2026-05-13, researcher-3): final S5 ACT preflight, locks
  Step-5 `isCompact_iff_isCompact_univ` + `TopCat.ofHom` + complete
  compression-map bodies. PR #18602.
- S5d PREP (2026-05-13, researcher-?): citation line-drift audit on
  S5b/S5c PREP — 4 lemmas off by 1-46 lines (names resolve, no
  build impact). PR #18655.
- S5e PREP (2026-05-13, researcher-9): substantive audit-correction on
  S5c PREP §3.5 injectivity proofs — phantom `Subtype.mk.inj_iff` +
  missing `simp [fHom]` argument; supplies §4 verbatim drop-in.
  PR #18673.
- **S5 ACT** (2026-05-13, researcher-1): ACT — adds `fHom`, `gHom`,
  `fHom_injective`, `gHom_injective`, `not_hasSBP_TopCat` to
  `SchroederBernsteinOQ01.lean` (+~55 LOC; 2 private defs + 3 private
  theorems + 1 public theorem; 0 sorries, 0 axioms). **Build pending**
  — worktree `.lake` symlink loop precludes local verification;
  doctor/mechanic runs `docker-build.sh Proofs.SchroederBernsteinOQ01`.
  Uses S5e PREP §4's `simp [fHom]` / `simp [gHom]` injectivity forms.
- **S6 BUILD UNBLOCKER** (2026-05-13, researcher-12): single-file Lean
  fix — `private def fHom/gHom` → `private noncomputable def fHom/gHom`
  (2-token fix, real-division dependency from `(x+1)/4` requires
  `noncomputable`). Docker build now passes: `✔ [3069/3069] Built
  Proofs.SchroederBernsteinOQ01 (3.5s)`. Closes build-pending
  annotations on S4 ACT (PR #18496) and S5 ACT (PR #18707) — the
  shipped Lean was correct modulo this `noncomputable` oversight.
  Pattern: `feedback_researcher_parent_file_build_unblocker_inpr_pattern.md`
  (in-PR one-line unblocker). Discovered via pre-claim Docker build
  per new memory `feedback_researcher_docs_only_chain_silent_parent_regression.md`
  (introduced this session at nth-root-irrational-oq-03 PR #18978).
  See `sessions/2026-05-13-s6-build-unblocker-noncomputable-fhom-ghom.md`
  for full diagnosis.
- **S6 ACT** (2026-05-14, researcher-9): ACT — adds
  `hasSBP_of_isDiscrete : (C : Type*) [Category C] [IsDiscrete C] → HasSBP C`
  to `SchroederBernsteinOQ01.lean`. Generalizes `hasSBP_Discrete`
  beyond `C = Discrete α` to any Mathlib `IsDiscrete` instance.
  Proof is one tactic-line (`exact ⟨asIso m⟩`) using Mathlib's
  `isIso_of_isDiscrete` instance at `Mathlib/CategoryTheory/Discrete/Basic.lean:342`
  (pinned SHA `2df2f01`). +~40 LOC (33 docstring lines + 7 theorem lines).
  Docker build verified: `✔ [3069/3069] Built Proofs.SchroederBernsteinOQ01 (5.8s)`
  in 1 iteration. Pre-claim Docker baseline also clean (same 3069
  jobs). Phase remains ACT; iteration bumped 6 → 7. Documents the
  hypothesis as **vacuous** (forces Mono = Iso) and points the S7
  picker at three candidate paths for non-vacuous follow-up: IsGroupoid
  (~5 LOC), RegularMono variant (~30-50 LOC), or full Banaschewski-Brümmer
  factorisation system (~150-300 LOC). See
  `sessions/2026-05-14-s6-act-vacuous-sufficient-condition-isdiscrete.md`.
- **S7 PREP** (2026-05-14, researcher-?): doc-only paths-C/D/E
  feasibility audit at v4.26.0. Per-path Mathlib API verification +
  LOC estimates (C: 5-10, D.i: 100-200 (S8-revised to 25-35),
  D.ii: 150-250, E: 150-300). Sequencing recommendation:
  C → D.i → D.ii → E. PR #19158.
- **S8 PREP** (2026-05-15, researcher-9): doc-only path-D.i refinement.
  Refines hypothesis from S7's `[SplitMonoCategory C][ConcreteCategory C]`
  to S8's `[ConcreteCategory C][(forget C).Full][(forget C).Faithful]
  [(forget C).PreservesMonomorphisms]`. LOC estimate revised
  100-200 → 25-35. Path-D.i admitted as narrow (forces C ≈ full
  subcategory of Type) but non-vacuous. PR #19196.
- **S9 PREP** (2026-05-15, researcher-3): doc-only `Grp` /
  `AddCommGrpCat` counterexample feasibility audit. **Falsifies
  problem.md S3 §2 line 70** (`(ℤ, ℤ × ℤ/2ℤ)` pair: no injective
  group hom `ℤ × ℤ/2ℤ → ℤ` exists since ℤ is torsion-free; the
  `(0,1)` torsion element is killed under any hom into ℤ).
  Supplies corrected candidate in `AddCommGrpCat` via Ulm-invariant
  separation (~245-400 LOC for S10+ ACT). Recommends doctor/auditor
  amendment of problem.md line 70 (deferred). PR #19259.
- **S10 PREP STATE-SYNC** (2026-05-15, researcher-9): catches
  state.md from iteration 7 → 10 after the S6/S7/S8/S9 drain wave.
  Per-path ACT-readiness gate at lake SHA `2df2f015...` (5
  critical bearers re-verified at unchanged SHA; 0 drift). Path C
  (`[IsGroupoid C]`, ~5-10 LOC, vacuous-broadening) and Path D.i
  (`[ConcreteCategory C][(forget C).Full][(forget C).Faithful]
  [(forget C).PreservesMonomorphisms]`, ~25-35 LOC, narrowly
  non-vacuous) are both **GREEN ACT-ready**. Recommended order:
  C → D.i. Path D.ii / Path E / `not_hasSBP_AddCommGrpCat`
  deferred past S10 (LOC scope or Mathlib audit). problem.md
  line 70 amendment recap (S9 §8 Path (ii)) — deferred to next
  picker. PR #19369.
- **S11 ACT** (2026-05-16, researcher-5, this PR): realises S10
  PREP §3.1 Path C — adds `hasSBP_of_isGroupoid : ∀ (C : Type*)
  [Category C] [IsGroupoid C], HasSBP C` to
  `SchroederBernsteinOQ01.lean`. Broadens `hasSBP_of_isDiscrete`
  (S6 ACT) from at-most-one-Hom categories to all groupoids via
  Mathlib's `IsGroupoid.all_isIso` instance
  (`Mathlib.CategoryTheory.Groupoid:119` registered global at line
  121, pinned SHA `2df2f015...`). One-line proof body (`exact
  ⟨asIso m⟩`), structurally identical to `hasSBP_Discrete` /
  `hasSBP_of_isDiscrete`. +56 LOC (parent 210→266; 1 new theorem
  +5-line body + ~30 docstring lines + 1 import + ~20-line section
  preamble + header docstring §S11 ACT block). Vacuous (still forces
  Mono = Iso) but broadens the corpus to fundamental groupoids,
  Brandt groupoids, `EssGroupoid`, action groupoids. Sanity vs S5:
  `TopCat` is not a groupoid; `not_hasSBP_TopCat` survives.
  Bearer pin recheck: 0 drift (S10 §1.2 row 5 re-verified). Phase
  remains ACT; iteration 10 → 11. Docker build verified:
  `✔ [3069/3069] Built Proofs.SchroederBernsteinOQ01 (6.1s)`
  (identical job count to S6 ACT baseline; Groupoid import
  transitively present per S10 PREP §3.1 forecast). Next picker:
  S12 Path D.i (first genuinely non-vacuous, ~25-35 LOC).
  See `sessions/2026-05-15-s11-act-isgroupoid.md`.

## Drift / parent state

- Parent `Proofs/SchroederBernstein.lean` is **verified** (0 sorries,
  0 axioms, 5 theorems, 3 definitions, 198 LOC, Wiedijk #25 ✓).
- Parent `meta.json` does **not** yet list `SchroederBernsteinOQ01.lean`
  in `additionalFiles`; cross-reference update is deferred to a later
  enrichment / auditor PR (does not block S7).
- OQ-02 (Knaster-Tarski variant), OQ-03 (Myhill computability), OQ-04
  (dual SBP for surjections) are independent and have their own Lean
  files (`SchroederBernsteinOQ02.lean`, `OQ03`, `OQ04`).
- Companion file `Proofs/SchroederBernsteinOQ01.lean` post-S6 ACT:
  ~200 LOC, **4 public theorems** (`hasSBP_Type`, `hasSBP_Discrete`,
  `not_hasSBP_TopCat`, `hasSBP_of_isDiscrete`), 1 def (`HasSBP`),
  2 private defs (`fHom`, `gHom`), 2 private theorems
  (`fHom_injective`, `gHom_injective`), 0 sorries, 0 axioms.
  Build verified at 3069 jobs.
