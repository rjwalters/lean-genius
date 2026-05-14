# Current State

**Phase**: ACT
**Since**: 2026-05-14 (S6 ACT vacuous sufficient condition `[IsDiscrete C] → HasSBP C`, researcher-9)
**Iteration**: 7
**Last Updated**: 2026-05-14T15:50:00Z (S6 ACT, researcher-9)

## Current Focus

Through S6 the slug has accumulated a **four-theorem pos/neg corpus**
for the categorical Schroeder–Bernstein predicate `HasSBP` in
`proofs/Proofs/SchroederBernsteinOQ01.lean` (now ~200 LOC,
4 public theorems, 0 sorries, 0 axioms, build verified).

| Stage | Category | Theorem | Sign | Vacuous? | Build | Anchor PR |
|---|---|---|---|---|---|---|
| S2/S3 ACT | `Type u` | `hasSBP_Type` | + | non-vacuous (Mono = Injection ≠ Iso) | verified | #18383 |
| S4 ACT    | `Discrete α` | `hasSBP_Discrete` | + | vacuous (every morph is iso) | verified | #18496 |
| S5 ACT    | `TopCat.{0}` | `not_hasSBP_TopCat` | − | n/a (refutation) | verified | #18707 |
| **S6 ACT** | **abstract `[IsDiscrete C]`** | **`hasSBP_of_isDiscrete`** | + | **vacuous (every morph is iso)** | **verified** | **this PR** |

S6 ACT generalizes `hasSBP_Discrete`'s proof pattern beyond
`C = Discrete α` to all categories `C` with Mathlib's
`[IsDiscrete C]` typeclass (at most one morphism between objects,
morphisms force `X = Y`). The substantive work is in Mathlib's
`isIso_of_isDiscrete` instance (`Discrete/Basic.lean:342`); the
categorical SBP reduction is one line (`asIso m`).

The S6 hypothesis is **the vacuous half of the Banaschewski–Brümmer
1986 sufficient-condition map**: it forces `Mono = Iso` and so doesn't
substantively use the mutual-mono hypothesis. The S5 TopCat
counterexample remains a sanity check: any non-vacuous hypothesis
*must exclude TopCat* (since `P TopCat → HasSBP TopCat` contradicts
`not_hasSBP_TopCat`).

The next horizon (S7+) is a **non-vacuous** sufficient condition:
Banaschewski–Brümmer 1986 "retraction condition", regular-mono
variants, or groupoid reductions. The "complete characterization"
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

**S7 (any researcher)**: State and prove a **non-vacuous** sufficient
condition for `HasSBP C`. The S6 ACT shipped the vacuous case
(`[IsDiscrete C] → HasSBP C`); the open work is a hypothesis that
allows monos that are not iso but still forces SBP.

Three candidate paths, ordered by ascending Mathlib-API ambition:

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
