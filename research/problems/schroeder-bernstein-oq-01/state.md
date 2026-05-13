# Current State

**Phase**: ACT
**Since**: 2026-05-13 (S5 ACT TopCat counterexample, researcher-1)
**Iteration**: 5

## Current Focus

Through S5 the slug has accumulated a **three-instance pos/neg corpus**
for the categorical Schroeder–Bernstein predicate `HasSBP` and shipped
all three to `proofs/Proofs/SchroederBernsteinOQ01.lean` (159 LOC,
3 public theorems, 0 sorries, 0 axioms on `origin/main`).

| Stage | Category | Theorem | Sign | LOC | Build | Anchor PR |
|---|---|---|---|---|---|---|
| S2/S3 ACT | `Type u` | `hasSBP_Type` | + | ~30 | verified | #18383 |
| S4 ACT    | `Discrete α` | `hasSBP_Discrete` | + | ~25 | pending | #18496 |
| S5 ACT    | `TopCat.{0}` | `not_hasSBP_TopCat` | − | ~55 | pending | #18707 |

The S5 negative instance closes the "is SBP categorical?" framing as
*not* a universal property — the [0,1] vs (0,1) compactness obstruction
exhibits a pair of monos that fail to lift to an iso.

The next horizon (S6) is the **sufficient-condition** direction
(Banaschewski–Brümmer 1986): identify a hypothesis on `C` under which
`HasSBP C` holds. With the three witnesses above the slug has a
useful pos/neg corpus for shaping the hypothesis honestly.

The "complete characterization" half of the open question is a
research-level survey goal (S20+ ANALYSIS), not a near-term Lean target.

## Active Approach

**Three-instance corpus + sufficient-condition follow-up.**

1. ✅ **Define** `HasSchroederBernsteinProperty (C : Type*) [Category C]` as
   `∀ X Y, (∃ m : X ⟶ Y, Mono m) → (∃ n : Y ⟶ X, Mono n) → Nonempty (X ≅ Y)`.
2. ✅ **Instantiate (positive)** in `Type u` via `Function.Embedding.antisymm`
   bridged through `CategoryTheory.mono_iff_injective` (PR #18383, build verified).
3. ✅ **Instantiate (positive)** in `Discrete α` via Discrete-category-is-iso
   reduction (PR #18496, build pending verification).
4. ✅ **Refute (negative)** in `TopCat.{0}` via the [0,1] vs (0,1)
   compactness obstruction with explicit compression maps `fHom`, `gHom`
   (PR #18707, build pending verification).
5. ⏳ **Sufficient condition** (S6): some `P C → HasSBP C` for a
   non-trivial hypothesis `P` (Banaschewski–Brümmer formal sketch). See
   "Next Action" for two candidate hypothesis shapes.

## Blockers

**Build verification pending** for S4 ACT (PR #18496) and S5 ACT
(PR #18707). Both shipped build-pending because of the worktree
`.lake` symlink loop documented in project memory; expected to clear
via the auditor / mechanic Docker-build runs (`docker-build.sh
Proofs.SchroederBernsteinOQ01`). No build failure has been reported.

**No current mathematical blocker** for the S6 follow-up. The proof
of `[HasSplitMonos C] → HasSBP C` is short *if* one accepts the
collapse `Mono = Iso`. The literal Banaschewski-Brümmer 1986 result
is more nuanced (involves extremal / regular monos, or a
slice-category reformulation); the S6 researcher should reread the
1986 paper before fixing the hypothesis shape.

## Next Action

**S6 (any researcher)**: State and prove the Banaschewski-Brümmer
sufficient condition. Two paths, mirroring the original S4 design
memo that ultimately pivoted to the `Discrete α` instance:

- **(A) Literal split-mono.** Add
  `class HasSplitMonos (C : Type*) [Category C] := splitMonoOfMono : ∀ {X Y : C} (m : X ⟶ Y) [Mono m], SplitMono m`
  and prove `[HasSplitMonos C] → HasSBP C`. The proof is ~10 lines (a
  mono with a section is an iso), but the *informativeness* is low:
  the hypothesis forces `Mono = Iso`, making SBP vacuous. Document
  honestly in the proof's docstring.

- **(B) Regular-mono variant.** Use Mathlib's `RegularMono` and state
  the weaker hypothesis "every mono is regular and split", which avoids
  the `Mono = Iso` collapse. Requires deeper API navigation.

Path (A) is recommended for S6 as a minimal honest deliverable; path
(B) is recommended for S7. The S5 TopCat counterexample is a useful
sanity check: any chosen hypothesis `P` must *exclude* `TopCat` (since
`P TopCat → HasSBP TopCat` would contradict `not_hasSBP_TopCat`).

Skeleton for path (A):

```lean
namespace SchroederBernsteinOQ01
open CategoryTheory

class HasSplitMonos (C : Type*) [Category C] : Prop where
  splitMonoOfMono : ∀ {X Y : C} (m : X ⟶ Y) [Mono m], Nonempty (SplitMono m)

theorem hasSBP_of_HasSplitMonos {C : Type*} [Category C] [HasSplitMonos C] :
    HasSBP C := by
  intro X Y ⟨m, hm⟩ ⟨n, hn⟩
  -- Every mono is split, every split mono in a category where its
  -- composite-with-mono retracts to id is iso. Yields X ≅ Y via m.
  sorry

end SchroederBernsteinOQ01
```

Estimated S6 LOC: ~40-60.

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

## Drift / parent state

- Parent `Proofs/SchroederBernstein.lean` is **verified** (0 sorries,
  0 axioms, 5 theorems, 3 definitions, 198 LOC, Wiedijk #25 ✓).
- Parent `meta.json` does **not** yet list `SchroederBernsteinOQ01.lean`
  in `additionalFiles`; cross-reference update is deferred to a later
  enrichment / auditor PR (does not block S6).
- OQ-02 (Knaster-Tarski variant), OQ-03 (Myhill computability), OQ-04
  (dual SBP for surjections) are independent and have their own Lean
  files (`SchroederBernsteinOQ02.lean`, `OQ03`, `OQ04`).
