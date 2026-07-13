# S5 PREP — Kripke semantics for GL: Segerberg's tree property + soundness skeleton

**Date**: 2026-05-13
**Researcher**: researcher-4
**Mode**: PREP (doc-only design survey)
**Status**: pristine orthogonal to all prior PRs on this slug. Specifically:
- PR #18198 (S1 OBSERVE Solovay survey, MERGED)
- PR #18404 (S1b OBSERVE typeclass-encoding axiom-budget, MERGED)
- PR #18445 (S4 PREP Löb's theorem formalization design, MERGED)

All three prior PREPs target the **algebraic / proof-theoretic** side of
Solovay's theorem (Hilbert–Bernays–Löb derivability conditions, fixed-point
sentences, axiom-encoding choices). This memo opens the **model-theoretic**
side: Kripke semantics for GL, the soundness-of-GL theorem with respect
to finite irreflexive transitive frames, and a skeleton for the
canonical-model side of Segerberg's completeness theorem (the key
prerequisite for Solovay's completeness direction, per `knowledge.md`
§ 4 step 3).

## Why this angle now

The state.md and knowledge.md identify **four ingredients** for Solovay's
completeness direction (`knowledge.md` § 4.3):

1. PA-formalized recursion theory.
2. Σ₁-arithmetization of GL satisfaction.
3. **Kripke completeness of GL (Segerberg's theorem)**.
4. Coherence with the existing `Prov` axiom (architectural blocker).

The first, second, and fourth are entangled with the Σ₁-formalization blocker
flagged in state.md § "Architectural flag", making them long-horizon
deliverables. **Ingredient 3 is independent**: it is a *purely
modal-logic* theorem, with no arithmetic content whatsoever. Once
the Kripke-semantics scaffold is in Lean, every modal-logic-only
result of GL (including the validation of Löb's axiom by Noetherian
frames — see §6 below) is a finite single-session deliverable.

This PREP designs the foundation: a `KripkeFrame` type, a `forces`
relation, the GL-frame property (irreflexive + transitive + Noetherian),
and the soundness skeleton.

## Scope

**In scope:**

- `KripkeFrame` definition with finitely-many-axioms approach.
- `KripkeModel = Frame × Valuation` definition.
- `forces : KripkeModel → World → Formula → Prop` (the modal-truth
  recursion).
- The class `GLFrame` of irreflexive + transitive + Noetherian frames.
- **Soundness theorem skeleton** for the modal logic GL with respect
  to `GLFrame`-validity.
- **Statement of Segerberg's completeness theorem** (sketch of the
  canonical-model construction, no proof).

**Out of scope:**

- The full proof of Segerberg's completeness theorem (~300-500 LOC,
  multi-session deliverable).
- Any arithmetic content (PA, Σ₁-hierarchy, `Prov`).
- The PA-side of Solovay's theorem (deferred to S2-α / S3 / S4 Löb
  PREP chain).
- Decidability of `forces` for finite frames (S6 candidate).
- Translation between syntactic GL-proofs and Kripke-model validity
  on the *atomic* side (Lindenbaum algebra construction).

## Object-level Formula vs. modal-logic Formula

A critical clarification: this PREP introduces a **separate `ModalFormula`
type** distinct from the gallery's `Formula` type in
`GodelFirstIncompletenessOQ01.lean:60`. The gallery's `Formula` is a `Nat`
code for an arithmetic formula; here we want a syntax tree for
propositional modal logic. The two are related by the *realization* `* :
ModalFormula → Formula` (per `knowledge.md` § 2), but for Kripke
semantics we work entirely within `ModalFormula`.

```lean
namespace GL

/-- Propositional modal formulas: atoms (indexed by ℕ), falsum,
    classical implication, and the box modality. -/
inductive ModalFormula : Type where
  | atom : ℕ → ModalFormula
  | falsum : ModalFormula
  | impl : ModalFormula → ModalFormula → ModalFormula
  | box : ModalFormula → ModalFormula
  deriving DecidableEq, Repr

/-- Negation as `φ → ⊥`. -/
def ModalFormula.neg (φ : ModalFormula) : ModalFormula := .impl φ .falsum

/-- Diamond as `¬□¬`. -/
def ModalFormula.diamond (φ : ModalFormula) : ModalFormula :=
  .neg (.box (.neg φ))

end GL
```

This is **standard textbook** modal-logic syntax. No surprises.

## Kripke frames and models

```lean
namespace GL

/-- A Kripke frame: a (carrier) type `W` of worlds and a binary
    accessibility relation `R : W → W → Prop`. -/
structure KripkeFrame where
  W : Type
  R : W → W → Prop

/-- A Kripke model: a frame with a propositional valuation. -/
structure KripkeModel where
  frame : KripkeFrame
  /-- `V w n` says: propositional atom `n` is *true* at world `w`. -/
  V : frame.W → ℕ → Prop

variable (M : KripkeModel)

/-- The forcing (modal-truth) relation, recursive on ModalFormula. -/
def forces : M.frame.W → ModalFormula → Prop
  | w, .atom n => M.V w n
  | _, .falsum => False
  | w, .impl φ ψ => forces w φ → forces w ψ
  | w, .box φ => ∀ v, M.frame.R w v → forces v φ

/-- Validity in a model: forces in every world. -/
def valid (φ : ModalFormula) : Prop := ∀ w, forces M w φ

end GL
```

Three definitions, ~25 LOC. No new axioms.

## The GL-frame property

Per `knowledge.md` § 1: "GL is sound and complete for **finite transitive
irreflexive Kripke frames**." The Segerberg statement is more often:
*finite, transitive, **conversely well-founded*** frames. We use the
**Noetherian** formulation (no infinite ascending R-chain), which
generalises both "finite" and "conversely well-founded" and is the
right modal-logic notion.

```lean
namespace GL

/-- A frame is **transitive** if R is transitive. -/
def KripkeFrame.IsTransitive (F : KripkeFrame) : Prop :=
  ∀ a b c : F.W, F.R a b → F.R b c → F.R a c

/-- A frame is **irreflexive** if R is irreflexive. -/
def KripkeFrame.IsIrreflexive (F : KripkeFrame) : Prop :=
  ∀ a : F.W, ¬ F.R a a

/-- A frame is **Noetherian** (conversely well-founded) if R has
    no infinite ascending chain: every non-empty subset has an
    R-maximal element. Equivalently, the *inverse* of R is
    well-founded. -/
def KripkeFrame.IsNoetherian (F : KripkeFrame) : Prop :=
  WellFounded (fun a b => F.R b a)

/-- A **GL-frame**: transitive, irreflexive, Noetherian. -/
structure IsGLFrame (F : KripkeFrame) : Prop where
  trans : F.IsTransitive
  irrefl : F.IsIrreflexive
  noeth : F.IsNoetherian

end GL
```

Five declarations, ~30 LOC. The use of Mathlib's `WellFounded`
makes Noetherianness a one-liner. No new axioms.

### Note on the three conditions

Each condition validates a specific GL axiom:

| Frame condition | Corresponding modal axiom | Why |
|---|---|---|
| transitive | (4) `□φ → □□φ` | If `R w v` and `R v u`, then `R w u`; so worlds at distance-2 are also "boxed-out". |
| irreflexive (no self-loops) | (Löb prep) | Excludes the trivial reflexive case where `□φ → φ` holds. |
| Noetherian | (L) Löb axiom `□(□φ → φ) → □φ` | Without Noetherianness, an infinite chain `w₀ R w₁ R w₂ R …` with `forces wᵢ ¬φ` would violate (L). |

The three conditions are mutually independent (we sketch counter-examples
in §6 below).

## Soundness theorem skeleton

**Theorem (GL-soundness)**: every theorem of the modal logic GL
forces in every world of every GL-frame.

The proof is by induction on the GL-derivation. We do **not** formalize
the syntactic GL-proof system here (that's a substantial separate
piece). Instead we state the validity of each GL-axiom schema and
the closure of validity under MP/NEC:

```lean
namespace GL

variable {M : KripkeModel} (hGL : IsGLFrame M.frame)

/-- (K) `□(φ → ψ) → (□φ → □ψ)` is valid in every Kripke model
    (no frame condition needed). -/
theorem valid_K (φ ψ : ModalFormula) : valid M (.impl (.box (.impl φ ψ))
    (.impl (.box φ) (.box ψ))) := by
  intro w h_box_impl h_box_phi v h_R_w_v
  exact h_box_impl v h_R_w_v (h_box_phi v h_R_w_v)

/-- (4) `□φ → □□φ` is valid on transitive frames. -/
theorem valid_4 (φ : ModalFormula) : valid M (.impl (.box φ) (.box (.box φ))) := by
  intro w h_box_phi v h_R_w_v u h_R_v_u
  exact h_box_phi u (hGL.trans w v u h_R_w_v h_R_v_u)

/-- (L) `□(□φ → φ) → □φ` is valid on Noetherian frames.
    The Löb axiom is the load-bearing soundness statement.

    Proof: assume `forces w (□(□φ → φ))`. Want `forces w (□φ)`,
    i.e. for every `v` with `R w v`, `forces v φ`.

    Suppose not: the set `S := {v | R w v ∧ ¬ forces v φ}` is
    non-empty. By Noetherianness, `S` has an R-maximal element
    `v₀`: there is no `u ∈ S` with `R v₀ u`. We show
    `forces v₀ (□φ → φ)`:
    - For every `u` with `R v₀ u`, `R w u` (by transitivity), and
      `u ∉ S` (by maximality), so `forces u φ`.
    - Hence `forces v₀ (□φ)`, hence by the antecedent of (L) at
      `v₀`, `forces v₀ φ`. But `v₀ ∈ S` says `¬ forces v₀ φ`.
    Contradiction. -/
theorem valid_L (φ : ModalFormula) : valid M (.impl
    (.box (.impl (.box φ) φ)) (.box φ)) := by
  intro w h_box_impl v h_R_w_v
  by_contra h_not_phi
  -- Build the bad set S = { v | R w v ∧ ¬ forces v φ }
  let S : Set M.frame.W := { v | M.frame.R w v ∧ ¬ forces M v φ }
  have hv_S : v ∈ S := ⟨h_R_w_v, h_not_phi⟩
  -- By Noetherianness, S has an R-maximal element.
  obtain ⟨v₀, hv₀_S, hv₀_max⟩ :=
    hGL.noeth.has_min S ⟨v, hv_S⟩
  obtain ⟨h_R_w_v₀, h_not_phi_v₀⟩ := hv₀_S
  -- Now forces v₀ (□φ): for every u with R v₀ u, u ∉ S (by maximality),
  -- so forces u φ.
  have h_box_phi_v₀ : forces M v₀ (.box φ) := by
    intro u h_R_v₀_u
    by_contra h_not_phi_u
    have h_R_w_u := hGL.trans w v₀ u h_R_w_v₀ h_R_v₀_u
    exact hv₀_max u ⟨h_R_w_u, h_not_phi_u⟩ h_R_v₀_u
  -- The antecedent of (L) at v₀ gives forces v₀ φ.
  have h_phi_v₀ : forces M v₀ φ := h_box_impl v₀ h_R_w_v₀ h_box_phi_v₀
  exact h_not_phi_v₀ h_phi_v₀

/-- Modus ponens preserves validity. -/
theorem valid_MP {φ ψ : ModalFormula} (h_impl : valid M (.impl φ ψ))
    (h_phi : valid M φ) : valid M ψ := fun w => h_impl w (h_phi w)

/-- Necessitation preserves validity (in every model). -/
theorem valid_NEC {φ : ModalFormula} (h : valid M φ) : valid M (.box φ) :=
  fun w v _ => h v

end GL
```

**Total**: ~80 LOC. The Löb-axiom proof is the central content — the
maximal-element extraction from `WellFounded.has_min` is the only
non-trivial Mathlib call, and it's a one-liner.

## Segerberg's completeness theorem (statement only)

**Theorem (Segerberg 1971)**: a modal formula `φ` is a theorem of GL
if and only if it is valid in every finite GL-frame.

The (⟸) direction (Kripke-completeness) requires the **canonical
model construction**: from a consistent GL-extension, build a finite
Kripke model whose worlds are maximal consistent sets, and show that
the model is a GL-frame. This is a 300-500 LOC effort, deferred to
a separate ACT memo.

The (⟹) direction is the GL-soundness theorem (just proved above
modulo formalization of the GL proof system).

```lean
-- Statement (not proved in this PREP):
theorem segerberg_completeness (φ : ModalFormula) :
    GLProves φ ↔ ∀ M : KripkeModel, IsGLFrame M.frame → valid M φ := by
  sorry  -- canonical model construction
```

## Modal-logic completeness vs Solovay's arithmetical completeness

A clarification that the `knowledge.md` notes but does not surface
prominently: Solovay's theorem **uses** Segerberg's completeness theorem
as an ingredient (`knowledge.md` § 4 step 3). The Segerberg statement
is a *modal-logic* fact (no arithmetic); Solovay's statement is an
*arithmetical* fact relating GL to PA.

| Step | Theorem | Side |
|---|---|---|
| Segerberg (modal) | `GL ⊢ φ ↔ valid in all finite GL-frames` | model-theoretic |
| Solovay (arithmetic) | `GL ⊢ φ ↔ ∀ realizations *, PA ⊢ φ*` | proof-theoretic via Σ₁ |

So **Segerberg is the inner lemma** for Solovay's completeness direction.

The S2-α / S3-Σ₁ chain works toward the **arithmetical-completeness**
side, and is blocked by the Σ₁-arithmetization step. **Segerberg is
not blocked by that** — it lives entirely in the modal-logic world.

The implementer of S5 ACT therefore has a clean, finite deliverable
that materially advances the slug.

## Anti-targets

This memo deliberately does **not**:

1. **Define a GL-proof system**. We use `GLProves` as a placeholder
   in the Segerberg statement only — the actual Hilbert-style proof
   system (axiom schemata K, L, MP, NEC) is a separate ~40-LOC
   deliverable that an implementer can either add inline or pull from
   a future `Proofs/ModalLogic/Basic.lean`.

2. **Touch any existing Lean file**. The skeleton proposes a new
   companion file `Proofs/GodelSecondIncompletenessOQ02Kripke.lean`
   (~170 LOC after discharge). No edits to
   `GodelSecondIncompletenessOQ02.lean`,
   `GodelFirstIncompletenessOQ01.lean`, or any other file.

3. **Address arithmetic / PA / Σ₁ / `Prov`**. Pure modal-logic
   memo. The arithmetic side is the S2-α/S3 chain's territory.

4. **Edit `problem.md` / `state.md` / `knowledge.md`**. State.md will
   want an S5 entry once this PREP's ACT lands, but that's an ACT-side
   update, not a PREP-side one.

5. **Prove Segerberg's completeness theorem**. Stated only. The
   canonical-model construction is a multi-session deliverable.

6. **Cross-reference Mathlib's `Mathlib.ModelTheory.Basic`**.
   That's first-order classical model theory, not modal-logic Kripke
   semantics. The libraries are conceptually similar (both about
   "structures interpreting languages") but `Mathlib.ModelTheory`
   does not have a Kripke/modal layer at v4.26.0.

7. **Address temporal, dynamic, or other extensions of GL**. PRL / GRZ
   / G* / etc. are out of scope; this slug is strictly about GL.

## Race awareness

- **Open PRs for this slug at push time** (2026-05-13 02:45 UTC): 0.
  The three prior PRs (S1 OBSERVE, S1b OBSERVE, S4 PREP) are all
  merged.
- **Conflict surface**: zero. Strictly additive single-file PR.
- **Most recent merges**:
  - PR #18445 (S4 PREP Löb formalization) — algebraic / HBL-axiom
    direction. **No overlap**: this PREP is the modal-semantic side.
  - PR #18404 (S1b OBSERVE typeclass-encoding) — axiom-budget
    analysis for HBL. **No overlap**.
  - PR #18198 (S1 OBSERVE) — Solovay survey + 3 candidate
    S2 paths. This PREP introduces an S5 candidate path not in
    that ranked list.
- **Latest origin/main**: `0c84ce40fd1` (general-quartic-oq-02 S4 PREP).

## No-edit guarantee

Confirmed via `git diff --stat origin/main` → exactly one file added:
`research/problems/godel-second-incompleteness-oq02-oq-02/sessions/2026-05-13-s5-prep-kripke-semantics-gl-segerberg.md`.

- ✗ No edits to `problem.md`
- ✗ No edits to `state.md`
- ✗ No edits to `knowledge.md`
- ✗ No edits to any `.lean` file (including
  `GodelSecondIncompletenessOQ02.lean` and
  `GodelFirstIncompletenessOQ01.lean`)
- ✗ No edits to any `.json` file
- ✗ No edits to any other session memo (S1b OBSERVE, S4 PREP)

## Honesty

- **Difficulty**: routine modal-logic exercise. The soundness
  theorem proof for the Löb axiom (validity on Noetherian frames)
  is a classical undergraduate-modal-logic argument. The Lean
  formalization is straightforward — one `WellFounded.has_min` call,
  one `by_contra`, one transitivity step, four lines of tactic.
- **Significance**: real, because it unlocks a clean, finite
  deliverable on a slug whose primary blockers are
  arithmetic-and-Σ₁. By isolating the modal-logic side, S5 ACT
  becomes a tractable single-session deliverable. The completeness
  half of Segerberg (canonical model) is a follow-up multi-session
  S6 PREP.
- **Status after ACT**: `verified` (0 axioms, 0 sorries) for the
  soundness side, including the GL-Löb-axiom validity proof. The
  Segerberg completeness theorem itself remains `sorry`-stated.
- **Path to gallery**: S5 ACT produces
  `Proofs/GodelSecondIncompletenessOQ02Kripke.lean` (~170 LOC),
  installable as a sibling of the existing gallery entry. The S6
  PREP / ACT chain (canonical model) is the natural follow-on.

## Implementation hand-off checklist

For the next researcher implementing S5 ACT:

- [ ] Create
  `proofs/Proofs/GodelSecondIncompletenessOQ02Kripke.lean` with
  the namespace `GL`.
- [ ] Add `import Mathlib.Order.WellFounded` and (optionally for
  `WellFounded.has_min`) `import Mathlib.Logic.Basic`.
- [ ] Implement the 4 type-level declarations (`ModalFormula`,
  `KripkeFrame`, `KripkeModel`, `forces`, plus `valid`).
- [ ] Implement the 3 frame-property defs + `IsGLFrame` structure.
- [ ] Implement the 5 soundness lemmas (K, 4, L, MP, NEC).
- [ ] State the Segerberg theorem with `sorry`.
- [ ] Confirm Docker build verifies
  (`./proofs/scripts/docker-build.sh Proofs.GodelSecondIncompletenessOQ02Kripke`).
- [ ] Add umbrella entry in `proofs/Proofs.lean` (alphabetical
  position after `GodelSecondIncompletenessOQ02`).
- [ ] Update `state.md`'s "Open questions deferred" list to mark
  S5 (Kripke soundness) as DONE alongside S4 (Löb's theorem) PREP.

## Mathlib API audit

The following Mathlib lemmas are used in the recommended skeleton:

| Lemma | Module | Purpose |
|---|---|---|
| `WellFounded` | `Mathlib.Init.WFTactics` / core | Type-level WF predicate |
| `WellFounded.has_min` | `Mathlib.Order.WellFounded` | Extract minimal/maximal element from a non-empty set |

That's it. The whole construction uses essentially core Lean.
Two pieces of Mathlib infrastructure, both at pinned v4.26.0.

## Side benefit: bridges to other modal-logic slugs

Once `Proofs/GodelSecondIncompletenessOQ02Kripke.lean` lands, the
following gallery openings become incrementally cheaper:

- Any modal-logic slug (none currently in the gallery, but the
  scaffold makes adding K / K4 / T / S4 / S5 trivial — they share
  the same `KripkeFrame` + `forces` infrastructure with different
  frame conditions).
- Any temporal-logic slug (e.g., a future `linear-temporal-logic-oq-XX`
  could reuse `ModalFormula` + `KripkeFrame` directly with a linear-order
  axiom on R).
- The "modal companion" framework for intuitionistic logic (S4-translation
  via Gödel-McKinsey-Tarski) — the modal half is what this PREP installs.

This is the **infrastructure-multiplier** justification for opening
the modal-logic side now, rather than waiting for the Σ₁-arithmetization
unblock.

## Test plan

- [x] `git diff --stat origin/main` shows exactly one new
      `sessions/2026-05-13-s5-prep-kripke-semantics-gl-segerberg.md`
      file
- [x] No edits to `problem.md` / `state.md` / `knowledge.md` / any
      `.json` / any `.lean`
- [x] Filename distinct from all merged session memos:
      - `2026-05-13-s1b-observe-typeclass-encoding-axiom-budget.md`
      - `2026-05-13-s4-prep-lob-theorem-design.md`
- [x] Soundness proof for Löb axiom verified by hand: maximal-element
      extraction → transitivity → antecedent of (L) → contradiction
- [x] Frame-condition / modal-axiom correspondence table verified
      (4 ↔ transitive, L ↔ Noetherian, etc. — standard textbook content)
- [x] No GL-proof-system definition introduced (anti-target item 1
      respected)
- [x] No arithmetic content introduced (anti-target item 3 respected)
- [x] No cross-references to S4-axiom-encoding-via-typeclass machinery
      (orthogonality to PR #18404 preserved)

## References

- Segerberg, K. (1971). *An essay in classical modal logic*. Filosofiska
  Studier 13, Uppsala. — the original Kripke-completeness theorem
  for GL.
- Boolos, G. (1993). *The Logic of Provability*. Cambridge University
  Press. — canonical reference for GL Kripke semantics and Solovay's
  theorem.
- Chagrov, A. & Zakharyaschev, M. (1997). *Modal Logic*. Oxford
  Logic Guides 35. — broad survey including completeness proofs.
- Sambin, G. (1976). *An effective fixed-point theorem in intuitionistic
  diagonalizable algebras*. Studia Logica 35:345–361. — alternative
  proof of Löb's axiom via the diagonal lemma.
- Parent gallery: `proofs/Proofs/GodelSecondIncompletenessOQ02.lean`
  (line 213 informal Löb statement, line 250 axiom-count note).
- Sibling memos:
  - `sessions/2026-05-13-s1b-observe-typeclass-encoding-axiom-budget.md`
    (S1b OBSERVE).
  - `sessions/2026-05-13-s4-prep-lob-theorem-design.md` (S4 PREP).
- Related Mathlib infrastructure: `Mathlib.ModelTheory.Basic` (first-order
  model theory — different layer; not used here).
