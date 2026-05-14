import Proofs.GodelSecondIncompletenessOQ02

/-!
# Gödel's Second Incompleteness — S2-α Companion: Object-Level Implication + HBL D2/D3

This companion file is the **S2-α ACT** for the
`godel-second-incompleteness-oq02-oq-02` research slug (Solovay's arithmetical
completeness for GL). After **nine merged PREP/OBSERVE design memos** (S1, S1b,
S4 – S11) without a single Lean ACT landing, this is the smallest unblocking
deliverable per `research/problems/godel-second-incompleteness-oq02-oq-02/state.md`
"ACT readiness map" §"S2-α companion".

## Purpose

The parent file `GodelSecondIncompletenessOQ02.lean` bundles the Hilbert-Bernays-Löb
(HBL) conditions D2 and D3 (together with the Diagonal Lemma applied to ¬Prov)
into a single opaque axiom `con_implies_G` (line 153). This companion file
**unbundles** D2 and D3 by:

1. Introducing an object-level implication `impl_formula : Formula → Formula → Formula`
   on the gallery's Gödel-coded `Formula` type, with infix notation `→ᶠ`.
2. Stating the meta-level modus-ponens rule for `impl_formula` as an axiom (`impl_mp`).
3. Stating the HBL D2 condition (internal distribution of `Prov` over `impl_formula`)
   as an axiom (`d2_distribution`).
4. Stating the HBL D3 condition (internal necessitation: provability of provability is
   provable) as an axiom (`d3_internal_necessitation`).

## Why a companion file (and not a parent-file edit)

The parent `GodelSecondIncompletenessOQ02.lean` is **verified** under its current axiom
budget (5 from First + 1 `con_implies_G` = 6). Adding D2/D3/impl_mp to the parent would
mean touching a verified file. Isolating the new axioms in a companion preserves the
parent's verified status and lets future S4 (Löb), S7 (arithmetical soundness),
and S11 (Łukasiewicz tautology lift) ACTs import this file additively.

## Axiom budget delta

This file adds **+3 axioms** to the gallery:

| Axiom | Role |
|-------|------|
| `impl_mp` | Meta-level modus ponens for `impl_formula` — the "deductive theorem" rule |
| `d2_distribution` | D2 (HBL): F ⊢ Prov ⌜φ → ψ⌝ implies F ⊢ Prov ⌜φ⌝ → Prov ⌜ψ⌝ |
| `d3_internal_necessitation` | D3 (HBL): F ⊢ Prov ⌜φ⌝ → Prov ⌜Prov ⌜φ⌝⌝ |

Per the project's axiom-integrity policy (`CLAUDE.md` §"Axiom Integrity"), these
three were **implicitly** bundled inside the existing `con_implies_G` axiom — and
also inside the informal Löb statement at parent line 213. Unbundling does not
add new mathematical content; it makes existing assumptions explicit.

## What this file does NOT do

- **Does not prove Löb's theorem.** That is S4 ACT scope; it requires an
  additional `lob_henkin_fixed_point` axiom (Henkin's diagonal lemma for the
  formula `Prov(x) → A`) and a 7-step internal derivation. See
  `sessions/2026-05-13-s4-prep-lob-theorem-design.md`.
- **Does not redefine `neg` via `impl_formula`.** S4 PREP §6b flags the
  classical convention `neg φ := impl_formula φ falsum` as desirable but
  breaking — deferred to a future refactor.
- **Does not derive `con_implies_G`.** That requires Löb (S4 ACT) +
  `neg_eq_impl_falsum` (a structural lemma, also S4 ACT scope).
- **Does not introduce a `GLFormula` inductive type or `translate` function.**
  Those are S8 + S10 ACT scope (separate companion files).

The single sanity theorem `internal_K` at the bottom of this file demonstrates
that the existing parent axiom `d1_representability` and the new `d2_distribution`
compose cleanly into the GL **K rule** (necessitation-distribution): from
`F ⊢ φ → ψ` derive `F ⊢ Prov ⌜φ⌝ → Prov ⌜ψ⌝`. This is a real *theorem*
(not an axiom), confirming the unbundling is structurally sound.

## Encoding choice for `impl_formula`

`impl_formula φ ψ := ⟨3 + 2 * Nat.pair φ.code ψ.code⟩`

The tag `3 + 2k` keeps `impl_formula`-coded numbers **disjoint** from the existing
tag families (per S10 PREP `#18678` §3.6):

| Constructor | Image | Disjointness |
|-------------|-------|--------------|
| `falsum = ⟨0⟩` | `{0}` | `3 + 2k ≥ 3 > 0` |
| `Prov n = ⟨n * 2⟩` | `{0, 2, 4, ...}` (all even) | `3 + 2k` is odd |
| `neg φ = ⟨φ.code + 1⟩` | (no fixed pattern) | non-collision is *not* guaranteed for arbitrary inputs, but no gallery code destructs back from codes to constructors, so the overlap is **non-substantive** (S10 PREP §3.6) |
| `G = ⟨42⟩` | `{42}` | `42 = 3 + 2k` requires `k = 19.5` — not a natural number, so disjoint |

The specific codes do not affect the logical arguments (per parent file
lines 78–82); the choice here is documentary, not structural.

## Status

- **0 sorries**
- **+3 axioms** (`impl_mp`, `d2_distribution`, `d3_internal_necessitation`)
- **1 derived theorem** (`internal_K` — sanity check that D1 + D2 compose)
- Unblocks S4 ACT (Löb), S7 ACT (soundness induction), and S11 ACT
  (Łukasiewicz tautology lift). Does not change parent file's verified state.
-/

open GodelFirst

namespace GodelSecond

-- ============================================================
-- PART 1: Object-level implication on Formula
-- ============================================================

/-- Object-level implication: `impl_formula φ ψ` is the formula expressing "φ → ψ"
    inside F. The Gödel encoding `⟨3 + 2 * Nat.pair φ.code ψ.code⟩` keeps the codes
    disjoint from `falsum`, `Prov`, and `G` (see file docstring §"Encoding choice"). -/
def impl_formula (φ ψ : Formula) : Formula :=
  ⟨3 + 2 * Nat.pair φ.code ψ.code⟩

@[inherit_doc] infixr:50 " →ᶠ " => impl_formula

/-- The code of `impl_formula φ ψ` is `3 + 2 * Nat.pair φ.code ψ.code`. By `rfl`. -/
theorem impl_formula_code (φ ψ : Formula) :
    (impl_formula φ ψ).code = 3 + 2 * Nat.pair φ.code ψ.code := rfl

/-- `impl_formula φ ψ` is never `falsum`. (Sanity check: confirms the encoding is
    disjoint from `falsum = ⟨0⟩`.) -/
theorem impl_formula_ne_falsum (φ ψ : Formula) :
    impl_formula φ ψ ≠ falsum := by
  intro h
  have hc : (impl_formula φ ψ).code = falsum.code := by rw [h]
  simp [impl_formula, falsum] at hc

/-- `impl_formula φ ψ` is never a `Prov n` formula. (Sanity check: confirms the
    encoding's odd-code image is disjoint from `Prov`'s even-code image.) -/
theorem impl_formula_ne_Prov (φ ψ : Formula) (n : Nat) :
    impl_formula φ ψ ≠ Prov n := by
  intro h
  have hc : (impl_formula φ ψ).code = (Prov n).code := by rw [h]
  simp [impl_formula, Prov] at hc
  omega

-- ============================================================
-- PART 2: The three HBL axioms on `impl_formula`
-- ============================================================

/-- **Axiom — Meta-level modus ponens for `impl_formula`**

    `(⊢ φ →ᶠ ψ) → (⊢ φ) → (⊢ ψ)`

    This is the meta-level inference rule "from `F ⊢ φ → ψ` and `F ⊢ φ` infer
    `F ⊢ ψ`". In a Hilbert-style presentation this is the **inference rule MP**;
    it is logically distinct from D2 (which is the internal/object-level version
    of distributivity). MP is sometimes called the "necessitation rule for
    implication"; without it, `impl_formula` would carry no operational content.

    **Why this is an axiom rather than a derived rule**: the gallery's `Provable`
    is an *opaque* predicate (parent's `axiom Provable : Formula → Prop`), so
    Lean cannot computationally extract a proof of `ψ` from proofs of `φ → ψ`
    and `φ`. We assert the meta-level MP rule directly. -/
axiom impl_mp : ∀ (φ ψ : Formula), (⊢ φ →ᶠ ψ) → (⊢ φ) → (⊢ ψ)

/-- **Axiom — D2 (Distribution of Prov over implication)**

    `(⊢ Prov ⌜φ →ᶠ ψ⌝) → (⊢ Prov ⌜φ⌝ →ᶠ Prov ⌜ψ⌝)`

    This is the HBL D2 condition (Hilbert-Bernays 1939). It says that if F
    internally proves `Prov ⌜φ → ψ⌝`, then F internally proves the *function*
    that turns proofs of φ into proofs of ψ — i.e., F can *internalize* its
    own modus-ponens rule.

    **Mathematical content**: D2 is the formalization of "the proof system F is
    closed under modus ponens, *and F can prove that fact*". It is satisfied by
    Peano Arithmetic and any sufficiently strong system that codes its own
    syntax and proof-checking procedure.

    **Full formalization path**: in a system with concrete Σ_1-formalized
    `Provable`, D2 follows from the primitive-recursive definition of
    proof-concatenation and the Σ_1-completeness of arithmetic. We take it as
    an axiom because the gallery's `Provable` is opaque (S6 PREP `#18497`). -/
axiom d2_distribution : ∀ (φ ψ : Formula),
    (⊢ Prov (godelNum (φ →ᶠ ψ))) → (⊢ Prov (godelNum φ) →ᶠ Prov (godelNum ψ))

/-- **Axiom — D3 (Internal necessitation: Σ_1-completeness restricted to `Prov`)**

    `⊢ Prov ⌜φ⌝ →ᶠ Prov ⌜Prov ⌜φ⌝⌝`

    This is the HBL D3 condition (Löb 1955; sometimes called the "L4" axiom or
    "internal necessitation"). It says that if F internally proves the
    Σ_1-formula `Prov ⌜φ⌝`, then F can *internally* certify that `Prov ⌜φ⌝` is
    itself provable.

    **Mathematical content**: D3 is the formalization of Σ_1-completeness
    *restricted to provability claims*. In Boolos's modal-logic notation, this
    is the GL axiom `□φ → □□φ` (sometimes called the **transitivity axiom 4**).

    **Why D3 is logically independent of D1 and D2**: D1 lifts external truths
    into F (`F ⊢ φ → F ⊢ Prov ⌜φ⌝`); D2 distributes `Prov` over implication;
    D3 specifically handles the *iteration* of `Prov`. None subsumes another;
    all three are needed to formalize Löb's theorem (S4 ACT). -/
axiom d3_internal_necessitation : ∀ (φ : Formula),
    ⊢ Prov (godelNum φ) →ᶠ Prov (godelNum (Prov (godelNum φ)))

-- ============================================================
-- PART 3: Sanity theorem — D1 + D2 give the GL K rule
-- ============================================================

/-- **GL K-rule (necessitation-distribution)**

    `(⊢ φ →ᶠ ψ) → (⊢ Prov ⌜φ⌝ →ᶠ Prov ⌜ψ⌝)`

    This is a genuine **theorem** (not an axiom) derived by composing the
    parent's `d1_representability` (D1, line 123) with this file's
    `d2_distribution` (D2). It corresponds to the modal-logic K-rule for GL:
    "from `F ⊢ φ → ψ` infer `F ⊢ □φ → □ψ`".

    **Proof**:
    1. By D1 applied to the hypothesis: `⊢ Prov ⌜φ → ψ⌝`.
    2. By D2 applied to (1): `⊢ Prov ⌜φ⌝ → Prov ⌜ψ⌝`.

    **Significance**: This theorem is the **structural witness** that
    unbundling D2/D3 from `con_implies_G` does not lose any operational content
    — D1 + D2 alone already give the K-rule, which is the "workhorse" of all
    HBL-based proofs. With D3 (above) and a future `lob_henkin_fixed_point`
    (S4 ACT), the full Löb theorem becomes derivable. -/
theorem internal_K (φ ψ : Formula) (h : ⊢ φ →ᶠ ψ) :
    ⊢ Prov (godelNum φ) →ᶠ Prov (godelNum ψ) :=
  d2_distribution φ ψ (d1_representability _ h)

-- Verify the new declarations are accessible at the namespace level
#check @impl_mp
#check @d2_distribution
#check @d3_internal_necessitation
#check @internal_K

end GodelSecond
