/-
# GL derives the "4" schema: `□A → □□A` (S18 ACT)

  Slug: godel-second-incompleteness-oq02-oq-02

First **derived theorem** inside the S8 GL Hilbert system
(`Proofs.GodelSecondIncompletenessOQ02GLSyntax`): the transitivity schema

    GL ⊢ □A → □□A

is NOT among the primitive constructors of `GL_proves` (which has only the
Łukasiewicz propositional schemas, `K`, Löb's `L`, `mp`, `nec`) — yet it is
derivable, which is the standard first non-trivial fact about GL (Boolos,
*The Logic of Provability*, Ch. 1; Smoryński §1): **GL extends K4**, i.e. the
Löb axiom secretly contains transitivity.

## Why this matters for the arithmetical side

Under Solovay's arithmetical reading (`translate`, S10 ACT), `four` says the
formalized D3 condition (`Prov⌜a⌝ → Prov⌜Prov⌜a⌝⌝`, internally) is *implied*
by the K + Löb principles: any future discharge of the `Hk`/`Hlob` hypotheses
of `arithmetical_soundness_of` (S16 ACT) automatically yields the internal D3
translation — it never needs to be assumed separately.

## Mechanism (Boolos' derivation, fully formalized)

With `B := A ∧ □A` (conjunction classically defined from `→`/`⊥`):

1. `⊢ B → A`, `⊢ B → □A` (propositional, via the defined-conjunction elims);
2. `box_mono` (K + nec derived rule) lifts them to `⊢ □B → □A`, `⊢ □B → □□A`;
3. the combinator layer turns `conj_intro : ⊢ A → □A → B` and `⊢ □B → □A`
   into `⊢ A → (□B → B)` (two `flip`s around an `imp_trans`);
4. `box_mono` again: `⊢ □A → □(□B → B)`; Löb at `B`: `⊢ □(□B → B) → □B`;
5. chaining: `⊢ □A → □B → □□A`. ∎

The propositional fragment is developed from the three Łukasiewicz schemas
alone (identity, ex falso, double-negation intro, flip/swap combinators,
defined conjunction with intro/elims) — a reusable toolkit for the pending
`Htaut` instance discharges (S16's open hypotheses).

Imports: only the S8 GLSyntax file (no Mathlib) — the whole development is
self-contained term-mode Hilbert derivations.

Axioms: 0.  Sorries: 0.
-/
import Proofs.GodelSecondIncompletenessOQ02GLSyntax

namespace GodelSecondGLFour

open GodelSecondGLSyntax

local infixr:55 " ⟶ " => GLFormula.impl
local prefix:75 "□" => GLFormula.box
local notation "⊥ₘ" => GLFormula.falsum

-- ============================================================
-- PART 1: Łukasiewicz-schema wrappers
-- ============================================================

/-- Schema k1 as a theorem: `⊢ p → (q → p)`. -/
theorem ax1 (p q : GLFormula) : GL_proves (p ⟶ q ⟶ p) :=
  .taut (.k1 p q)

/-- Schema k2 as a theorem: `⊢ (p → (q → r)) → ((p → q) → (p → r))`. -/
theorem ax2 (p q r : GLFormula) :
    GL_proves ((p ⟶ q ⟶ r) ⟶ (p ⟶ q) ⟶ (p ⟶ r)) :=
  .taut (.k2 p q r)

/-- Schema k3 as a theorem: `⊢ (¬p → ¬q) → (q → p)`. -/
theorem ax3 (p q : GLFormula) :
    GL_proves (((p ⟶ ⊥ₘ) ⟶ (q ⟶ ⊥ₘ)) ⟶ (q ⟶ p)) :=
  .taut (.k3 p q)

-- ============================================================
-- PART 2: propositional toolkit (derived rules and theorems)
-- ============================================================

/-- Identity: `⊢ p → p` (the classic k1/k2 combination). -/
theorem imp_id (p : GLFormula) : GL_proves (p ⟶ p) :=
  ((ax2 p (p ⟶ p) p).mp (ax1 p (p ⟶ p))).mp (ax1 p p)

/-- Derived rule — transitivity of implication (hypothetical syllogism):
    from `⊢ p → q` and `⊢ q → r` conclude `⊢ p → r`. -/
theorem imp_trans {p q r : GLFormula}
    (h₁ : GL_proves (p ⟶ q)) (h₂ : GL_proves (q ⟶ r)) :
    GL_proves (p ⟶ r) :=
  ((ax2 p q r).mp ((ax1 (q ⟶ r) p).mp h₂)).mp h₁

/-- Derived rule — argument flip: from `⊢ p → (q → r)` conclude
    `⊢ q → (p → r)`. -/
theorem flip {p q r : GLFormula} (h : GL_proves (p ⟶ q ⟶ r)) :
    GL_proves (q ⟶ p ⟶ r) :=
  imp_trans (ax1 q p) ((ax2 p q r).mp h)

/-- Theorem-form swap: `⊢ (p → (q → r)) → (q → (p → r))`. -/
theorem imp_swap (p q r : GLFormula) :
    GL_proves ((p ⟶ q ⟶ r) ⟶ (q ⟶ p ⟶ r)) :=
  flip (imp_trans (ax1 q p) (flip (ax2 p q r)))

/-- Ex falso quodlibet: `⊢ ⊥ → p` (classically, via k3 against `¬⊥`). -/
theorem efq (p : GLFormula) : GL_proves (⊥ₘ ⟶ p) :=
  (ax3 p ⊥ₘ).mp ((ax1 (⊥ₘ ⟶ ⊥ₘ) (p ⟶ ⊥ₘ)).mp (imp_id ⊥ₘ))

/-- Double-negation introduction: `⊢ p → ¬¬p` (a flip of identity). -/
theorem dni (p : GLFormula) : GL_proves (p ⟶ (p ⟶ ⊥ₘ) ⟶ ⊥ₘ) :=
  flip (imp_id (p ⟶ ⊥ₘ))

/-- Antecedent strengthening through `⊥`: `⊢ ¬p → (p → ¬q)`. -/
theorem neg_imp_lift (p q : GLFormula) :
    GL_proves ((p ⟶ ⊥ₘ) ⟶ (p ⟶ q ⟶ ⊥ₘ)) :=
  (ax2 p ⊥ₘ (q ⟶ ⊥ₘ)).mp ((ax1 (⊥ₘ ⟶ q ⟶ ⊥ₘ) p).mp (efq (q ⟶ ⊥ₘ)))

-- ============================================================
-- PART 3: defined conjunction with intro/elim
-- ============================================================

/-- Classical conjunction over the `→`/`⊥` fragment:
    `p ∧ q := ¬(p → ¬q)`. -/
def conj (p q : GLFormula) : GLFormula :=
  (p ⟶ q ⟶ ⊥ₘ) ⟶ ⊥ₘ

/-- Conjunction introduction: `⊢ p → (q → p ∧ q)` — "apply the hypothesis
    `p → ¬q` to `p`, then to `q`" via the swap combinator. -/
theorem conj_intro (p q : GLFormula) :
    GL_proves (p ⟶ q ⟶ conj p q) :=
  imp_trans (flip (imp_id (p ⟶ q ⟶ ⊥ₘ))) (imp_swap (p ⟶ q ⟶ ⊥ₘ) q ⊥ₘ)

/-- Left projection: `⊢ p ∧ q → p` (k3 against `¬p → ¬(p ∧ q)`). -/
theorem conj_elim_left (p q : GLFormula) :
    GL_proves (conj p q ⟶ p) :=
  (ax3 p (conj p q)).mp (imp_trans (neg_imp_lift p q) (dni (p ⟶ q ⟶ ⊥ₘ)))

/-- Right projection: `⊢ p ∧ q → q` (k3 against `¬q → ¬(p ∧ q)`). -/
theorem conj_elim_right (p q : GLFormula) :
    GL_proves (conj p q ⟶ q) :=
  (ax3 q (conj p q)).mp
    (imp_trans (ax1 (q ⟶ ⊥ₘ) p) (dni (p ⟶ q ⟶ ⊥ₘ)))

-- ============================================================
-- PART 4: the modal layer and the 4 schema
-- ============================================================

/-- Derived rule — box monotonicity (regularity): from `⊢ p → q` conclude
    `⊢ □p → □q`.  This is exactly `K` applied to the necessitation of the
    hypothesis. -/
theorem box_mono {p q : GLFormula} (h : GL_proves (p ⟶ q)) :
    GL_proves (□p ⟶ □q) :=
  (GL_proves.k p q).mp (.nec h)

/-- **GL derives the "4" schema: `⊢ □A → □□A`** — GL extends K4.

The schema is not a constructor of `GL_proves`; it falls out of Löb's axiom
via Boolos' argument.  With `B := A ∧ □A`:

* `□B → □A` and `□B → □□A` (box-monotone conjunction projections);
* `A → (□B → B)` — given `A`, a proof of `B` yields `□A` (first projection
  lifted), and `A` with `□A` re-assemble `B` (`conj_intro`); formally two
  `flip`s around an `imp_trans`;
* box-monotonicity: `□A → □(□B → B)`; Löb at `B`: `□(□B → B) → □B`;
* chain through `□B → □□A`. ∎ -/
theorem four (A : GLFormula) : GL_proves (□A ⟶ □□A) :=
  let B := conj A (□A)
  -- projections, lifted through the box
  let s₁ : GL_proves (□B ⟶ □A) := box_mono (conj_elim_left A (□A))
  let s₂ : GL_proves (□B ⟶ □□A) := box_mono (conj_elim_right A (□A))
  -- `A → (□B → B)`
  let d : GL_proves (A ⟶ □B ⟶ B) :=
    flip (imp_trans s₁ (flip (conj_intro A (□A))))
  -- Löb closes the loop
  let g : GL_proves (□A ⟶ □B) :=
    imp_trans (box_mono d) (GL_proves.lob B)
  imp_trans g s₂

/-- `iterBox n A = □…□A` with `n` boxes. -/
def iterBox : Nat → GLFormula → GLFormula
  | 0, A => A
  | n + 1, A => □(iterBox n A)

/-- Iterated transitivity: `⊢ □A → □ⁿ⁺¹A` for every `n` — repeated
    application of `four` under `box_mono`.  (`n = 0` is identity; each
    successor composes one `four` with the boxed induction hypothesis.) -/
theorem box_iterate (A : GLFormula) :
    ∀ n : Nat, GL_proves (□A ⟶ iterBox (n + 1) A)
  | 0 => imp_id (□A)
  | n + 1 => imp_trans (four A) (box_mono (box_iterate A n))

end GodelSecondGLFour
