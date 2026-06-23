/-!
# GL syntax: `GLFormula` + `PropAxiom` + `GL_proves`

Syntactic foundation for the propositional modal logic GL (Gödel-Löb).

This companion file is **independent** of the parent `Proofs.GodelSecondIncompletenessOQ02`
and `Proofs.GodelFirstIncompletenessOQ01`. It defines the modal-formula
language and the Hilbert-style derivability predicate `GL_proves`, in the
form expected by downstream stages:

- **S5 ACT** (Kripke semantics) will define `forces : KripkeModel → World → GLFormula → Prop`
  and prove `forces_of_GL_proves` by induction on `GL_proves`.
- **S7 ACT** (arithmetical soundness) will define
  `translate : (PropAtom → Formula) → GLFormula → Formula` bridging GL to PA,
  and prove `GL_proves φ → ∀ ρ, ⊢ translate ρ φ`.

Design follows S8 PREP #18566 §9 (recommended choice: Option B —
Łukasiewicz propositional axiom schemas + Kalmár completeness), tightened by
S9 PREP #18623 §7 (drop unnecessary imports, drop low-value `@[simp]` renames).

The propositional fragment uses the three Łukasiewicz schemas (Łukasiewicz 1929):

- k1: `p → (q → p)`
- k2: `(p → (q → r)) → ((p → q) → (p → r))`
- k3: `(¬p → ¬q) → (q → p)`

Combined with the `mp` constructor of `GL_proves`, these give the full
classical propositional fragment by Kalmár's theorem (Mendelson 2015, §1.6).

GL-specific axioms (`K`, `L`, `nec`) are direct constructors on `GL_proves`.

References:
- Boolos, G. (1993). *The Logic of Provability*. Cambridge University Press. Chs. 1–2.
- Mendelson, E. (2015). *Introduction to Mathematical Logic*, 6th ed. CRC Press. §1.6.
- Smoryński, C. (1985). *Self-Reference and Modal Logic*. Springer. §1.

LOC budget: ≤80 (per S8 PREP §10). Actual: ~55 LOC of source.
Axioms: 0. Sorries: 0.
-/

namespace GodelSecondGLSyntax

/-- Atomic propositional variables of GL formulas. The natural choice is `Nat`
    so that we have countably many atoms; this is what Solovay's completeness
    construction requires. -/
abbrev PropAtom : Type := Nat

/-- Formulas of the propositional modal logic GL.

    Four constructors (atom / falsum / impl / box) suffice — every other
    propositional connective is classically definable (e.g. `¬φ := φ → ⊥`,
    `φ ∧ ψ := ¬(φ → ¬ψ)`, `◇φ := ¬□¬φ`). -/
inductive GLFormula : Type where
  | atom (p : PropAtom)        : GLFormula
  | falsum                      : GLFormula
  | impl (p q : GLFormula)      : GLFormula
  | box  (p : GLFormula)        : GLFormula
  deriving DecidableEq, Repr

namespace GLFormula

/-- Derived negation: `¬φ := φ → ⊥`. -/
def not (p : GLFormula) : GLFormula := .impl p .falsum

end GLFormula

/-- The three Łukasiewicz axiom schemas for classical propositional logic
    with `→` and `⊥` as primitives. Together with `GL_proves.mp` these
    give the full classical propositional fragment (Kalmár's theorem). -/
inductive PropAxiom : GLFormula → Prop where
  | k1 (p q   : GLFormula) : PropAxiom (.impl p (.impl q p))
  | k2 (p q r : GLFormula) :
      PropAxiom (.impl (.impl p (.impl q r))
                       (.impl (.impl p q) (.impl p r)))
  | k3 (p q   : GLFormula) :
      PropAxiom (.impl (.impl (.impl p .falsum) (.impl q .falsum))
                       (.impl q p))

/-- Hilbert-style derivability for the propositional modal logic GL.

    Five constructors:

    - `taut` — propositional fragment via Łukasiewicz schemas
    - `k`    — modal distribution axiom `K`: `□(p → q) → (□p → □q)`
    - `lob`  — Löb's axiom `L`: `□(□p → p) → □p`
    - `mp`   — modus ponens
    - `nec`  — necessitation

    Substitution is admissible (Avron 1991; Kracht 1999 §3.1): each schematic
    constructor is parametric in arbitrary `GLFormula` arguments, so any
    substitution instance of a derivable formula is derivable by the same
    derivation tree with substituted parameters. No `subst` constructor is
    needed. -/
inductive GL_proves : GLFormula → Prop where
  | taut {t : GLFormula} (h : PropAxiom t) : GL_proves t
  | k    (p q : GLFormula) :
      GL_proves (.impl (.box (.impl p q)) (.impl (.box p) (.box q)))
  | lob  (p : GLFormula) :
      GL_proves (.impl (.box (.impl (.box p) p)) (.box p))
  | mp   {p q : GLFormula} (h₁ : GL_proves (.impl p q)) (h₂ : GL_proves p) :
      GL_proves q
  | nec  {p : GLFormula} (h : GL_proves p) : GL_proves (.box p)

end GodelSecondGLSyntax
