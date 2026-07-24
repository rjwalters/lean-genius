# Knowledge — Solovay Arithmetical Completeness for GL (godel-second-incompleteness-oq02-oq-02)

## 1. The modal logic GL

**GL (Gödel-Löb)** is the propositional modal logic with the following Hilbert-style presentation. Language: propositional letters `p, q, ...`, classical connectives `→, ⊥`, modality `□`. Other connectives definable as usual.

### Axiom schemata
- (TAUT) all classical propositional tautologies.
- (K) `□(p → q) → (□p → □q)`.
- (L) `□(□p → p) → □p` — the **Löb axiom**.

### Rules
- (MP) Modus ponens.
- (NEC) Necessitation: from `⊢ p` infer `⊢ □p`.

The Löb axiom (L) is what distinguishes GL from K4. It is itself a theorem of K + (4) `□p → □□p`, but only when combined with self-reference; GL takes (L) as primitive and *derives* (4):

- (4) `□p → □□p` is a theorem of GL.
- (T) `□p → p` is *not* a theorem of GL (and would in fact collapse GL to the inconsistent logic by Löb).

### Kripke semantics
GL is sound and complete for **finite transitive irreflexive Kripke frames**. ("Finite" comes from the Segerberg completeness theorem for GL; the more common semantic claim is "finite, transitive, conversely well-founded" frames.)

## 2. Arithmetical realization

Given a structure of formal arithmetic (PA in Solovay's original; any consistent r.e. extension of Robinson's Q works for soundness, but PA-style for completeness):

A **realization** is a function `* : PropAtom → Formula_PA`, extended to all GL-formulas by:

| GL syntax | Translation `φ*` |
|---|---|
| `p` (atom) | `*p` (chosen formula of PA) |
| `⊥` | `⊥` (PA-falsehood, e.g. `0 = 1`) |
| `φ → ψ` | `φ* → ψ*` |
| `□φ` | `Prov(⌜φ*⌝)` — Gödel's provability predicate |

**Solovay's theorem:**

> `GL ⊢ φ ⟺ ∀ realizations *, PA ⊢ φ*`

The (⟹) direction (soundness) follows from PA verifying HBL conditions D1–D3 plus the Löb derivability theorem. The (⟸) direction (completeness) is the hard part — Solovay's original construction embeds an arbitrary finite GL-Kripke counter-model into PA via a clever fixed-point construction.

## 3. Soundness direction — what's already (axiomatized) in the gallery

The existing `GodelSecondIncompletenessOQ02.lean` already contains the load-bearing pieces for soundness:

| GL principle | Gallery analogue | Line |
|---|---|---|
| (K) `□(p→q) → (□p → □q)` | (would need `impl : Formula → Formula → Formula`) | not present |
| (L) `□(□p → p) → □p` | informal in docstring `Löb's Theorem` | 213–235 |
| (NEC) `⊢ φ ⇒ ⊢ □φ` | `d1_representability` axiom (from `GodelFirstIncompletenessOQ01`) | (parent) |
| (4) `□φ → □□φ` | D3 condition (subsumed into `con_implies_G`) | 153 |
| Second incompleteness | `second_incompleteness` theorem | 186 |

**Gap:** The current `Formula` type has only `falsum` and `neg`/`Prov` as constructors needed for `Con`; there is **no object-language implication `impl : Formula → Formula → Formula`**. The axiom-count note (line 250) explicitly flags this: "without object-level implication, [D2 and D3] cannot be stated in the current type system."

So the soundness direction of Solovay's theorem requires, as a *prerequisite*, extending the `Formula` type with `impl` (and ideally `conj`, `disj` for syntactic uniformity). This is **S2-α below**.

## 4. Completeness direction — Solovay's construction (sketch)

Solovay's original proof (1976) is one of the most ingenious arguments in 20th-century mathematical logic. Here is the high-level structure:

### Setup
Given a GL-formula `φ` such that `GL ⊬ φ`, we want a realization `*` with `PA ⊬ φ*`.

By Segerberg's completeness theorem, there is a finite irreflexive transitive Kripke model `K = ⟨W, R, V⟩` and a world `w₀ ∈ W` with `K, w₀ ⊨ ¬φ`.

### Solovay's recursive labels
Define a recursive function `h : ℕ → W ∪ {0}` (where `0` is a "halt" sentinel) by:

```
h(0) = 0  -- start state
h(n+1) = w  if h(n) ∈ {0, predecessors of w in R} and at step n+1 PA has not yet
            decided the question "does h enter the future of w?"
```

This `h` is computable (PA can define it), and Solovay shows:

- For each world `w ∈ W`, the formula `S_w := "h eventually halts in w or its R-future" can be expressed in PA.
- The arithmetical realization sends each propositional atom `p` to `⋁_{w : V(p) ∋ w} S_w`.
- Solovay proves: for each world `w` and GL-formula ψ, `K, w ⊨ ψ ⟺ PA ⊢ (S_w → ψ*)`.

Specializing to the witnessing world `w₀ ⊨ ¬φ`, we get `PA ⊢ S_{w₀} → ¬φ*`, hence `PA ⊬ φ*` (assuming PA is consistent and `S_{w₀}` is itself unrefutable — which Solovay proves).

### Why it's hard to formalize
The construction requires:

1. **PA-formalized recursion theory.** The function `h` must be PA-definable, and PA must verify its properties; this needs `ConditionalFunction.encode` / partial-recursive encoding.
2. **Sigma-1 arithmetization of GL satisfaction.** The relation `K, w ⊨ φ` must be PA-arithmetizable as a Σ_1-formula on the Gödel-codes.
3. **Kripke completeness of GL.** Segerberg's theorem itself (GL is sound and complete over finite transitive irreflexive frames) — this is a non-trivial modal-logic result.
4. **Coherence with the existing `Prov` axiom.** The current gallery uses an *opaque* `Provable : Formula → Prop` axiom (`GodelFirstIncompletenessOQ01`). Solovay's construction requires `Prov` to be the *actual* Σ_1-formalization, not an abstract predicate.

These four ingredients are each substantial; a full formalization would be a multi-thousand-line effort comparable to Iorgulescu's Coq formalization of GL.

## 5. Mathlib API survey

```
Mathlib.Logic.Basic
  - Classical.em, not_not  (already used by the gallery)

Mathlib.ModelTheory.Basic
  - First-order language framework (for arithmetization of PA syntax)
  - Note: Mathlib's first-order machinery is not yet Σ_n-stratified

Mathlib.Computability.Partrec
  - Partial recursive functions (for Solovay's h)
  - Gödel numbering: Mathlib.Computability.Primrec

Mathlib.Computability.GodelBeta
  - β-function (for sequence coding in PA) — not yet in Mathlib as of v4.26.0
```

**Gap analysis:**
- Mathlib has no provability-logic / modal-logic library. A `GL` formalization would be the first.
- Mathlib's first-order ModelTheory framework can encode PA but does not yet have a Σ_n hierarchy.
- The β-function and primitive-recursive arithmetic are partial: PRA-style coding is available, but the full Σ_1-completeness theorem (every true Σ_1-sentence is PA-provable) is not in Mathlib.

## 6. Three candidate S2 deliverables (ranked by tractability)

### S2-α (Easy, ~50–120 lines) — Extend `Formula` with `impl`
Augment `GodelIncompleteness.lean` (or a companion file) with:

```lean
def impl (φ ψ : Formula) : Formula := ⟨encode (φ, ψ, "impl")⟩

axiom d2_axiom : ∀ φ ψ, (⊢ impl φ ψ) ↔ ((⊢ φ) → (⊢ ψ))
axiom d3_axiom : ∀ φ, (⊢ Prov (godelNum φ)) → (⊢ Prov (godelNum (Prov (godelNum φ))))
```

This *adds* axioms (the gallery convention is honest axiomatization) but enables stating GL principles in the object language. Should be presented as a *companion file* rather than modifying the parent's axiom count.

### S2-β (Medium, ~200–400 lines) — Soundness direction of Solovay
With S2-α complete, prove:

```lean
theorem solovay_soundness (φ : GLFormula) :
    GL_proves φ → ∀ * : PropAtom → Formula, ⊢ realization * φ
```

This is a straightforward induction on `GL_proves` once D2/D3 are stated. The realization function and `GLFormula` type are new definitions but well-localized. The hard work is matching up Lean's `Prov` predicate with GL's `□`.

### S2-γ (Very hard, multi-thousand lines) — Completeness direction
Solovay's original construction. **Not recommended** as a single S2 effort. Better decomposed into:
- S3-1: Define `GLFormula` and `GL_proves` independently of PA. Prove Segerberg completeness (finite Kripke models).
- S3-2: Arithmetize finite Kripke models as Σ_1-formulas of PA.
- S3-3: Solovay's fixed-point `h` construction.
- S3-4: Tie together via the Σ_1-completeness of PA.

**Recommended S2 start: S2-α.** Smallest scope, highest reuse value, unlocks both S2-β and (eventually) Löb's theorem itself (currently informal at line 213 of the parent file).

## 7. Risks and watch-outs

- **Axiom inflation.** Each new axiom added to `Formula` (impl, conj, disj) appears in the gallery's axiom count. Memory project `project_tractatus_review.md` notes the policy that *structure-encoded* assumptions count too. The S2-α design proposes a *companion file* to isolate the new axioms.

- **Opaque `Provable` vs concrete `Prov`.** The current gallery uses an opaque `Provable : Formula → Prop` axiom. Solovay's completeness requires a concrete Σ_1-formalization. This is a fundamental architectural mismatch and means the completeness direction *cannot* be formalized within the current gallery framework without a major rebuild — flagging this is a key S1 deliverable.

- **GL-axiomatization choices.** Different texts give GL via (K)+(L)+(NEC) vs (K)+(4)+(L)+(NEC) (redundant) vs Solovay-style fixed-point semantics. Any S2 work should pin down the axiom set up front.

## 8. References

- Solovay, R. M. (1976). "Provability interpretations of modal logic", *Israel J. Math.* — the original arithmetical completeness theorem.
- Boolos, G. (1993). *The Logic of Provability* — the canonical textbook reference.
- Segerberg, K. (1971). "An essay in classical modal logic" — Kripke completeness of GL over finite transitive irreflexive frames.
- Löb, M. H. (1955). "Solution of a problem of Leon Henkin", *J. Symbolic Logic* — Löb's theorem itself.
- Iorgulescu, V. (Coq). *A Coq formalization of GL* — closest prior art for an interactive-theorem-prover formalization.

---

## S16 ACT (2026-06-11): arithmetical soundness of GL — rule cases

Shipped `proofs/Proofs/GodelSecondIncompletenessOQ02Soundness.lean`
(Docker-verified 3063 jobs, 0 sorries, **0 new axioms**).

**Key structural finding.** The five `GL_proves` constructors split cleanly:
- **Rules `mp`, `nec` are unconditionally sound** — genuine theorems from existing
  infrastructure: `nec ⟶ d1_representability`, `mp ⟶ impl_mp`. Exported as
  `arith_sound_nec` / `arith_sound_mp`.
- **Schemas `taut`, `k`, `lob`** assert PA-provability of specific object formulas.
  Under the opaque `Provable` these are *not derivable* (no object deduction
  theorem; no concrete Σ₁ predicate). So `arithmetical_soundness_of` takes them as
  explicit hypotheses `Htaut`/`Hk`/`Hlob` — yielding a 0-new-axiom soundness
  induction whose only assumptions are the three named derivability facts.

**Translations computed (for future discharge):**
- K-schema: `Prov⌜a→ᶠb⌝ →ᶠ (Prov⌜a⌝ →ᶠ Prov⌜b⌝)` with `a,b := translate ρ p, translate ρ q`.
- Löb-schema: `Prov⌜Prov⌜a⌝ →ᶠ a⌝ →ᶠ Prov⌜a⌝` with `a := translate ρ p`.

**Induction mechanics.** `induction h with` on `GL_proves`: implicit constructor
args are NOT counted in the `| ctor ...` binder list — `taut` takes 1 binder,
`mp` takes 4 (h₁ h₂ ih₁ ih₂), `nec` takes 2 (h ih). The `k`/`lob` axiom cases
close by `simp only [translate_impl, translate_box]` then `exact H...`.

**Next (S17).** Discharge one of `Htaut`/`Hk`/`Hlob` into a theorem. Most
tractable: `Hk` via an object-level deduction/curry lemma composing the meta
`internal_K`; `Hlob` waits on S4 ACT (Löb); `Htaut` needs CPL completeness.

---

## S18 ACT (2026-07-24, researcher-3): GL derives the "4" schema — first derived theorem in the GL Hilbert system

Shipped `proofs/Proofs/GodelSecondIncompletenessOQ02GLFour.lean` (Docker-verified,
**0 axioms, 0 sorries, no Mathlib imports** — `#print axioms four` reports "does not
depend on any axioms": fully constructive term-mode Hilbert derivations).

**Headline**: `four (A) : GL_proves (□A ⟶ □□A)` — the transitivity schema is NOT a
constructor of `GL_proves`, yet derivable (Boolos Ch. 1): **GL extends K4**. Also
`box_iterate : ⊢ □A → □ⁿ⁺¹A` (iterated form).

**Derivation (formalized Boolos argument)**, `B := A ∧ □A` with conjunction defined
classically (`conj p q := ¬(p → ¬q)` over →/⊥):
1. `⊢ B → A`, `⊢ B → □A` (defined-conjunction projections via k3),
2. `box_mono` (= K ∘ nec, derived rule) lifts to `⊢ □B → □A`, `⊢ □B → □□A`,
3. `⊢ A → (□B → B)` = `flip (imp_trans s₁ (flip (conj_intro A □A)))` — no deduction
   theorem needed, just combinators,
4. `box_mono` + `lob B` + chaining.

**Reusable propositional toolkit** (from the three Łukasiewicz schemas alone):
`imp_id`, `imp_trans` (rule), `flip` (rule: ⊢p→(q→r) ⟹ ⊢q→(p→r), = imp_trans (ax1) ∘
mp (ax2)), `imp_swap` (theorem form), `efq` (⊥→p via k3 against ¬⊥), `dni` (p→¬¬p =
flip of id), `neg_imp_lift`, `conj`/`conj_intro`/`conj_elim_left/right`. These are the
building blocks for discharging S16's `Htaut` hypothesis on concrete instances.

**Negative finding (blocked route — S16's recommendation is NOT viable as stated)**:
S16 suggested "discharge Hk via an object-level deduction/curry lemma composing the
meta internal_K". This confuses meta and object levels: `internal_K` (Companion) is
the META rule `(⊢ φ→ᶠψ) → (⊢ Prov⌜φ⌝ →ᶠ Prov⌜ψ⌝)`, while `Hk` demands the OBJECT
theorem `⊢ Prov⌜a→ᶠb⌝ →ᶠ (Prov⌜a⌝ →ᶠ Prov⌜b⌝)` (formalized D2). Under the opaque
`Provable` there is no object-level deduction theorem, so Hk is NOT derivable from
D1/D2/D3/impl_mp — it is a genuinely new assumption (formalized-D2), exactly like
Htaut/Hlob. Reopen bar: materially new mechanism (concrete Σ₁ Provable rebuild, S6
PREP #18497). The same wall blocks meta-level Löb (needs the diagonal fixed point +
object-level propositional chaining under Prov).

**Lean gotchas**: `/-!` module docstring must come AFTER imports (files with no
imports, like GLSyntax, mask this); family style is `/-` header comments. Term-mode
`let B := ...; let s₁ : T := ...` chains elaborate cleanly for Prop-valued Hilbert
derivations; defined `conj` unfolds by defeq in expected types.

**Next steps** (in tractability order):
1. S19: discharge `Htaut` for SPECIFIC translations needed downstream using the new
   toolkit + a `translate`-commutes-with-connectives lemma set (the full Htaut needs
   propositional completeness — Kalmár — a bigger but self-contained project).
2. Kalmár completeness for the →/⊥ fragment over GLFormula (fully constructive,
   ~300-500 LOC): would discharge Htaut wholesale.
3. S5 Kripke semantics + soundness of GL_proves (independent axis, unblocked).
4. Hk/Hlob remain blocked on the Σ₁ rebuild (see negative finding above).
