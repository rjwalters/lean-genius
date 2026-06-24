# Knowledge Base: de-moivre-oq-01-oq-03-oq-02

Insights accumulated during research on this problem.

---

## Problem Understanding

Package the parent's Chebyshev–De Moivre algebra over 𝔽_p as the semigroup / nesting law
`C_{mn}(x) = C_m(C_n(x))`, bundled as a monoid homomorphism `(ℤ, ·) →* (End 𝔽_p, ∘)`, with
the commuting family `C_a ∘ C_b = C_b ∘ C_a` (the Chebyshev/Lucas key-exchange trapdoor).

---

## Insights

- **Mathlib already has the polynomial identity.** `Polynomial.Chebyshev.C_mul` states
  `C R (m*n) = (C R m).comp (C R n)` for the third-kind `C` over any commutative ring. So the
  *core* nesting identity is NOT new; the contribution is the evaluation-map form (one
  `eval_comp` rewrite), the bundled `MonoidHom`, the commuting-family corollary, and the
  power-map conjugacy. The entry is honest about this (badge original for the new packaging;
  description and assumptions credit `C_mul` to Mathlib).
- **The monoid-hom needs no field.** `C_{mn} = C_m ∘ C_n` and commutativity are CommRing
  facts, so they hold over `ZMod p` for ANY modulus — stated in an `AnyModulus` section to
  avoid an unused `[Fact p.Prime]` (which the `unusedSectionVars` linter flags). Only the
  unit-circle conjugacy genuinely uses the field 𝔽_p (via `mul_inv_cancel₀ z⁻¹`).
- **The nesting law is the power law in disguise.** On `z·w = 1`, `zⁿ·wⁿ = (z·w)ⁿ = 1`, so
  `(zⁿ, wⁿ)` is again a unit-circle pair. Reusing the parent's `chebyshevC_eval_add`,
  both `C_{mn}(z+w)` and `C_m(C_n(z+w))` equal `(zⁿ)ᵐ + (wⁿ)ᵐ`, i.e. `n ↦ C_n` is conjugate
  to the power monoid `n ↦ (·^n)` via `z ↦ z + z⁻¹`. This is the genuine structural insight.
- **Function.End is the right home.** `Function.End α` is `α → α` with `1 = id`, `f*g = f∘g`,
  so `map_one' = (C_1 = X = id)` and `map_mul'` is literally the nesting law; both close by
  `funext` + the eval lemma up to defeq.

## Built Items

- `chebyshevC_evalComp` — eval-map composition law `C_{mn}(x) = C_m(C_n(x))` (general CommRing).
- `chebyshevC_evalComp_comm` — commuting family `C_m(C_n x) = C_n(C_m x)`.
- `chebyshevC_evalComp_pow` — power-map conjugacy on the unit circle (reuses parent).
- `chebyshevEnd`, `chebyshevHom` — bundled `MonoidHom (ℤ →* Function.End (ZMod p))`.
- `chebyshevEnd_comm` — commuting family on endomorphisms over `ZMod p`.
- `chebyshevEnd_eval_pow` — conjugacy over the finite field 𝔽_p.
- File: `proofs/Proofs/DeMoivreOQ01OQ03OQ02.lean` (126 lines, 6 theorems, 2 defs, 0 sorries,
  0 axioms — `#print axioms` shows only propext/Classical.choice/Quot.sound).

## Mathlib Gaps

- None blocking. Mathlib has `C_mul`; the missing piece was the evaluation-map / monoid-hom
  packaging and the crypto-facing commuting-family/conjugacy statements, all built here.

---

## Dead Ends

- (none) — first session; tractable via direct reuse of Mathlib `C_mul` + parent identity.

---

## Session Log

### Session 2026-06-24 (Session 1) — Semigroup law over 𝔽_p [FRESH, COMPLETED]

**Outcome**: completed — verified, 0-axiom entry shipped.

Selected after stirling/fibonacci/arsinh candidates were taken by concurrent agents and
the Gram/Hadamard candidate proved too heavy (Mathlib lacks the PSD det inequality). This
problem was tractable because Mathlib's `C_mul` + the parent's `chebyshevC_eval_add` reduce
the work to packaging. Proved 6 theorems + 2 defs; built clean (21s host lake), 0 axioms.

**Next steps** (follow-ups, optional): assemble a concrete DH-style protocol object over 𝔽_p;
factor the hom through `(ZMod p)ˣ` to make the conjugacy `n ↦ C_n ≅ n ↦ (·^n)` explicit.
