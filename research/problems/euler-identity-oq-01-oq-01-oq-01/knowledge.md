# Knowledge Base: euler-identity-oq-01-oq-01-oq-01

Retrospective knowledge survey for the Lie-group-homomorphism extension of
Euler's formula. Backfilled 2026-05-16 from the verified gallery proof
shipped in #16705 (2026-05-07).

---

## 1. Mathematical Context

### Why this is a Lie-group statement

The unit circle `S¹ ⊆ ℂ` is the prototypical 1-dimensional compact connected
Lie group. Its Lie algebra is `Lie(S¹) = iℝ ⊆ ℂ` (the tangent space at 1,
identified with the imaginary axis). The Lie-group exponential map
`Lie(S¹) → S¹` is `iv ↦ exp(iv)`, which under the identification
`Lie(S¹) ≅ ℝ` becomes precisely `circleMap : t ↦ exp(it)`.

The general Lie-theoretic facts predict five properties of `circleMap`:

1. Homomorphism `(ℝ, +) → (S¹, ·)` (functoriality of `exp`).
2. Continuous (smooth, in fact).
3. Kernel discrete (rank-nullity for Lie groups: dim kernel + dim image = dim ℝ).
4. Image equals the connected component of the identity in S¹ (which is all of S¹).
5. Inverse-of-bijection: ℝ/kernel ≅ S¹ as Lie groups.

This OQ formalizes all five in Lean, with `kernel = 2π·ℤ` made explicit.

### Why `Multiplicative ℝ →* ℂˣ`?

Mathlib's `MonoidHom` is multiplicative-on-both-sides; to encode an
additive-domain homomorphism with a Mathlib bundled hom we use
`Multiplicative ℝ` (the type-level wrapper that turns `(ℝ, +)` into a
multiplicative monoid). The codomain `ℂˣ` (units of ℂ) is also
multiplicative. So:

- `circleHom : Multiplicative ℝ →* ℂˣ` is the most Mathlib-native
  packaging.
- The user-friendly form `circleMap_add` is the "untyped" statement,
  proved first, then lifted.

An alternative would have been `AddMonoidHom ℝ (Additive ℂˣ)` — semantically
equivalent but conventionally less common.

### Surjectivity onto S¹

The classical proof uses `arg z` (the angle): for any `z` with `‖z‖ = 1`,
take `t = arg z` and unwrap with `cos_arg` + `sin_arg` + `re_add_im`. The
Lean proof is six lines (§6 of the source file).

### De Moivre as a corollary

`(exp(it))^n = exp(int)` is immediate from the homomorphism + `Complex.exp_int_mul`
(`exp(nz) = (exp z)^n` for `n : ℤ`). No induction needed — the work is
absorbed into Mathlib's `exp_int_mul`.

---

## 2. Mathlib API Map (as used in the proof)

The proof imports 8 modules and consumes the following symbols:

| Symbol | Module (as cited in meta.json) | Current location at pin `2df2f0150c…` (v4.26.0) | Status |
|--------|--------------------------------|-------------------------------------------------|--------|
| `Complex.exp_add` | `Mathlib.Analysis.SpecialFunctions.Exp` | (re-exported via `Mathlib.Tactic`) | ✓ available |
| `Complex.exp_neg` | `Mathlib.Analysis.SpecialFunctions.Exp` | (re-exported) | ✓ available |
| `Complex.exp_eq_one_iff` | `Mathlib.Analysis.SpecialFunctions.Complex.Log` | `Mathlib/Analysis/SpecialFunctions/Complex/Log.lean:132` | ✓ verified |
| `Complex.exp_int_mul` | `Mathlib.Analysis.SpecialFunctions.Exp` | `Mathlib/Analysis/Complex/Exponential.lean` (Mathlib refactor) | ✓ re-exported |
| `Complex.norm_exp_ofReal_mul_I` | `Mathlib.Analysis.SpecialFunctions.Complex.Circle` | `Mathlib/Analysis/Complex/Trigonometric.lean:943` (Mathlib moved file) | ✓ re-exported; meta.json claim is stale but proof still verifies via transitive import |
| `Complex.cos_arg`, `Complex.sin_arg` | `Mathlib.Analysis.SpecialFunctions.Complex.Log` | `Mathlib/Analysis/SpecialFunctions/Complex/Log.lean` (used via `rw [log, exp_add_mul_I, …]` at L42) | ✓ available |
| `Complex.continuous_exp` | `Mathlib.Analysis.SpecialFunctions.Exp` | (re-exported) | ✓ available |
| `Complex.re_add_im` | `Mathlib.Data.Complex.Basic` | (foundational, re-exported) | ✓ available |

### Drift note (informational only)

Between the proof's `dateAdded: 2026-05-07` and this backfill (2026-05-16),
Mathlib moved `norm_exp_ofReal_mul_I` from `SpecialFunctions/Complex/Circle.lean`
into `Analysis/Complex/Trigonometric.lean`. The Lean file still verifies
because it imports `Mathlib.Tactic` and `Mathlib.Analysis.SpecialFunctions.Complex.Circle`,
which transitively re-export the symbol. **No proof edit is needed.** The
`mathlibDependencies[]` claim in `src/data/proofs/euler-identity-oq-01-oq-01-oq-01/meta.json`
points at the old module path; this is cosmetic metadata drift — auditor /
mechanic territory if anyone wants to refresh it.

### Mathlib name collision: `Mathlib.circleMap` vs `EulerIdentityOQ01OQ01OQ01.circleMap`

Mathlib has its own `circleMap` (in `Mathlib/Analysis/SpecialFunctions/Complex/CircleMap.lean`):

```lean
def circleMap (c : ℂ) (R : ℝ) : ℝ → ℂ := fun θ => c + R * exp (θ * I)
```

— the **contour-integration** parametrization (circle of radius `R` centered
at `c`). Our `EulerIdentityOQ01OQ01OQ01.circleMap t := exp(t * I)` is the
unit-circle restriction (`c = 0`, `R = 1`, applied form). Because it lives
in a different namespace, there is **no conflict**. If a future iteration
wanted to align with Mathlib, the recipe is

```lean
EulerIdentityOQ01OQ01OQ01.circleMap = Mathlib.circleMap 0 1
```

(modulo the application/uncurry difference). Not a needed refactor.

---

## 3. Proof Architecture (8 sections)

`proofs/Proofs/EulerIdentityOQ01OQ01OQ01.lean` is 241 LOC organized as:

| § | Content | Key lemmas |
|---|---------|------------|
| §1 | Definition of `circleMap` + basic algebra | `circleMap_zero`, `circleMap_add`, `circleMap_neg`, `circleMap_sub`, `circleMap_eq_cos_add_sin_I` |
| §2 | Image on unit circle | `norm_circleMap`, `circleMap_ne_zero` |
| §3 | `MonoidHom` packaging | `circleHom`, `circleHom_apply`, `circleMap_homomorphism` |
| §4 | Continuity | `continuous_circleMap`, `continuous_circleHom` |
| §5 | Kernel = 2π·ℤ | `circleMap_eq_one_iff` (the longest proof in the file — ~16 lines) |
| §6 | Surjectivity onto S¹ | `circleMap_surjective_unit_circle` |
| §7 | De Moivre | `circleMap_npow`, `circleMap_zpow` |
| §8 | Summary `main` + `#check`s | `main` (just an alias for `circleMap_eq_cos_add_sin_I`) |

### Pivotal one-liner

The connection to the parent OQ-01-OQ-01 file lives in §1:

```lean
theorem circleMap_eq_cos_add_sin_I (t : ℝ) :
    circleMap t = (Real.cos t : ℂ) + (Real.sin t : ℂ) * I := by
  unfold circleMap
  exact EulerIdentityOQ01OQ01.euler_formula t
```

So the entire OQ-01-OQ-01-OQ-01 file is a "wrapper layer" on top of the
parent axiom-free Euler formula, packaging it as Lie-group infrastructure.

---

## 4. What Was NOT Done (and Why)

### Did not use `Mathlib.Topology.Algebra.Group.Basic.expMapCircle` or similar

Mathlib's `expMapCircle` (in older versions) and the unit-circle subgroup
`Circle` (in newer versions) are existing instances. We could have proved
`circleHom = Subtype.val ∘ expMapCircle` or similar. We didn't because:

1. The OQ asks specifically about Euler's formula as a homomorphism — the
   pedagogical value is in writing the homomorphism out by hand from the
   parent axiom-free Euler formula, not in invoking Mathlib's blackbox.
2. The 241 LOC is self-contained — anyone reading the file can trace the
   logic end-to-end without descending into `expMapCircle` machinery.
3. A future refactor to align with Mathlib's `Circle` subgroup is open.

### Did not state the Pontryagin-dual statement

The full Lie-theoretic packaging would say `Hom(ℝ, S¹) ≅ S¹` (every
continuous group hom is of the form `t ↦ exp(iωt)` for some `ω ∈ ℝ`).
This requires uniqueness, which is a separate theorem (Ostrowski-style
character argument on the connected component of the identity). Not in
the OQ scope.

### Did not formalize ℝ/2πℤ ≅ S¹ as a topological quotient

`circleMap_eq_one_iff` gives the kernel and `circleMap_surjective_unit_circle`
gives the image. The first isomorphism theorem then *yields* the
topological quotient isomorphism `ℝ/2πℤ ≅ S¹`, but assembling it into a
`MulEquiv` plus a homeomorphism is a separate piece of API work. Plausible
follow-up if anyone opens a new OQ.

---

## 5. Possible Future Open Questions

(None currently in `meta.json`'s `openQuestions: []`. Recorded here only
as plausible continuations, not as commitments.)

1. **Q-α**: Package `ℝ/2πℤ ≅ S¹` as a `Mathlib.Topology.Algebra.MulHomeomorph`
   (continuous group iso with continuous inverse). LOC estimate ~40-80,
   tractability MODERATE.
2. **Q-β**: Prove that every continuous group hom `ℝ → S¹` is of the form
   `t ↦ exp(iωt)` (Pontryagin-dual statement, Ostrowski-style). LOC
   estimate ~100-150, tractability MODERATE+ (needs density of `ℚ` in ℝ
   + connectedness of `S¹`).
3. **Q-γ**: Align `EulerIdentityOQ01OQ01OQ01.circleMap` with Mathlib's
   own `circleMap` API and re-derive all six theorems via the alignment.
   LOC reduction estimate -40 LOC, tractability EASY.
4. **Q-δ**: De Moivre over the reals: `(cos t + i sin t)^n = cos(nt) + i sin(nt)`
   stated *purely in trig form* (without going through `Complex.exp`).
   Follows from §7 + `circleMap_eq_cos_add_sin_I` in one rewrite. LOC ~5,
   tractability EASY.

---

## 6. Bearer Audit at Current Mathlib Pin (`2df2f0150c…`, v4.26.0)

Spot-checks performed 2026-05-16 via `gh api` against the pinned SHA:

- ✓ `Mathlib/Analysis/SpecialFunctions/Complex/Circle.lean` exists at pin (size 10304 bytes).
- ✓ `Mathlib/Analysis/SpecialFunctions/Complex/Log.lean` exists at pin (size 20291 bytes).
- ✓ `Mathlib/Analysis/SpecialFunctions/Exp.lean` exists at pin (size 7880 bytes).
- ✓ `exp_eq_one_iff` is at `Log.lean:132`.
- ✓ `norm_exp_ofReal_mul_I` is at `Mathlib/Analysis/Complex/Trigonometric.lean:943`
  (relocated from `Circle.lean` between #16705 and now — re-exported, so the
  proof still verifies).
- ✓ `Mathlib/Analysis/SpecialFunctions/Complex/CircleMap.lean` exists at pin
  (Mathlib's own `circleMap` — different namespace, no conflict).

No bearer issues that affect the verified status of the proof.

---

## 7. Dead Ends / Non-Choices

None to record — the proof shipped first try in #16705. The retrospective
review (this document) found no surprises beyond the cosmetic
`mathlibDependencies[]` path drift noted in §2.

---

## 8. References

- Lean source: `proofs/Proofs/EulerIdentityOQ01OQ01OQ01.lean` (241 LOC)
- Gallery entry: `src/data/proofs/euler-identity-oq-01-oq-01-oq-01/`
- Shipping PR: [#16705](https://github.com/rjwalters/lean-genius/pull/16705) — "research(euler-identity-oq-01-oq-01-oq-01): Lie group exp ℝ → S¹ as continuous group hom"
- Enrichment PR: [#16767](https://github.com/rjwalters/lean-genius/pull/16767) — "Enrich euler-identity-oq-01-oq-01-oq-01: add 9 annotations + wire index.ts"
- Direct parent: `research/problems/euler-identity-oq-01-oq-01/` (and `proofs/Proofs/EulerIdentityOQ01OQ01.lean`, 142 LOC, also axiom-free)
- Lie-theoretic background: any standard Lie-group text — Knapp *Lie Groups Beyond an Introduction* §I.1, or Bröcker–tom Dieck *Representations of Compact Lie Groups* §I.2.
