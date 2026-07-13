# Knowledge — World-Model Spectrum (tractatus-ontology-oq-06)

## 1. The existing `WorldModel` structure

```lean
structure WorldModel (S : Type) where
  W        : Type
  holds    : W → S → Prop
  nonempty : Nonempty W
```

This is **maximally general**: any `WorldModel` is determined by an arbitrary type `W` of worlds and an arbitrary relation `holds : W → S → Prop`. The spectrum question asks: which subclasses of this structure carry distinctive philosophical content?

### Existing inhabitants

| Model | Worlds (`W`) | `holds` | Independence? |
|---|---|---|---|
| `freeModel S` | `S → Prop` | `fun w s => w s` | Yes (trivially) |
| `weatherModel` | `{w : WeatherFacts → Prop // w .rain → w .clouds}` | `fun w s => w.val s` | No (rain ⇒ clouds) |
| `ConstrainedWorld S a b` (impl chassis) | `{w : S → Prop // w a → w b}` | (via `toWorld`) | No when `a ≠ b` |

Both constrained examples are **subset-quotient** models: they realize `W` as `{w : S → Prop // φ w}` for some predicate `φ`. This is *not* an accident — it is the natural shape of a "constrained free model".

## 2. Proposed spectrum (four levels)

We propose a four-tier classification. Each tier is a refinement of the previous one: more constraint → fewer worlds → fewer independent propositions.

### Tier 0 — Free model
- `W = S → Prop`, `holds = application`.
- Every Boolean assignment is a world.
- All Tractarian theorems hold; `IndependentWorlds` is automatic.
- Cardinality: `|W| = 2^|S|` (when `S` is finite).

### Tier 1 — Predicate-constrained free model
- `W = {w : S → Prop // φ w}` for some `φ : (S → Prop) → Prop`.
- `holds = fun w s => w.val s`.
- Worlds are still Boolean assignments, but only those satisfying `φ`.
- Special case Tier 1a — **Horn-constrained**: `φ w = ∀ i, head_i w → body_i w` (finite list of implications). Captures `weatherModel`, `ConstrainedWorld`.
- Special case Tier 1b — **Equivalence-constrained**: `φ w = ∀ i, w (a_i) ↔ w (b_i)`. Models gauge symmetries / state identifications.
- Special case Tier 1c — **Cardinality-constrained**: `φ w = (Finset.filter (·) ...).card = k`. Models "exactly k facts obtain" assumptions.

### Tier 2 — Multi-world models (Kripke-style)
- `W = Σ p : Possibility, S → Prop` (or arbitrary indexed type), plus accessibility relation `R : W → W → Prop`.
- Captures modal, temporal, epistemic logics. The `WorldModel` structure as given **already supports this** — `W` is opaque, so the accessibility is a separate piece of data layered on top.
- Independence is now world-relative: `w` is independent from `w'` iff there is no `R`-path between them constraining their assignments.
- This is **out of scope** for the basic OQ but flagged as a future extension.

### Tier 3 — Quotient / equivalence-class models
- Worlds are equivalence classes under some relation `~` on `S → Prop`.
- Captures "indistinguishable worlds" (e.g. observational equivalence, behavioral equivalence in epistemic logic).
- Equivalent to Tier 1 with `φ` chosen to pick a single representative per class, but the abstraction is philosophically distinct.

## 3. Natural refinement preorder

There is a candidate **refinement preorder** `≤` on `WorldModel S`:

> `M ≤ M'` if there is a function `f : M.W → M'.W` such that for every `w : M.W` and every `s : S`, `M.holds w s ↔ M'.holds (f w) s`.

Equivalently, every world of `M` factors through a world of `M'` with the same Boolean profile. Under this preorder:

- `freeModel S` is the **terminal object**: every `WorldModel S` injects into it (send `w` to `fun s => M.holds w s`).
- Constrained models sit below `freeModel`.
- The relation captures "constraint addition": going down the order adds constraints.

Two open conjectures (to be addressed in later iterations):

- **(R1)** `IsTautologyM`-preservation is **upward-closed** along `≤`: if `M ≤ M'` and `p` is a tautology in `M'`, then `p` is a tautology in `M`. *(Intuition: fewer worlds ⇒ more tautologies.)*
- **(R2)** `evalM_free_eq_eval` generalizes: for every `M ≤ freeModel S`, `evalM M p w = p.eval (fun s => M.holds w s)`. *(Already true definitionally for Tier 1 models; lemma would extract this.)*

## 4. Theorem-survival table

Which existing theorems hold at which tier?

| Theorem | T0 free | T1 horn | T1 equiv | T2 Kripke | T3 quotient |
|---|---|---|---|---|---|
| `truth_functional_compositionality_gen` | ✓ | ✓ | ✓ | ✓ | ✓ |
| `tautology_is_world_invariant` | ✓ | ✓ | ✓ | ✓ | ✓ |
| `elementary_independence` | ✓ | ✗ in general | ✗ when class > 1 | ✗ | depends |
| `nand_expresses_neg/conj` | ✓ | ✓ | ✓ | ✓ | ✓ |
| `evalM_free_eq_eval` | ✓ | (via embedding) | (via embedding) | n/a | n/a |
| `constrained_independence_fails` (with `a ≠ b`) | n/a | constructive witness | constructive witness | n/a | n/a |

Key observation: **compositionality and tautology-invariance are spectrum-invariant** (they only use the `holds`/`evalM` recursion), while **independence is the discriminating feature** — it pins down the free model uniquely (among Tier 0–1) up to bijection.

## 5. Mathlib-relevant API for future ACT

The following Mathlib pieces are likely useful for any concrete spectrum implementation:

1. **`Set.Subtype` / `Subtype`** — for predicate-constrained Tier 1 models.
2. **`Filter` and `Filter.OrderHom`** — the refinement preorder above is morally a filter refinement; if recast in terms of "set of worlds", Mathlib's `Filter` API gives a ready-made lattice.
3. **`Relation.ReflTransGen`** — for Tier 2 Kripke accessibility.
4. **`Quotient` / `Setoid`** — for Tier 3.
5. **`Decidable` instances** — for finite `S`, every `φ` over `S → Bool` is decidable; Tier 1 models inherit `Fintype W` when `S` is finite, which enables `native_decide` checks of theorem-survival on small worked examples.
6. **`Lattice`** — `WorldModel S` under the refinement preorder may form a lattice (meet = pointwise intersection of constraints, join = pointwise union); needs verification but suggests a clean S2 result.

## 6. Three candidate S2 deliverables

In rough order of tractability:

- **S2-α (Easy)** Formal definition of `Refines : WorldModel S → WorldModel S → Prop` and proof that `freeModel S` is the maximum element (every model refines into it).

- **S2-β (Medium)** Define `HornModel S : List (S × S) → WorldModel S` (a generic Tier 1a model), prove that `ConstrainedWorld S a b ≃ HornModel S [(a, b)]`, and re-express `weatherModel` as `HornModel WeatherFacts [(.rain, .clouds)]`. Builds reusable infrastructure.

- **S2-γ (Hard)** Prove the **uniqueness of `freeModel`** characterization: any inhabited `WorldModel S` satisfying `IndependentWorlds`-style independence at all states of affairs is uniquely determined up to a refinement-isomorphism with `freeModel S`. This would be the spectrum's first non-trivial Main Result.

S2-α is the recommended starting point: ~30–60 lines, no new Mathlib dependencies, directly addresses the OQ.

## 7. References

- TLP 2.061, 2.062 — independence of states of affairs (motivates the free model).
- TLP 5.5, 5.501 — truth-functional generation; compositionality.
- Wittgenstein commentary on logical atomism as a meta-claim about assignment structure (rather than a logical theorem) anticipates the spectrum framing of independence as a model-choice.
- `mathlib4` `Mathlib.Order.RelClasses` — preorder / lattice machinery.
- `mathlib4` `Mathlib.Logic.Equiv.Defs` — equivalence/bijection for the "up to refinement" claims.
- Internal: peer-review-round-3 notes (`memory/project_tractatus_review.md`) request a "Model spectrum section".
