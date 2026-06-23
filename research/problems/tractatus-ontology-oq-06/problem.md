# tractatus-ontology-oq-06 — World-Model Spectrum

## Question

What is the **right spectrum of world models** between the *free model* (full independence of elementary propositions) and *fully constrained models* (every assignment is filtered through a domain-specific predicate)? Concretely:

> Given the existing `WorldModel S` structure in `Proofs/TractatusOntology.lean` (lines 274–291), can we organize the space of inhabited `WorldModel`s into a **principled spectrum** — parameterized by the kind of constraint — so that the philosophical claims of the Tractatus (independence, compositionality, bivalence, expressibility) can be classified by *which point in the spectrum* preserves them?

The expected deliverable is a **classification scheme** rather than a single theorem: a hierarchy of world-model classes (free → conditional → modal → epistemic), together with which Tractarian results survive at each level. The companion task is to prove a **compatibility lemma** showing that the spectrum is well-ordered under a natural refinement preorder.

## Why it matters

1. **Philosophical precision.** TLP 2.061 ("States of affairs are independent of one another") is *not* a logical theorem — it is a constraint on the world model. Without a spectrum, one can only state that "independence holds in the free model"; one cannot quantify *how much* a given model deviates from the free model. The spectrum makes the philosophical commitment of the Tractatus precise as a **point in a parameterized design space**.

2. **Reusability.** A spectrum of WorldModels lets downstream formalizations (epistemic logic, dynamic logic, causal inference) plug into the same TLP machinery. The current file has only `freeModel` and `weatherModel` (one ad-hoc instance); a clear taxonomy invites systematic instances.

3. **Round-3 peer-review item #4.** The peer-review feedback explicitly asks for a "Model spectrum section" systematizing free vs constrained models with a table of which theorems hold in which models. This OQ is the concrete answer to that ask.

## Scope of S1 OBSERVE

This iteration is **documentation only** — no Lean code changes. We catalogue:

1. Existing models in the file and their position in the spectrum.
2. Candidate intermediate model classes drawn from Mathlib / standard model theory.
3. The natural refinement preorder on `WorldModel S` (when is one model a "constraint refinement" of another?).
4. Which existing theorems are spectrum-invariant vs spectrum-dependent.
5. Mathlib API that a future Lean implementation would lean on.

Subsequent sessions (S2+) will pick a concrete spectrum representation and prove the survival/failure pattern of each TLP theorem as a function of spectrum position.

## Anchoring file references

- `Proofs/TractatusOntology.lean:274–291` — `WorldModel S`, `freeModel`
- `Proofs/TractatusOntology.lean:560–649` — `ConstrainedWorld`, `weatherModel`, `constrained_independence_fails`, `weather_independence_fails`
- `Proofs/TractatusOntology.lean:319–331` — `truth_functional_compositionality_gen` (spectrum-invariant: holds for **every** `WorldModel`)
- `Proofs/TractatusOntology.lean:437` — `elementary_independence` (spectrum-dependent: requires `IndependentWorlds S`)
