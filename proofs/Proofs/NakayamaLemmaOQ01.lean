import Mathlib.RingTheory.Nakayama
import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
import Mathlib.Tactic

/-
# Nakayama's Lemma — the local-ring forms and lifting of generators

## What This Proves

Nakayama's lemma is the workhorse of commutative algebra. Mathlib proves the
general *Jacobson radical* versions (Stacks 00DV statements (2), (4), (8)) in
`Mathlib/RingTheory/Nakayama.lean`. What practitioners actually quote, however,
is the **local-ring** specialization and its corollaries about generators. This
file derives those textbook forms and packages them as a self-contained unit.

Throughout, `R` is a commutative (local) ring, `M` an `R`-module, `𝔪` the
maximal ideal of `R`, and `N ≤ M` a finitely generated submodule.

* **Jacobson form** (`nakayama_jacobson`). If `N` is finitely generated,
  `N ≤ I • N`, and `I ≤ jacobson ⊥`, then `N = 0`. This is the Mathlib headline
  `Submodule.eq_bot_of_le_smul_of_le_jacobson_bot`, restated as the baseline.

* **Local form** (`nakayama_local`). Over a local ring, if `N` is finitely
  generated and `N ≤ 𝔪 • N`, then `N = 0`. The single most-cited statement of
  the lemma — obtained from the Jacobson form because `𝔪 ≤ jacobson ⊥` in a
  local ring.

* **Vanishing form** (`nakayama_local_top`, `nakayama_local_top_ne`). For a
  finitely generated module `M`, `𝔪 • M = M` forces `M = 0`; contrapositively,
  a nonzero finitely generated module satisfies `𝔪 • M ≠ M`. (This is the form
  behind "the cotangent space `M / 𝔪M` detects nonvanishing".)

* **Generators corollary** (`nakayama_generators`). Over a local ring, if `N` is
  finitely generated and `N ≤ span t + 𝔪 • N`, then already `N ≤ span t`. In
  words: elements that generate `N` *modulo* `𝔪N` generate `N` on the nose.

* **Lifting generators** (`nakayama_span_of_span_quotient`). For finitely
  generated `M`, if a set `t` spans `M` modulo `𝔪M`, then `t` spans `M`. This is
  the statement used to lift a basis of the `R/𝔪`-vector space `M/𝔪M` to a
  generating set of `M` (the source of "minimal number of generators =
  `dim_{R/𝔪} M/𝔪M`").

## Relation to Mathlib

Mathlib's `Nakayama.lean` proves the general Jacobson-radical statements but
states none of them for the maximal ideal of a local ring, and offers no
ready-made "generators lift from `M/𝔪M`" corollary. Those specializations —
the forms every commutative-algebra course states — are what this file
contributes, by combining the Jacobson statements with
`IsLocalRing.maximalIdeal_le_jacobson`. A `grep` of `proofs/Proofs` for
`nakayama`, `jacobson`, or `maximalIdeal` returns no prior formalization; the
gallery had only incidental prose mentions (Murnaghan–Nakayama, Nullstellensatz).

This file is `0`-axiom (only `propext` / `Classical.choice` / `Quot.sound`; no
`native_decide`).
-/

namespace NakayamaLemma

open Submodule IsLocalRing

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

/-- **Nakayama's lemma, Jacobson form** (Stacks 00DV (2)). A finitely generated
submodule `N` with `N ≤ I • N` and `I ≤ jacobson ⊥` is trivial. This is the
Mathlib headline `Submodule.eq_bot_of_le_smul_of_le_jacobson_bot`, restated as
the baseline for the local-ring specializations below. -/
theorem nakayama_jacobson (I : Ideal R) (N : Submodule R M) (hN : N.FG)
    (hIN : N ≤ I • N) (hIjac : I ≤ Ideal.jacobson ⊥) : N = ⊥ :=
  Submodule.eq_bot_of_le_smul_of_le_jacobson_bot I N hN hIN hIjac

variable [IsLocalRing R]

/-- **Nakayama's lemma, local form.** Over a local ring with maximal ideal `𝔪`,
a finitely generated submodule `N` with `N ≤ 𝔪 • N` vanishes. Derived from the
Jacobson form via `𝔪 ≤ jacobson ⊥`. -/
theorem nakayama_local (N : Submodule R M) (hN : N.FG)
    (hIN : N ≤ maximalIdeal R • N) : N = ⊥ :=
  nakayama_jacobson (maximalIdeal R) N hN hIN (maximalIdeal_le_jacobson ⊥)

/-- **Nakayama's lemma, vanishing form.** A finitely generated module `M` with
`𝔪 • M = M` (equivalently `M ≤ 𝔪 • M`) is the zero module. -/
theorem nakayama_local_top [Module.Finite R M]
    (h : (⊤ : Submodule R M) ≤ maximalIdeal R • ⊤) : Subsingleton M := by
  have htop : (⊤ : Submodule R M) = ⊥ := nakayama_local ⊤ Module.Finite.fg_top h
  refine ⟨fun a b => ?_⟩
  have ha : a ∈ (⊥ : Submodule R M) := htop ▸ Submodule.mem_top
  have hb : b ∈ (⊥ : Submodule R M) := htop ▸ Submodule.mem_top
  rw [Submodule.mem_bot] at ha hb
  rw [ha, hb]

/-- **Nakayama's lemma, nonvanishing form.** A nonzero finitely generated module
satisfies `𝔪 • M ≠ M`: the quotient `M / 𝔪M` is itself nonzero. -/
theorem nakayama_local_top_ne [Module.Finite R M] [Nontrivial M] :
    maximalIdeal R • (⊤ : Submodule R M) ≠ ⊤ := by
  intro h
  exact not_subsingleton M (nakayama_local_top (le_of_eq h.symm))

/-- **Nakayama's lemma, generators corollary.** Over a local ring, if the
finitely generated submodule `N` satisfies `N ≤ span t + 𝔪 • N`, then already
`N ≤ span t`: generators modulo `𝔪N` are generators of `N`. -/
theorem nakayama_generators {N : Submodule R M} {t : Set M} (hN : N.FG)
    (h : N ≤ Submodule.span R t ⊔ maximalIdeal R • N) :
    N ≤ Submodule.span R t :=
  Submodule.le_of_le_smul_of_le_jacobson_bot hN (maximalIdeal_le_jacobson ⊥) h

/-- **Nakayama's lemma, lifting a generating set.** For a finitely generated
module `M`, if `t` spans `M` modulo `𝔪M`, then `t` spans `M`. This lifts a
basis of the residue vector space `M / 𝔪M` to a generating set of `M`. -/
theorem nakayama_span_of_span_quotient [Module.Finite R M] {t : Set M}
    (h : (⊤ : Submodule R M) ≤ Submodule.span R t ⊔ maximalIdeal R • ⊤) :
    Submodule.span R t = ⊤ :=
  top_le_iff.mp (nakayama_generators Module.Finite.fg_top h)

end NakayamaLemma
