import Mathlib

/-!
# Eliminating the ISC-count interface axioms (erdos-1036-oq-01-oq-01)

The gallery proof `Erdos1036OQ01.lean` ("Optimal Constant in Shelah's Coloring
Theorem") axiomatizes the *true ISC count* `numISCTrue G` — the number of
induced-subgraph **isomorphism classes** of a finite graph `G` — together with
the two structural bounds the development needs:

* `numISCTrue_le_pow : numISCTrue G ≤ 2 ^ n`  (at most `2^n` vertex subsets);
* `numISCTrue_pos   : 0 < numISCTrue G`        (the empty subgraph is one class).

The parent file flags these three axioms as "would be eliminated by ~200 lines of
Quotient type construction". This file discharges all three with an explicit,
self-contained construction in a fraction of that:

`numISCTrue G` is `Nat.card` of the quotient of `Finset V` by the setoid
`iscSetoid` that identifies two vertex subsets exactly when their induced
subgraphs are isomorphic.

## Why `Nat.card` (not `Fintype.card`)

The ~200-line estimate comes from the apparent need for a `Fintype`/`DecidableEq`
instance on the quotient, which would require *deciding graph isomorphism*.
Using `Nat.card` sidesteps that entirely: no `DecidableRel` is needed to **define**
`numISCTrue`, and the `≤ 2^n` bound is a one-liner because a quotient of a finite
type is never larger than the type itself (`Fintype.card_quotient_le`, reached via
a `classical` `DecidableRel`). Faithfulness is exact: the quotient's cardinality
*is* the number of isomorphism classes of induced subgraphs over all vertex
subsets.

## Status

BUILD-PENDING (Docker verification host down at authoring time; left UNREGISTERED
in `Proofs.lean` so an unverified file cannot break the aggregate build / auto-merge).
A future Docker-enabled session should `lake`-build this file, then add
`import Proofs.Erdos1036OQ01OQ01` to `Proofs.lean` and retarget the parent's three
interface axioms at these theorems.
-/

namespace Erdos1036OQ01OQ01

open SimpleGraph

variable {V : Type} [Fintype V] [DecidableEq V]

/-- ISC-equivalence on vertex subsets: `S` and `T` are equivalent when their
induced subgraphs `G[S]` and `G[T]` are isomorphic. Graph isomorphism is an
equivalence relation (reflexive via `Iso.refl`, symmetric via `Iso.symm`,
transitive via `Iso.trans`), so this is a genuine setoid on `Finset V` — the
setoid on "induced subgraph pairs". -/
def iscSetoid (G : SimpleGraph V) : Setoid (Finset V) where
  r S T := Nonempty (G.induce (↑S) ≃g G.induce (↑T))
  iseqv :=
    { refl := fun _ => ⟨SimpleGraph.Iso.refl _⟩
      symm := fun ⟨e⟩ => ⟨e.symm⟩
      trans := fun ⟨e⟩ ⟨f⟩ => ⟨e.trans f⟩ }

/-- The true ISC count: the number of induced-subgraph isomorphism classes,
realised as the cardinality of the quotient of `Finset V` by `iscSetoid`.

This is the definitional replacement for the parent's `axiom numISCTrue`. -/
noncomputable def numISCTrue (G : SimpleGraph V) : ℕ :=
  Nat.card (Quotient (iscSetoid G))

/-- **Interface axiom 1 discharged** (`numISCTrue_le_pow`).
There are only `2^n` vertex subsets, so there are at most `2^n` isomorphism
classes: the quotient is no larger than `Finset V`. -/
theorem numISCTrue_le_pow (G : SimpleGraph V) :
    numISCTrue G ≤ 2 ^ Fintype.card V := by
  classical
  show Nat.card (Quotient (iscSetoid G)) ≤ 2 ^ Fintype.card V
  rw [Nat.card_eq_fintype_card]
  calc Fintype.card (Quotient (iscSetoid G))
        ≤ Fintype.card (Finset V) := Fintype.card_quotient_le _
    _ = 2 ^ Fintype.card V := Fintype.card_finset

/-- **Interface axiom 2 discharged** (`numISCTrue_pos`).
The empty subset gives one isomorphism class, so the quotient is nonempty. -/
theorem numISCTrue_pos (G : SimpleGraph V) : 0 < numISCTrue G := by
  show 0 < Nat.card (Quotient (iscSetoid G))
  haveI : Nonempty (Quotient (iscSetoid G)) := ⟨Quotient.mk _ (∅ : Finset V)⟩
  -- `Finite (Quotient (iscSetoid G))` is found automatically from `Finite (Finset V)`.
  exact Nat.card_pos

end Erdos1036OQ01OQ01
