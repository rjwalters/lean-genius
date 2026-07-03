/-
Copyright (c) 2026 RJ Walters. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RJ Walters
-/
import Proofs.SpernerSimplicialBridge
import Mathlib.Order.KonigLemma

/-
# Sperner's lemma on infinite towers via Kőnig's infinity lemma

The parent file `SpernerSimplicialBridge.lean` proves Sperner's lemma for a single
*finite* set `topCells : Finset (Finset E)` of top simplices satisfying purity and
the pseudomanifold condition (`Sperner.SimplicialComplex.exists_panchromatic`). The
follow-up `SpernerSimplicialBridgeOQ02.lean` reconciled this with Mathlib's
`Geometry.SimplicialComplex`. Both are inherently *finite* statements — the
door-counting parity argument is a counting argument over a finite door graph.

This file answers the next open question:

> Does the finite panchromatic-cell existence extend to an *infinite* limit
> statement via a compactness argument (Kőnig's lemma / inverse limits)?

## The construction

An infinite simplicial object is modelled as a **tower** indexed by `ℕ`: for each
level `n` a finite pseudomanifold complex `topCells n`, all sharing one global
colouring `c` and each satisfying its own odd-boundary hypothesis. The finite
bridge theorem then guarantees that the set

  `PanCell n := { panchromatic cells of level n }`

is **nonempty** (finite Sperner) and **finite** (it is a subtype of the finite
cell type). A tower additionally carries coherent *restriction maps*
`π : PanCell j → PanCell i` for `i ≤ j` (the combinatorial content of "the level-`j`
complex refines the level-`i` complex").

The compactness step is exactly Kőnig's infinity lemma in its inverse-system form,
`exists_seq_forall_proj_of_forall_finite`:

* `α 0 = PanCell 0` is finite,
* every `α i = PanCell i` is nonempty,

so there is a **coherent thread** `f : (n : ℕ) → PanCell n` with `π hij (f j) = f i`
for all `i ≤ j`. This is a genuine limit object: it selects one panchromatic cell at
*every* level of the tower, compatibly with the restriction maps — the honest
infinite analogue of the finite existence theorem. Note Kőnig requires only per-level
nonemptiness and finiteness of level `0`; the restriction maps need not be surjective.

## Main results

* `Sperner.SimplicialComplex.nonempty_panCell` — each level of a tower has at least
  one panchromatic cell (a direct corollary of the finite bridge).
* `Sperner.SimplicialComplex.exists_coherent_panchromatic_thread` — Kőnig's lemma:
  a coherent thread of panchromatic cells through the whole tower.
* `Sperner.SimplicialComplex.exists_coherent_panchromatic_cells` — the same, with
  the panchromaticity of each thread cell exposed explicitly.

## References

* [D. Kőnig, *Über eine Schlussweise aus dem Endlichen ins Unendliche*]
* [M. De Longueville, *A Course in Topological Combinatorics*]

## Tags

Sperner, simplicial complex, pseudomanifold, bridge, Kőnig's lemma, compactness,
inverse limit, infinite
-/

set_option maxHeartbeats 800000

namespace Sperner.SimplicialComplex

open Finset

section InfiniteTower

variable {E : Type} [DecidableEq E] [LinearOrder E] {d : ℕ}

/-- The vertex-enumeration function for the level-`n` cells of a tower. This is the
same `vertexEnum`-based labelling the finite bridge consumes, packaged as a function
of the level `n`. -/
noncomputable def levelVertex (topCells : ℕ → Finset (Finset E))
    (hcard : ∀ n, ∀ s ∈ topCells n, s.card = d + 1) (n : ℕ) :
    { s : Finset E // s ∈ topCells n } → Fin (d + 1) → E :=
  fun σ => vertexEnum σ.1 (hcard n σ.1 σ.2)

/-- The type of **panchromatic cells at level `n`** of a tower: cells of the
level-`n` complex whose `d + 1` vertices receive all `d + 1` colours. -/
def PanCell (topCells : ℕ → Finset (Finset E))
    (hcard : ∀ n, ∀ s ∈ topCells n, s.card = d + 1)
    (c : E → Fin (d + 1)) (n : ℕ) : Type :=
  { σ : { s : Finset E // s ∈ topCells n } //
      Sperner.IsPanchromatic (levelVertex topCells hcard n) c σ }

/-- Every level of a tower has only finitely many panchromatic cells: `PanCell n` is
a subtype of the finite cell type `{ s // s ∈ topCells n }`. -/
instance instFinitePanCell (topCells : ℕ → Finset (Finset E))
    (hcard : ∀ n, ∀ s ∈ topCells n, s.card = d + 1)
    (c : E → Fin (d + 1)) (n : ℕ) : Finite (PanCell topCells hcard c n) := by
  unfold PanCell
  infer_instance

/-- **Finite Sperner ⟹ every tower level has a panchromatic cell.**

For each level `n`, if the finite complex `topCells n` is pure, pseudomanifold, and
has an odd boundary door count under the global colouring `c`, then it contains at
least one panchromatic cell. This is the per-level input to the compactness
argument. -/
theorem nonempty_panCell (topCells : ℕ → Finset (Finset E))
    (hcard : ∀ n, ∀ s ∈ topCells n, s.card = d + 1)
    (hpseudo : ∀ n, ∀ f : Finset E, f.card = d →
      ((topCells n).filter (fun s => f ⊆ s)).card ≤ 2)
    (c : E → Fin (d + 1))
    (hbdry : ∀ n, Odd (Finset.univ.filter
      (fun p : { s : Finset E // s ∈ topCells n } × Fin (d + 1) =>
        Sperner.IsDoor (levelVertex topCells hcard n) c p.1 p.2 ∧
        adjFn (topCells n) (hcard n) p.1 p.2 = none)).card)
    (n : ℕ) : Nonempty (PanCell topCells hcard c n) := by
  obtain ⟨σ, hσ⟩ := exists_panchromatic (topCells n) (hcard n) (hpseudo n) c (hbdry n)
  exact ⟨⟨σ, hσ⟩⟩

/-- **Sperner's lemma on an infinite tower (Kőnig form).**

Let `topCells : ℕ → Finset (Finset E)` be a tower of finite pseudomanifold complexes,
all coloured by a single `c : E → Fin (d + 1)`, each with an odd boundary door count
(so each level has a panchromatic cell by the finite bridge). Suppose the tower is
equipped with coherent restriction maps `π hij : PanCell j → PanCell i` for `i ≤ j`
(functorial: `π` respects reflexivity and composition).

Then there is a **coherent thread** `f : (n : ℕ) → PanCell n` selecting one
panchromatic cell at every level, compatibly with the restriction maps:
`π hij (f j) = f i` for all `i ≤ j`.

The proof is a direct application of Kőnig's infinity lemma
(`exists_seq_forall_proj_of_forall_finite`): each `PanCell n` is finite and nonempty,
which is precisely the hypothesis Kőnig needs. -/
theorem exists_coherent_panchromatic_thread (topCells : ℕ → Finset (Finset E))
    (hcard : ∀ n, ∀ s ∈ topCells n, s.card = d + 1)
    (hpseudo : ∀ n, ∀ f : Finset E, f.card = d →
      ((topCells n).filter (fun s => f ⊆ s)).card ≤ 2)
    (c : E → Fin (d + 1))
    (hbdry : ∀ n, Odd (Finset.univ.filter
      (fun p : { s : Finset E // s ∈ topCells n } × Fin (d + 1) =>
        Sperner.IsDoor (levelVertex topCells hcard n) c p.1 p.2 ∧
        adjFn (topCells n) (hcard n) p.1 p.2 = none)).card)
    (π : {i j : ℕ} → i ≤ j → PanCell topCells hcard c j → PanCell topCells hcard c i)
    (π_refl : ∀ ⦃i⦄ (a : PanCell topCells hcard c i), π le_rfl a = a)
    (π_trans : ∀ ⦃i j k⦄ (hij : i ≤ j) (hjk : j ≤ k) (a : PanCell topCells hcard c k),
      π hij (π hjk a) = π (hij.trans hjk) a) :
    ∃ f : (n : ℕ) → PanCell topCells hcard c n,
      ∀ ⦃i j⦄ (hij : i ≤ j), π hij (f j) = f i := by
  -- Each level is finite (instance) and nonempty (finite Sperner).
  haveI : ∀ n, Nonempty (PanCell topCells hcard c n) :=
    fun n => nonempty_panCell topCells hcard hpseudo c hbdry n
  -- Kőnig's infinity lemma for inverse systems: fibers are finite because every
  -- level is a finite type.
  exact exists_seq_forall_proj_of_forall_finite π π_refl π_trans
    (fun _ _ => Set.toFinite _)

/-- **Coherent thread of panchromatic cells, panchromaticity exposed.**

The same conclusion as `exists_coherent_panchromatic_thread`, but repackaged so the
panchromaticity of each selected cell is stated explicitly alongside the coherence of
the thread. -/
theorem exists_coherent_panchromatic_cells (topCells : ℕ → Finset (Finset E))
    (hcard : ∀ n, ∀ s ∈ topCells n, s.card = d + 1)
    (hpseudo : ∀ n, ∀ f : Finset E, f.card = d →
      ((topCells n).filter (fun s => f ⊆ s)).card ≤ 2)
    (c : E → Fin (d + 1))
    (hbdry : ∀ n, Odd (Finset.univ.filter
      (fun p : { s : Finset E // s ∈ topCells n } × Fin (d + 1) =>
        Sperner.IsDoor (levelVertex topCells hcard n) c p.1 p.2 ∧
        adjFn (topCells n) (hcard n) p.1 p.2 = none)).card)
    (π : {i j : ℕ} → i ≤ j → PanCell topCells hcard c j → PanCell topCells hcard c i)
    (π_refl : ∀ ⦃i⦄ (a : PanCell topCells hcard c i), π le_rfl a = a)
    (π_trans : ∀ ⦃i j k⦄ (hij : i ≤ j) (hjk : j ≤ k) (a : PanCell topCells hcard c k),
      π hij (π hjk a) = π (hij.trans hjk) a) :
    ∃ f : (n : ℕ) → PanCell topCells hcard c n,
      (∀ n, Sperner.IsPanchromatic (levelVertex topCells hcard n) c (f n).1) ∧
      ∀ ⦃i j⦄ (hij : i ≤ j), π hij (f j) = f i := by
  obtain ⟨f, hf⟩ :=
    exists_coherent_panchromatic_thread topCells hcard hpseudo c hbdry π π_refl π_trans
  exact ⟨f, fun n => (f n).2, hf⟩

end InfiniteTower

end Sperner.SimplicialComplex
