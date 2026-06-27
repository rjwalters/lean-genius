import Mathlib.Combinatorics.Pigeonhole
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Int.ModEq
import Mathlib.Data.Finset.Card
import Mathlib.Tactic

/-
# Blichfeldt's Generalization of Minkowski's Fundamental Theorem (OQ-03)

## What This Proves

Blichfeldt's theorem (1914) is the measure-theoretic engine behind Minkowski's
Fundamental Theorem. In its basic form it states:

> If `L ⊆ ℝⁿ` is a lattice with fundamental domain of covolume `V`, and `s ⊆ ℝⁿ`
> is measurable with `vol(s) > V`, then `s` contains two distinct points whose
> difference lies in `L`.

Mathlib already provides this `m = 1` case as
`MeasureTheory.exists_pair_mem_lattice_not_disjoint_vadd`.

**Blichfeldt's *generalization*** (the content of this open problem) sharpens the
volume hypothesis to a multiple of the covolume and produces *many* points:

> If `vol(s) > m · V` for a positive integer `m`, then `s` contains `m + 1`
> distinct points `x₀, …, x_m` that are *pairwise congruent modulo `L`*, i.e.
> `xᵢ − xⱼ ∈ L` for all `i, j`.

The measure-theoretic proof replaces the disjointness argument of the `m = 1`
case by a *covering-multiplicity* argument: the average number of lattice
translates of `s` covering a point of the fundamental domain equals
`vol(s) / V > m`, so some point is covered at least `m + 1` times, yielding the
`m + 1` congruent points.

## This File: the Discrete Pigeonhole Core

The combinatorial heart of Blichfeldt's generalization — the step that the
measure-theoretic averaging argument ultimately reduces to — is a clean
pigeonhole statement about the quotient by a finite-index subgroup, with **no**
measure theory required. We formalize it in full generality and instantiate it
on the integer lattice.

The reduction is faithful: discretising `ℝⁿ` along a sublattice `qℤⁿ ⊆ L` turns
"covolume" into the index `[L : qℤⁿ]` and "many points of large volume" into
"many lattice representatives", and the geometric conclusion `xᵢ − xⱼ ∈ L`
becomes congruence in the finite quotient. The general `m`-fold pigeonhole below
is exactly what powers that reduction.

## Main results

* `BlichfeldtGeneral.exists_card_lt_pairwise_sub_mem` — the general `m`-fold
  Blichfeldt pigeonhole for an arbitrary finite-index subgroup of an abelian
  group: more than `[G : L] · m` points force an `(m+1)`-point pairwise-congruent
  subfamily.
* `BlichfeldtGeneral.exists_pair_sub_mem` — the classical `m = 1` Blichfeldt
  principle as a corollary.
* `BlichfeldtGeneral.exists_card_lt_modEq` — the integer-lattice instantiation:
  more than `q · m` integers contain `m + 1` that are pairwise congruent mod `q`.

## Status

- [x] General `m`-fold Blichfeldt pigeonhole (abstract finite-index subgroup)
- [x] Classical `m = 1` Blichfeldt principle (corollary)
- [x] Integer-lattice (`ℤ`, modulus `q`) instantiation
- [x] 0 sorries, 0 axioms — fully machine-checked
- Measure-theoretic statement over `ℝⁿ` is described above as motivation; its
  formalization (via `IsAddFundamentalDomain.lintegral_eq_tsum`) is future work.
-/

open Finset

namespace BlichfeldtGeneral

variable {G : Type*} [AddCommGroup G] {L : AddSubgroup G}

/-- **Blichfeldt's generalization (discrete core).**

Let `L` be a finite-index subgroup of an abelian group `G`, so the quotient
`G ⧸ L` is finite, and let `s` be a finite set of `G` with strictly more than
`[G : L] · m` elements. Then `s` contains a subfamily `t` of more than `m`
elements that is *pairwise congruent modulo `L`*: any two of its members differ
by an element of `L`.

This is the exact combinatorial content of Blichfeldt's theorem with the volume
hypothesis `vol(s) > m · covolume`: the role of the fundamental domain is played
by the quotient `G ⧸ L`, and "covered `m + 1` times" becomes "a fiber of the
quotient map of size `> m`". -/
theorem exists_card_lt_pairwise_sub_mem [Fintype (G ⧸ L)] {s : Finset G} {m : ℕ}
    (h : Fintype.card (G ⧸ L) * m < s.card) :
    ∃ t ⊆ s, m < t.card ∧ ∀ x ∈ t, ∀ y ∈ t, x - y ∈ L := by
  classical
  -- Pigeonhole on the quotient map `G → G ⧸ L`: some residue class is hit
  -- more than `m` times.
  obtain ⟨y, -, hy⟩ :=
    Finset.exists_lt_card_fiber_of_mul_lt_card_of_maps_to (n := m)
      (s := s) (t := (Finset.univ : Finset (G ⧸ L)))
      (f := fun x => (QuotientAddGroup.mk x : G ⧸ L))
      (fun a _ => Finset.mem_univ _)
      (by simpa [Finset.card_univ] using h)
  -- That fiber is the desired pairwise-congruent subfamily. We let the set be
  -- inferred from `hy` so its `DecidablePred` instance matches exactly.
  refine ⟨_, Finset.filter_subset _ _, hy, ?_⟩
  intro x hx z hz
  simp only [Finset.mem_filter] at hx hz
  have hxz : (QuotientAddGroup.mk x : G ⧸ L) = QuotientAddGroup.mk z :=
    hx.2.trans hz.2.symm
  rwa [QuotientAddGroup.eq_iff_sub_mem] at hxz

/-- **Classical Blichfeldt principle** (`m = 1`).

If a finite set `s` of an abelian group has strictly more elements than the index
`[G : L]`, then `s` contains two *distinct* points whose difference lies in `L`.
This is the discrete form of Mathlib's
`MeasureTheory.exists_pair_mem_lattice_not_disjoint_vadd`. -/
theorem exists_pair_sub_mem [Fintype (G ⧸ L)] {s : Finset G}
    (h : Fintype.card (G ⧸ L) < s.card) :
    ∃ x ∈ s, ∃ y ∈ s, x ≠ y ∧ x - y ∈ L := by
  obtain ⟨t, hts, hcard, hpair⟩ :=
    exists_card_lt_pairwise_sub_mem (L := L) (m := 1) (by simpa using h)
  obtain ⟨x, hx, y, hy, hxy⟩ := Finset.one_lt_card.mp hcard
  exact ⟨x, hts hx, y, hts hy, hxy, hpair x hx y hy⟩

/-- **Integer-lattice instantiation.**

Among strictly more than `q · m` integers there are `m + 1` that are pairwise
congruent modulo `q`. This is Blichfeldt's generalization for the rank-one
lattice `qℤ ⊆ ℤ`, where the covolume is `q = [ℤ : qℤ]`. -/
theorem exists_card_lt_modEq {q m : ℕ} [NeZero q] {s : Finset ℤ}
    (h : q * m < s.card) :
    ∃ t ⊆ s, m < t.card ∧ ∀ x ∈ t, ∀ y ∈ t, x ≡ y [ZMOD (q : ℤ)] := by
  classical
  obtain ⟨y, -, hy⟩ :=
    Finset.exists_lt_card_fiber_of_mul_lt_card_of_maps_to (n := m)
      (s := s) (t := (Finset.univ : Finset (ZMod q)))
      (f := fun x => (x : ZMod q))
      (fun a _ => Finset.mem_univ _)
      (by simpa [Finset.card_univ, ZMod.card] using h)
  refine ⟨_, Finset.filter_subset _ _, hy, ?_⟩
  intro x hx z hz
  simp only [Finset.mem_filter] at hx hz
  have hxz : ((x : ZMod q)) = (z : ZMod q) := hx.2.trans hz.2.symm
  exact (ZMod.intCast_eq_intCast_iff x z q).mp hxz

end BlichfeldtGeneral
