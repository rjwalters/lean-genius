/-
  Erdős Problem #895 — the sharp `Fin 18` counterexample, machine-verified

  Source: https://erdosproblems.com/895
  Companion to `Erdos895Problem.lean`.

  ## Background

  Erdős–Hajnal asked: for large `n`, must every triangle-free graph on `{1,…,n}`
  contain three vertices `a, b, a+b` that are pairwise non-adjacent (an *independent
  additive / Schur triple*)? Ben Barber (2015) proved YES for all `n ≥ 18`, and the
  threshold is sharp: there is a triangle-free graph on `{1,…,17}` with no such triple
  among **three distinct** vertices.

  ## Why this companion file exists

  `Erdos895Problem.lean` states `counterexample_17` over `Fin 17` using a predicate
  `IsAdditiveTriple` that omits the distinctness constraint `a ≠ b`. As researcher-1
  established (Z3 exhaustive UNSAT + pure-Python witness checks, scripts under
  `research/problems/erdos-895-incomplete-01/`), that statement is **false**: with the
  loose predicate every triangle-free graph on `Fin 17` already has an (a = b) "triple",
  and the genuine, distinct-vertex counterexample lives on **`Fin 18`** (vertex `0`
  isolated, modelling `{1,…,17}`), not `Fin 17`.

  This file gives the **corrected, machine-checked** statement: the explicit 42-edge
  witness, built as a genuine `SimpleGraph (Fin 18)`, is triangle-free and has no
  independent additive triple among three distinct vertices. Both facts are discharged
  by `native_decide` (exhaustive over `Fin 18`). The witness graph is
  `research/problems/erdos-895-incomplete-01/counterexample-fin18.json`.

  Note on axioms: `native_decide` relies on `Lean.ofReduceBool` (the Lean compiler's
  kernel-reduction trust). This file is therefore *axiomatized* in the gallery sense,
  with that single disclosed assumption; the underlying combinatorial claim is an
  exhaustive finite check.
-/

import Mathlib

open Finset SimpleGraph

namespace Erdos895CounterexampleFin18

/-! ## Predicates (matching `Erdos895Problem.lean`, with distinctness corrected) -/

/-- Three vertices form an independent set if no two are adjacent. -/
@[reducible] def IsIndependentTriple {n : ℕ} (G : SimpleGraph (Fin n)) (a b c : Fin n) : Prop :=
  ¬G.Adj a b ∧ ¬G.Adj b c ∧ ¬G.Adj a c

/-- A graph is triangle-free if it contains no 3-clique. -/
@[reducible] def IsTriangleFree {n : ℕ} (G : SimpleGraph (Fin n)) : Prop :=
  ∀ a b c : Fin n, ¬(G.Adj a b ∧ G.Adj b c ∧ G.Adj a c)

/-- A **corrected** additive triple `(a, b, a+b)` requiring three DISTINCT vertices
(`a ≠ b`), matching Barber's theorem. The loose version in `Erdos895Problem.lean` omits
`a ≠ b` and so admits the degenerate `(k, k, 2k)`, which changes the answer. -/
@[reducible] def IsDistinctAdditiveTriple {n : ℕ} (a b c : Fin n) : Prop :=
  (a.val : ℕ) + b.val = c.val ∧ a.val > 0 ∧ b.val > 0 ∧ a ≠ b

/-! ## The explicit witness graph on `Fin 18` -/

/-- The 42 edges (ascending pairs on `{1,…,17}`) of Barber's sharp counterexample. -/
def ce895Pairs : List (ℕ × ℕ) :=
  [(1,3), (1,5), (1,10), (1,12), (1,14), (1,16), (2,5), (2,6), (2,9), (2,12), (2,13),
   (2,16), (3,7), (3,9), (3,11), (3,13), (3,15), (4,5), (4,11), (4,12), (4,13), (4,14),
   (5,8), (5,15), (6,7), (6,10), (6,11), (6,14), (6,15), (7,8), (7,12), (7,16), (8,9),
   (8,10), (8,13), (9,14), (10,17), (11,16), (12,17), (14,17), (15,17), (16,17)]

/-- Symmetric Boolean adjacency: `a ~ b` iff the ascending pair `(min a b, max a b)`
is one of the 42 listed edges. Symmetric by construction (via `min`/`max`). -/
def ce895Adj (a b : Fin 18) : Bool :=
  decide ((min a.val b.val, max a.val b.val) ∈ ce895Pairs)

theorem ce895Adj_comm (a b : Fin 18) : ce895Adj a b = ce895Adj b a := by
  unfold ce895Adj
  rw [Nat.min_comm, Nat.max_comm]

/-- Barber's sharp counterexample as a genuine simple graph on `Fin 18`. -/
def G895 : SimpleGraph (Fin 18) where
  Adj a b := ce895Adj a b = true ∧ a ≠ b
  symm := by
    rintro a b ⟨hadj, hne⟩
    exact ⟨by rw [ce895Adj_comm]; exact hadj, hne.symm⟩
  loopless := by rintro a ⟨_, hne⟩; exact hne rfl

instance : DecidableRel G895.Adj := fun a b =>
  inferInstanceAs (Decidable (ce895Adj a b = true ∧ a ≠ b))

/-! ## Verified properties (exhaustive `native_decide` over `Fin 18`) -/

/-- `G895` is triangle-free. -/
theorem ce895_triangleFree : IsTriangleFree G895 := by native_decide

/-- `G895` has **no** independent additive triple among three DISTINCT vertices.
(Under the loose predicate of `Erdos895Problem.lean` the degenerate triples `(k, k, 2k)`
would spuriously count; with `a ≠ b` enforced there is genuinely none.) -/
theorem ce895_no_distinct_independent_additive_triple :
    ¬ ∃ a b c : Fin 18, IsDistinctAdditiveTriple a b c ∧ IsIndependentTriple G895 a b c := by
  native_decide

/-- **Corrected sharpness witness for Erdős #895.** There is a triangle-free graph on
`Fin 18` (= `{1,…,17}`, vertex `0` isolated) with no independent additive triple among
three distinct vertices — the machine-verified replacement for the false-as-stated
`counterexample_17` (over `Fin 17`) in `Erdos895Problem.lean`. Together with Barber's
theorem (`n ≥ 18` ⟹ such a triple always exists, in distinct vertices) this shows the
threshold is sharp. -/
theorem counterexample_fin18 :
    ∃ G : SimpleGraph (Fin 18), IsTriangleFree G ∧
      ¬ ∃ a b c : Fin 18, IsDistinctAdditiveTriple a b c ∧ IsIndependentTriple G a b c :=
  ⟨G895, ce895_triangleFree, ce895_no_distinct_independent_additive_triple⟩

end Erdos895CounterexampleFin18
