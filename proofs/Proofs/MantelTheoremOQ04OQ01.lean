/-
Copyright (c) 2024-2026 lean-genius contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib

/-!
# The Turán graph as a complete multipartite graph (general `n`)

`Proofs/MantelTheoremOQ04.lean` identifies the triangle-free (`r = 2`) extremal graph
`turanGraph n 2` with the *balanced complete bipartite* graph `K_{⌈n/2⌉,⌊n/2⌋}` for arbitrary
`n`, generalizing Mathlib's `completeEquipartiteGraph.turanGraph` (which only covers the
balanced **equipartite** case `n = r · t`). This file takes the natural next step: the same
identification for **every** number of parts `r`.

Mathlib's `completeEquipartiteGraph.turanGraph` gives
`completeEquipartiteGraph r t ≃g turanGraph (r * t) r`, i.e. it identifies `turanGraph n r` with
a complete `r`-partite graph **only** when `r ∣ n` and all parts have equal size `t = n / r`.
For general `n` the `r` residue classes mod `r` have sizes that differ by at most one — the parts
are *balanced* but not *equal* — so the equipartite isomorphism does not apply.

## Main results

* `turanGraphIsoCompleteMultipartite` : for `0 < r`,
  `completeMultipartiteGraph (fun j : Fin r => residue class j) ≃g turanGraph n r`,
  where the `j`-th part is the set of vertices `v` with `v % r = j`. This realizes `turanGraph n r`
  as a genuine complete `r`-partite graph for arbitrary `n`, the structural heart of Turán's
  theorem. The bijection is `Equiv.sigmaFiberEquiv` of the colouring `v ↦ v % r`, so it carries
  "different part" exactly to "different residue", i.e. to `turanGraph` adjacency.
* `turanGraph_isCompleteMultipartite` : `(turanGraph n r).IsCompleteMultipartite` for `0 < r`,
  transported from the canonical complete multipartite graph along the isomorphism.
* `card_turanResidue` : the `j`-th part has size `(n + r - 1 - j) / r` — the exact balanced
  cardinalities (`⌈(n - j) / r⌉`), so any two parts differ in size by at most one.
* `sum_turanResidueSize` : `∑ j : Fin r, (n + r - 1 - j) / r = n`. The `r` residue classes
  partition the `n` vertices; equivalently the balanced part sizes sum to `n`.
-/

open Finset Fintype SimpleGraph

namespace Mantel

variable (n r : ℕ)

/-- The Turán colouring: a vertex `v : Fin n` of `turanGraph n r` is sent to its residue
`v % r : Fin r`. Two vertices are adjacent in `turanGraph n r` iff they get different colours,
so the colour classes are exactly the parts of the complete multipartite structure. -/
def turanColor (hr : 0 < r) (v : Fin n) : Fin r := ⟨(v : ℕ) % r, Nat.mod_lt _ hr⟩

@[simp] lemma turanColor_val (hr : 0 < r) (v : Fin n) :
    ((turanColor n r hr v : Fin r) : ℕ) = (v : ℕ) % r := rfl

/-- **`turanGraph n r` is a complete `r`-partite graph for arbitrary `n`.**

The parts are the `r` residue classes `{v : Fin n | v % r = j}`, `j : Fin r`. Via
`Equiv.sigmaFiberEquiv` of the colouring `turanColor`, "lying in different parts" corresponds
exactly to "having different residues mod `r`", which is `turanGraph` adjacency. This generalizes
Mathlib's `completeEquipartiteGraph.turanGraph` from the equipartite case `n = r · t` (equal parts)
to all `n` (balanced parts differing in size by at most one). -/
def turanGraphIsoCompleteMultipartite (hr : 0 < r) :
    completeMultipartiteGraph (fun j : Fin r => {v : Fin n // turanColor n r hr v = j}) ≃g
      turanGraph n r where
  toEquiv := Equiv.sigmaFiberEquiv (turanColor n r hr)
  map_rel_iff' := by
    rintro ⟨j, v, hv⟩ ⟨j', w, hw⟩
    simp only [Equiv.sigmaFiberEquiv_apply, turanGraph_adj, completeMultipartiteGraph,
      comap_adj, top_adj, ne_eq]
    -- `hv : turanColor v = j`, `hw : turanColor w = j'`; reduce both sides to `↑j ≠ ↑j'`.
    have hvj : (v : ℕ) % r = (j : ℕ) := by rw [← turanColor_val n r hr v, hv]
    have hwj : (w : ℕ) % r = (j' : ℕ) := by rw [← turanColor_val n r hr w, hw]
    rw [hvj, hwj]
    exact ⟨fun h he => h (by rw [he]), fun h he => h (Fin.ext he)⟩

/-- **`turanGraph n r` is complete multipartite** (for `0 < r`): the negation of adjacency is
transitive, i.e. "same part" is an equivalence. Transported from the canonical
`completeMultipartiteGraph` along `turanGraphIsoCompleteMultipartite`. -/
theorem turanGraph_isCompleteMultipartite (hr : 0 < r) :
    (turanGraph n r).IsCompleteMultipartite :=
  (completeMultipartiteGraph.isCompleteMultipartite _).comap
    (turanGraphIsoCompleteMultipartite n r hr).symm.toEmbedding

/-- Explicit bijection between `Fin ((n + r - 1 - j) / r)` and the `j`-th residue class of
`turanGraph n r`. The `k`-th element of the class is `r * k + j`. This pins down the exact size
of each part. -/
def turanResidueEquiv (hr : 0 < r) (j : Fin r) :
    Fin ((n + r - 1 - (j : ℕ)) / r) ≃ {v : Fin n // turanColor n r hr v = j} where
  toFun k :=
    ⟨⟨r * (k : ℕ) + (j : ℕ), by
        have hb : ((k : ℕ) + 1) * r ≤ n + r - 1 - (j : ℕ) :=
          (Nat.le_div_iff_mul_le hr).mp k.2
        rw [add_one_mul] at hb
        have hcomm : (k : ℕ) * r = r * (k : ℕ) := Nat.mul_comm _ _
        have := j.2
        omega⟩,
      by
        apply Fin.ext
        rw [turanColor_val]
        show (r * (k : ℕ) + (j : ℕ)) % r = (j : ℕ)
        rw [Nat.mul_add_mod, Nat.mod_eq_of_lt j.2]⟩
  invFun v :=
    ⟨(v : Fin n) / r, by
      have hv : ((v : Fin n) : ℕ) % r = (j : ℕ) := by rw [← turanColor_val n r hr (v : Fin n), v.2]
      have hub : ((v : Fin n) : ℕ) < n := (v : Fin n).2
      rw [← Nat.add_one_le_iff, Nat.le_div_iff_mul_le hr, add_one_mul]
      have hdm := Nat.div_add_mod ((v : Fin n) : ℕ) r
      have hcomm : ((v : Fin n) : ℕ) / r * r = r * (((v : Fin n) : ℕ) / r) := Nat.mul_comm _ _
      omega⟩
  left_inv k := by
    apply Fin.ext
    show (r * (k : ℕ) + (j : ℕ)) / r = (k : ℕ)
    rw [Nat.mul_add_div hr, Nat.div_eq_of_lt j.2, add_zero]
  right_inv v := by
    apply Subtype.ext
    apply Fin.ext
    have hv : ((v : Fin n) : ℕ) % r = (j : ℕ) := by rw [← turanColor_val n r hr (v : Fin n), v.2]
    show r * (((v : Fin n) : ℕ) / r) + (j : ℕ) = ((v : Fin n) : ℕ)
    rw [← hv, Nat.div_add_mod]

/-- **The `j`-th part of `turanGraph n r` has size `(n + r - 1 - j) / r = ⌈(n - j) / r⌉`.**
These are the balanced Turán part sizes: as `j` ranges over `Fin r` the values take only the two
consecutive integers `⌈n / r⌉` and `⌊n / r⌋`, so any two parts differ in size by at most one. -/
theorem card_turanResidue (hr : 0 < r) (j : Fin r) :
    Fintype.card {v : Fin n // turanColor n r hr v = j} = (n + r - 1 - (j : ℕ)) / r := by
  rw [← Fintype.card_fin ((n + r - 1 - (j : ℕ)) / r)]
  exact Fintype.card_congr (turanResidueEquiv n r hr j).symm

/-- **The `r` residue classes partition the `n` vertices.** Equivalently, the balanced Turán part
sizes sum to `n`: `∑ j : Fin r, ⌈(n - j) / r⌉ = n`. -/
theorem sum_turanResidueSize (hr : 0 < r) :
    ∑ j : Fin r, (n + r - 1 - (j : ℕ)) / r = n := by
  have key : ∑ j : Fin r, Fintype.card {v : Fin n // turanColor n r hr v = j} = n := by
    rw [← Fintype.card_sigma, Fintype.card_congr (Equiv.sigmaFiberEquiv (turanColor n r hr)),
      Fintype.card_fin]
  calc ∑ j : Fin r, (n + r - 1 - (j : ℕ)) / r
      = ∑ j : Fin r, Fintype.card {v : Fin n // turanColor n r hr v = j} :=
        Finset.sum_congr rfl (fun j _ => (card_turanResidue n r hr j).symm)
    _ = n := key

/-- The balanced complete-bipartite case `r = 2` recovers the part sizes `⌈n/2⌉` and `⌊n/2⌋`
used in `MantelTheoremOQ04.lean`: residue `0` has `(n + 1) / 2` vertices and residue `1` has
`n / 2`. -/
theorem card_turanResidue_two (j : Fin 2) :
    Fintype.card {v : Fin n // turanColor n 2 (by norm_num) v = j} =
      if (j : ℕ) = 0 then (n + 1) / 2 else n / 2 := by
  rw [card_turanResidue n 2 (by norm_num) j]
  rcases (by omega : (j : ℕ) = 0 ∨ (j : ℕ) = 1) with hj | hj <;> simp [hj]

end Mantel
