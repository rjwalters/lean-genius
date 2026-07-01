/-
# Erdős Problem #1021 — WIP-02
## The bipartite pair graph G_k is C₄-free

Erdős Problem #1021 asks whether, for every `k ≥ 3`, there is `c_k > 0` with
`ex(n, G_k) ≪ n^{3/2 - c_k}`. That question is OPEN and this file does NOT touch it.

The sibling files pin down the *asymptotic* boundary (`Erdos1021OQ01Incomplete01.lean`:
the exponent gap `1/(k-1) → 0`, the `o ⟹ O` collapse) and the *local degree structure*
(`Erdos1021Wip01.lean`: pair vertices have degree `2`, primary vertices degree `k - 1`).
Neither says anything, machine-checked, about **why `n^{3/2}` is the natural exponent at all**.

This file supplies that missing structural fact, with **zero axioms and zero sorries**:

> **`G_k` is C₄-free**: any two distinct vertices of `G_k` have **at most one common
> neighbour**.

Equivalently, `G_k` contains no `K_{2,2}` (no `4`-cycle): the *codegree* of every pair of
distinct vertices is `≤ 1`. This is exactly the hypothesis of the Kővári–Sós–Turán / Reiman
theorem, whose conclusion is `ex(n, C₄) ≤ ½(1 + √(4n-3))·n = O(n^{3/2})`. So the `n^{3/2}`
appearing throughout Problem #1021 is not an accident of the definition of `G_k`; it is forced
by this elementary `C₄`-freeness, proved here from first principles.

Why `G_k` is C₄-free, combinatorially:
* two **primary** vertices `y_i, y_j` (`i ≠ j`) have a common neighbour only at the pair
  vertex `{i,j}` — the unique pair containing both `i` and `j`;
* two **pair** vertices `⟨{a,b}⟩ ≠ ⟨{c,d}⟩` have a common neighbour `y_m` only when
  `m ∈ {a,b} ∩ {c,d}`, and two distinct `2`-element sets meet in at most one point;
* a **primary** and a **pair** vertex have no common neighbour at all (`G_k` is bipartite).

The file is deliberately **self-contained** (same robustness choice as `Wip01`/`Incomplete01`):
it re-declares `G_k` locally rather than importing `Erdos1021Problem.lean`.

## References
- Kővári, T., Sós, V., Turán, P. (1954). "On a problem of K. Zarankiewicz." Coll. Math. 3:50–57.
- Reiman, I. (1958). "Über ein Problem von K. Zarankiewicz." Acta Math. Acad. Sci. Hungar. 9.
- Bondy, J.A., Simonovits, M. (1974). "Cycles of even length in graphs." J. Combin. Theory 16.
- https://erdosproblems.com/1021
-/

import Mathlib

open SimpleGraph

namespace Erdos1021Wip02

variable {k : ℕ}

/-! ## The bipartite pair graph G_k (local, self-contained definition)

`G_k` has `k` "primary" vertices `Fin k` and `C(k,2)` "pair" vertices — unordered pairs
`{a,b} ⊂ Fin k` encoded as ordered `(a,b)` with `a < b`. Each pair vertex is adjacent to
exactly the two primary vertices of its pair. This matches `Erdos1021.Gk` and
`Erdos1021Wip01.Gk`. -/

/-- The vertex type for `G_k`: a primary vertex (`Fin k`) or a pair vertex. -/
abbrev Gk_vertex (k : ℕ) := Fin k ⊕ { p : Fin k × Fin k // p.1 < p.2 }

/-- `G_k`: each pair vertex `⟨(a,b)⟩` is adjacent to exactly primary vertices `a` and `b`. -/
def Gk (k : ℕ) : SimpleGraph (Gk_vertex k) where
  Adj v w := match v, w with
    | Sum.inl i, Sum.inr ⟨(a, b), _⟩ => i = a ∨ i = b
    | Sum.inr ⟨(a, b), _⟩, Sum.inl i => i = a ∨ i = b
    | _, _ => False
  symm := by
    intro v w h
    rcases v with i | ⟨⟨a, b⟩, hab⟩ <;> rcases w with j | ⟨⟨c, d⟩, hcd⟩ <;> exact h
  loopless := by
    intro v h
    rcases v with i | ⟨⟨a, b⟩, hab⟩ <;> exact h

/-! ## Part I: Adjacency characterizations (mirrors `Wip01`) -/

/-- A pair vertex `⟨{a,b}⟩` is adjacent in `G_k` to exactly the primaries `y_a` and `y_b`. -/
theorem adj_pair_iff (a b : Fin k) (hab : a < b) (w : Gk_vertex k) :
    (Gk k).Adj (Sum.inr ⟨(a, b), hab⟩) w ↔ w = Sum.inl a ∨ w = Sum.inl b := by
  cases w with
  | inl i => simp only [Gk, Sum.inl.injEq]
  | inr q =>
      simp only [Gk]
      constructor
      · exact False.elim
      · rintro (h | h) <;> exact (Sum.inr_ne_inl h).elim

/-- A primary vertex `y_i` is adjacent in `G_k` to exactly the pair vertices containing `i`. -/
theorem adj_primary_iff (i : Fin k) (w : Gk_vertex k) :
    (Gk k).Adj (Sum.inl i) w ↔
      ∃ q : { p : Fin k × Fin k // p.1 < p.2 }, w = Sum.inr q ∧ (i = q.val.1 ∨ i = q.val.2) := by
  cases w with
  | inl j =>
      simp only [Gk]
      constructor
      · exact False.elim
      · rintro ⟨q, hq, _⟩; exact (Sum.inl_ne_inr hq).elim
  | inr q =>
      obtain ⟨⟨a, b⟩, hab⟩ := q
      simp only [Gk, Sum.inr.injEq]
      constructor
      · intro h; exact ⟨⟨(a, b), hab⟩, rfl, h⟩
      · rintro ⟨q', hq', h⟩
        obtain ⟨⟨a', b'⟩, hab'⟩ := q'
        cases hq'; exact h

/-- Projection-free adjacency: a primary `y_i` is adjacent to the pair vertex `⟨(a,b)⟩`
    exactly when `i ∈ {a, b}`. (Convenient form for the case analysis below.) -/
theorem adj_primary_pair (i a b : Fin k) (hab : a < b) :
    (Gk k).Adj (Sum.inl i) (Sum.inr ⟨(a, b), hab⟩) ↔ (i = a ∨ i = b) := by
  simp only [Gk]

/-- Projection-free adjacency: the pair vertex `⟨(a,b)⟩` is adjacent to a primary `y_m`
    exactly when `m ∈ {a, b}`. -/
theorem adj_pair_inl (a b : Fin k) (hab : a < b) (m : Fin k) :
    (Gk k).Adj (Sum.inr ⟨(a, b), hab⟩) (Sum.inl m) ↔ (m = a ∨ m = b) := by
  simp only [Gk]

/-! ## Part II: `G_k` is C₄-free — every two distinct vertices have ≤ 1 common neighbour

The heart of the file. We prove the neighbourhood intersection of any two distinct vertices
is a *subsingleton*, i.e. has at most one element (`codegree ≤ 1`). -/

/-- **`G_k` is C₄-free.** The set of common neighbours of any two distinct vertices `v ≠ w`
is a subsingleton: there is at most one vertex adjacent to both. Equivalently, `G_k` contains
no `K_{2,2}` (no `4`-cycle) — the Kővári–Sós–Turán hypothesis forcing `ex(n, G_k) = O(n^{3/2})`.

The proof is a case analysis on the two sides of the bipartition:
* two primaries `y_i, y_j` share only the pair vertex `{i,j}`;
* two distinct pair vertices `{a,b}, {c,d}` share only a primary in `{a,b} ∩ {c,d}`, and
  two distinct `2`-sets meet in `≤ 1` point;
* a primary and a pair vertex share nothing (bipartiteness). -/
theorem Gk_common_neighbors_subsingleton (v w : Gk_vertex k) (hvw : v ≠ w) :
    Set.Subsingleton ((Gk k).neighborSet v ∩ (Gk k).neighborSet w) := by
  rintro u₁ ⟨h1v, h1w⟩ u₂ ⟨h2v, h2w⟩
  simp only [mem_neighborSet] at h1v h1w h2v h2w
  -- Split on the two sides of `v` and `w`.
  rcases v with i | ⟨⟨a, b⟩, hab⟩ <;> rcases w with j | ⟨⟨c, d⟩, hcd⟩
  · -- v = y_i, w = y_j : common neighbours are pair vertices; the pair `{i,j}` is forced.
    have hij : i ≠ j := fun h => hvw (congrArg Sum.inl h)
    -- Neighbours of a primary are pair vertices, so `u₁, u₂` have the form `Sum.inr _`.
    obtain ⟨⟨⟨e₁, f₁⟩, hef₁⟩, rfl⟩ : ∃ q, u₁ = Sum.inr q := by
      cases u₁ with
      | inl x => simp only [Gk] at h1v
      | inr q => exact ⟨q, rfl⟩
    obtain ⟨⟨⟨e₂, f₂⟩, hef₂⟩, rfl⟩ : ∃ q, u₂ = Sum.inr q := by
      cases u₂ with
      | inl x => simp only [Gk] at h2v
      | inr q => exact ⟨q, rfl⟩
    rw [adj_primary_pair] at h1v h2v h1w h2w
    dsimp only at hef₁ hef₂
    -- h1v : i = e₁ ∨ i = f₁, h1w : j = e₁ ∨ j = f₁, h2v : i = e₂ ∨ i = f₂, h2w : j = e₂ ∨ j = f₂
    suffices h : e₁ = e₂ ∧ f₁ = f₂ by obtain ⟨rfl, rfl⟩ := h; rfl
    rcases h1v with rfl | rfl <;> rcases h1w with h1w | h1w <;>
      rcases h2v with h2v | h2v <;> rcases h2w with h2w | h2w <;>
      exact ⟨by omega, by omega⟩
  · -- v = y_i (primary), w = pair `{c,d}` : no common neighbour (bipartite ⇒ contradiction).
    rw [adj_primary_iff] at h1v
    obtain ⟨q, rfl, _⟩ := h1v
    rw [adj_pair_iff c d hcd] at h1w
    rcases h1w with h | h <;> exact absurd h (by simp)
  · -- symmetric to the previous case.
    rw [adj_primary_iff] at h1w
    obtain ⟨q, rfl, _⟩ := h1w
    rw [adj_pair_iff a b hab] at h1v
    rcases h1v with h | h <;> exact absurd h (by simp)
  · -- v = pair `{a,b}`, w = pair `{c,d}` : common neighbours are primaries in `{a,b}∩{c,d}`.
    have hpairs : ¬ (a = c ∧ b = d) := by rintro ⟨rfl, rfl⟩; exact hvw rfl
    -- Neighbours of a pair vertex are primaries, so `u₁, u₂` have the form `Sum.inl _`.
    obtain ⟨m₁, rfl⟩ : ∃ m, u₁ = Sum.inl m := by
      cases u₁ with
      | inl m => exact ⟨m, rfl⟩
      | inr q => simp only [Gk] at h1v
    obtain ⟨m₂, rfl⟩ : ∃ m, u₂ = Sum.inl m := by
      cases u₂ with
      | inl m => exact ⟨m, rfl⟩
      | inr q => simp only [Gk] at h2v
    rw [adj_pair_inl a b hab] at h1v h2v
    rw [adj_pair_inl c d hcd] at h1w h2w
    dsimp only at hab hcd
    -- h1v : m₁ = a ∨ m₁ = b, h1w : m₁ = c ∨ m₁ = d, h2v : m₂ = a ∨ m₂ = b, h2w : m₂ = c ∨ m₂ = d
    suffices h : m₁ = m₂ by rw [h]
    rcases h1v with rfl | rfl <;> rcases h1w with h1w | h1w <;>
      rcases h2v with h2v | h2v <;> rcases h2w with h2w | h2w <;>
      omega

/-- **Codegree bound (C₄-free, cardinality form).** Any two distinct vertices of `G_k` have
at most one common neighbour: the neighbourhood intersection has `ncard ≤ 1`. -/
theorem Gk_codegree_le_one (v w : Gk_vertex k) (hvw : v ≠ w) :
    ((Gk k).neighborSet v ∩ (Gk k).neighborSet w).ncard ≤ 1 := by
  rw [Set.ncard_le_one]
  intro x hx y hy
  exact Gk_common_neighbors_subsingleton v w hvw hx hy

/-- **No `4`-cycle, explicit form.** There do not exist two distinct vertices `v ≠ w` with two
*distinct* common neighbours `u₁ ≠ u₂`. This is the standard statement that `G_k` is C₄-free
(contains no `K_{2,2}`), read off directly from the subsingleton bound. -/
theorem Gk_no_C4 (v w u₁ u₂ : Gk_vertex k)
    (hvw : v ≠ w)
    (h1 : (Gk k).Adj v u₁) (h2 : (Gk k).Adj w u₁)
    (h3 : (Gk k).Adj v u₂) (h4 : (Gk k).Adj w u₂) :
    u₁ = u₂ :=
  Gk_common_neighbors_subsingleton v w hvw ⟨h1, h2⟩ ⟨h3, h4⟩

/-! ## Part III: Summary

Proved here (0 axioms, 0 sorries), all about the *actual* graph `G_k`:
* `adj_pair_iff`, `adj_primary_iff` — exact adjacency on each side (as in `Wip01`).
* `Gk_common_neighbors_subsingleton` — **`G_k` is C₄-free**: two distinct vertices have at
  most one common neighbour (codegree `≤ 1`).
* `Gk_codegree_le_one` — the same fact in cardinality (`ncard ≤ 1`) form.
* `Gk_no_C4` — the explicit "no `K_{2,2}` / no `4`-cycle" statement.

This is the elementary structural reason the Kővári–Sós–Turán bound applies and `n^{3/2}` is
the natural exponent for Erdős Problem #1021. The problem itself — whether the exponent can be
*beaten* to `3/2 - c_k` — remains OPEN and is untouched here.
-/

end Erdos1021Wip02
