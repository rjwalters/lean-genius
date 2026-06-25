/-
# Erdős Problem #1021 — WIP-01
## The local degree structure of the bipartite pair graph G_k

Erdős Problem #1021 asks whether, for every `k ≥ 3`, there is `c_k > 0` with
`ex(n, G_k) ≪ n^{3/2 - c_k}`. That question is OPEN and this file does NOT touch it.

The existing files for this problem formalize the *asymptotic* boundary of the question
(`Erdos1021OQ01Incomplete01.lean`: the o ⟹ O collapse, the exponent gap `1/(k-1)`, …)
but say almost nothing, machine-checked, about the **actual combinatorial object `G_k`**
beyond bipartiteness. This file fills that gap with **zero axioms and zero sorries**.

It is deliberately **self-contained** (like the sibling `Incomplete01` file): it re-declares
`G_k` locally rather than importing `Erdos1021Problem.lean`, whose `Gk_bipartite` has an
`↔`-vs-`→` precedence bug and whose `cycleGraph` loopless proof no longer goes through under
the current Mathlib. (Re-declaring is the same robustness choice `Incomplete01` made for the
asymptotic definitions.)

What is pinned down here — the local adjacency structure of `G_k`, which is precisely the
structure that makes `n^{3/2}` the natural exponent:

* `Gk_pair_adj_iff` / `Gk_primary_adj_iff` — exact adjacency characterizations on each side.
* `Gk_pair_neighborSet` — every pair vertex `⟨{a,b}⟩` has neighbor set exactly `{y_a, y_b}`.
* `Gk_pair_degree` — **every pair vertex has degree exactly `2`** (the pair side is
  `2`-regular: each `z_j` is a "cherry" joining two primary vertices — the source of the
  Kővári–Sós–Turán `n^{3/2}` behaviour).
* `Gk_primary_neighborSet` / `Gk_primary_degree` — a primary vertex `y_i` is adjacent to
  exactly the pair vertices containing `i`; **its degree is exactly `k - 1`** (bijection
  with the other primaries `{j ≠ i}`).
* `Gk_handshake` — `2·C(k,2) = k·(k-1)`, the degree-sum (handshake) consistency between the
  two sides.

None of this is asymptotic and none of it is assumed: elementary finite combinatorics about
`G_k`, fully verified.

## References
- Kővári, T., Sós, V., Turán, P. (1954). "On a problem of K. Zarankiewicz." Coll. Math. 3.
- Bondy, J.A., Simonovits, M. (1974). "Cycles of even length in graphs." JCTB 16.
- https://erdosproblems.com/1021
-/

import Mathlib

open SimpleGraph

namespace Erdos1021Wip01

variable {k : ℕ}

/-! ## The bipartite pair graph G_k (local, self-contained definition)

`G_k` has `k` "primary" vertices `Fin k` and `C(k,2)` "pair" vertices — unordered pairs
`{a,b} ⊂ Fin k` encoded as ordered `(a,b)` with `a < b`. Each pair vertex is adjacent to
exactly the two primary vertices of its pair. This matches `Erdos1021.Gk`. -/

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

/-! ## Part I: Exact adjacency characterizations -/

/-- A pair vertex `⟨{a,b}⟩` is adjacent in `G_k` to exactly the two primary vertices
    `y_a` and `y_b`. -/
theorem Gk_pair_adj_iff (a b : Fin k) (hab : a < b) (w : Gk_vertex k) :
    (Gk k).Adj (Sum.inr ⟨(a, b), hab⟩) w ↔ w = Sum.inl a ∨ w = Sum.inl b := by
  cases w with
  | inl i => simp only [Gk, Sum.inl.injEq]
  | inr q =>
      simp only [Gk]
      constructor
      · exact False.elim
      · rintro (h | h) <;> exact (Sum.inr_ne_inl h).elim

/-- A primary vertex `y_i` is adjacent in `G_k` to exactly the pair vertices whose pair
    contains `i`. -/
theorem Gk_primary_adj_iff (i : Fin k) (w : Gk_vertex k) :
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

/-! ## Part II: The pair side is 2-regular -/

/-- The neighbor set of a pair vertex is exactly `{y_a, y_b}`. -/
theorem Gk_pair_neighborSet (a b : Fin k) (hab : a < b) :
    (Gk k).neighborSet (Sum.inr ⟨(a, b), hab⟩) = {Sum.inl a, Sum.inl b} := by
  ext w
  simp only [mem_neighborSet, Set.mem_insert_iff, Set.mem_singleton_iff, Gk_pair_adj_iff a b hab]

/-- **Every pair vertex of `G_k` has degree exactly `2`.**
    Each `z_j` joins precisely the two primary vertices of its pair, so the pair side of
    `G_k` is `2`-regular. This is the local "cherry" structure behind the `n^{3/2}` exponent. -/
theorem Gk_pair_degree (a b : Fin k) (hab : a < b) :
    ((Gk k).neighborSet (Sum.inr ⟨(a, b), hab⟩)).ncard = 2 := by
  rw [Gk_pair_neighborSet a b hab]
  refine Set.ncard_pair ?_
  intro h
  exact (ne_of_lt hab) (Sum.inl_injective h)

/-! ## Part III: The primary side has degree `k - 1` -/

/-- The neighbor set of a primary vertex `y_i` is exactly the set of pair vertices whose
    pair contains `i`. -/
theorem Gk_primary_neighborSet (i : Fin k) :
    (Gk k).neighborSet (Sum.inl i) =
      {w | ∃ q : { p : Fin k × Fin k // p.1 < p.2 },
              w = Sum.inr q ∧ (i = q.val.1 ∨ i = q.val.2)} := by
  ext w
  simp only [mem_neighborSet, Set.mem_setOf_eq, Gk_primary_adj_iff i w]

/-- The pair vertex determined by `i` and a distinct primary `j`:
    `{i, j}` ordered so the smaller index comes first. -/
private def mkPair (i j : Fin k) (hij : i ≠ j) : { p : Fin k × Fin k // p.1 < p.2 } :=
  if h : i < j then ⟨(i, j), h⟩ else ⟨(j, i), lt_of_le_of_ne (not_lt.mp h) (fun e => hij e.symm)⟩

/-- **Every primary vertex of `G_k` has degree exactly `k - 1`.**
    `y_i` is adjacent to the `k - 1` pair vertices `{i, j}` over the other primaries `j ≠ i`.
    Proved by exhibiting a bijection from `{j : Fin k // j ≠ i}` onto the neighbor set. -/
theorem Gk_primary_degree (i : Fin k) :
    ((Gk k).neighborSet (Sum.inl i)).ncard = k - 1 := by
  classical
  rw [Gk_primary_neighborSet i]
  have hcard : Fintype.card { j : Fin k // j ≠ i } = k - 1 := by
    simp [Fintype.card_subtype_compl]
  have himg :
      {w : Gk_vertex k | ∃ q : { p : Fin k × Fin k // p.1 < p.2 },
            w = Sum.inr q ∧ (i = q.val.1 ∨ i = q.val.2)}
        = (fun j : { j : Fin k // j ≠ i } =>
            (Sum.inr (mkPair i j.1 (fun e => j.2 e.symm)) : Gk_vertex k)) '' Set.univ := by
    ext w
    constructor
    · rintro ⟨⟨⟨a, b⟩, hab⟩, rfl, hi | hi⟩
      · -- i = a; the other element is b, and mkPair i b = ⟨(i,b),hab⟩
        subst hi
        have hbi : b ≠ i := (ne_of_lt hab).symm
        refine ⟨⟨b, hbi⟩, Set.mem_univ _, ?_⟩
        simp only [mkPair, dif_pos hab]
      · -- i = b; the other element is a, and mkPair i a = ⟨(a,i),hab⟩
        subst hi
        have hai : a ≠ i := ne_of_lt hab
        refine ⟨⟨a, hai⟩, Set.mem_univ _, ?_⟩
        have hnia : ¬ i < a := not_lt.mpr (le_of_lt hab)
        simp only [mkPair, dif_neg hnia]
    · rintro ⟨⟨j, hj⟩, _, rfl⟩
      refine ⟨mkPair i j (fun e => hj e.symm), rfl, ?_⟩
      by_cases h : i < j
      · simp [mkPair, dif_pos h]
      · simp [mkPair, dif_neg h]
  have hinj : Function.Injective
      (fun j : { j : Fin k // j ≠ i } =>
        (Sum.inr (mkPair i j.1 (fun e => j.2 e.symm)) : Gk_vertex k)) := by
    rintro ⟨j₁, hj₁⟩ ⟨j₂, hj₂⟩ h
    simp only [Sum.inr.injEq] at h
    have key : j₁ = j₂ := by
      unfold mkPair at h
      by_cases h1 : i < j₁ <;> by_cases h2 : i < j₂
      · rw [dif_pos h1, dif_pos h2, Subtype.mk.injEq, Prod.mk.injEq] at h; exact h.2
      · rw [dif_pos h1, dif_neg h2, Subtype.mk.injEq, Prod.mk.injEq] at h
        exact absurd h.1.symm hj₂
      · rw [dif_neg h1, dif_pos h2, Subtype.mk.injEq, Prod.mk.injEq] at h
        exact absurd h.1 hj₁
      · rw [dif_neg h1, dif_neg h2, Subtype.mk.injEq, Prod.mk.injEq] at h; exact h.1
    exact Subtype.ext key
  rw [himg, Set.ncard_image_of_injective _ hinj, Set.ncard_univ,
      Nat.card_eq_fintype_card, hcard]

/-! ## Part IV: Handshake consistency -/

/-- The two sides of `G_k` agree under the handshake lemma: the `C(k,2)` pair vertices each
    contribute degree `2`, the `k` primary vertices each contribute degree `k - 1`, and these
    totals coincide: `2·C(k,2) = k·(k-1)`. -/
theorem Gk_handshake (k : ℕ) :
    2 * Nat.choose k 2 = k * (k - 1) := by
  rw [Nat.choose_two_right]
  have h : 2 ∣ k * (k - 1) := by
    rcases Nat.even_or_odd k with he | ho
    · exact he.two_dvd.mul_right _
    · exact (Nat.Odd.sub_odd ho odd_one).two_dvd.mul_left _
  rw [Nat.mul_div_cancel' h]

/-! ## Part V: Summary

Proved here (0 axioms, 0 sorries), all about the *actual* graph `G_k`:
* `Gk_pair_adj_iff`, `Gk_primary_adj_iff` — exact adjacency on each side.
* `Gk_pair_neighborSet`, `Gk_pair_degree` — pair side is `2`-regular (degree `2`).
* `Gk_primary_neighborSet`, `Gk_primary_degree` — primary side has degree `k - 1`.
* `Gk_handshake` — `2·C(k,2) = k·(k-1)`, the degree-sum consistency.

NOT addressed (genuinely open / external): OQ-01 `ex(n, G_k) = o(n^{3/2})`, the KST upper
bound, and the probabilistic lower bound. Those live in the sibling files and remain open.
-/

end Erdos1021Wip01
