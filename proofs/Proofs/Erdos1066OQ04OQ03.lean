import Mathlib

/-
# Erdős 1066 — OQ-04-OQ-03: Proving the kissing-number axioms in Lean

## Research Problem: erdos-1066-oq-04-oq-03

The parent entry `erdos-1066-oq-04` (Higher-Dimensional Unit Distance
Independence) develops the bound

    g_d(n) ≥ n / (τ(d) + 1)

for the independence number of unit-distance graphs on n separated points
in ℝ^d, where τ(d) is the kissing number.  That development rests on two
`axiom` declarations:

  * `degree_le_kissing`   — each vertex has unit-degree ≤ τ(d), a purely
                            geometric / sphere-packing fact;
  * `greedy_independence` — a graph with max degree ≤ τ(d) has an
                            independent set of size ≥ n/(τ(d)+1), a general
                            graph-theory fact.

Its open question asks: *Can the 2 axioms be proved in Lean?*  This entry
answers the **graph-theory half** completely and 0-axiom, and pins down the
exact mathematical residue of the geometric half.

## What is proved here (0 axioms, self-contained)

`greedy_independence_of_maxDegree` — **the general greedy / Turán-type
independence bound**: for *any* degree bound `Δ`, any separated configuration
whose every vertex has unit-degree ≤ `Δ` admits an independent set of size
≥ `n/(Δ+1)`.  No kissing numbers, no axioms.  The proof is the classic
"a maximum independent set is dominating" argument:

    n  ≤  Σ_{u ∈ S} (1 + deg u)  ≤  |S| · (Δ + 1).

`greedy_independence_kissing` — instantiating `Δ := τ(d)` recovers exactly the
parent's `greedy_independence` statement, now as a **theorem** whose only
remaining hypothesis is the degree bound `degree_le_kissing`.

## The residue: `degree_le_kissing` is genuinely hard

`degree_le_kissing` is *not* a one-session Lean target: with the exact kissing
numbers τ(4)=24, τ(8)=240, τ(24)=196560, the bound `unitDegree ≤ τ(d)` is
the kissing-number problem itself (the d=8, 24 cases are Viazovska-level
theorems).  So this entry honestly reduces the parent's axiom budget from
**2 → 1**: the combinatorial axiom is eliminated; the geometric one is
isolated as the true open formalization target.

Tags: combinatorial-geometry, unit-distance, independence-number, graph-theory
-/

open scoped Classical

namespace Erdos1066OQ04OQ03

-- ============================================================
-- Part I: Self-contained re-declaration of the framework
-- (parent file is axiom-bearing; we re-declare to stay 0-axiom)
-- ============================================================

/-- A separated configuration: `n` points in ℝ^d with pairwise distance ≥ 1. -/
structure SepConfig (d n : ℕ) where
  points : Fin n → EuclideanSpace ℝ (Fin d)
  separated : ∀ i j : Fin n, i ≠ j → dist (points i) (points j) ≥ 1

variable {d n : ℕ}

/-- The unit-distance graph: an edge between points at distance exactly 1. -/
def unitEdge (C : SepConfig d n) (i j : Fin n) : Prop :=
  i ≠ j ∧ dist (C.points i) (C.points j) = 1

/-- The unit-distance relation is symmetric. -/
theorem unitEdge_symm (C : SepConfig d n) {i j : Fin n} :
    unitEdge C i j → unitEdge C j i := by
  rintro ⟨hij, hd⟩
  exact ⟨hij.symm, by rw [dist_comm]; exact hd⟩

/-- The unit degree of a vertex: number of unit-distance neighbours. -/
noncomputable def unitDegree (C : SepConfig d n) (i : Fin n) : ℕ :=
  (Finset.univ.filter (fun j => unitEdge C i j)).card

/-- An independent set in the unit-distance graph: no pair shares a unit edge. -/
def IsIndepSet (C : SepConfig d n) (S : Finset (Fin n)) : Prop :=
  ∀ i ∈ S, ∀ j ∈ S, ¬ unitEdge C i j

-- ============================================================
-- Part II: The general greedy independence bound (0 axioms)
-- ============================================================

/-- The closed neighbourhood of `u`: `u` together with its unit-neighbours. -/
private noncomputable def closedNbhd (C : SepConfig d n) (u : Fin n) : Finset (Fin n) :=
  insert u (Finset.univ.filter (fun w => unitEdge C u w))

private theorem card_closedNbhd_le (C : SepConfig d n) (u : Fin n) :
    (closedNbhd C u).card ≤ 1 + unitDegree C u := by
  unfold closedNbhd unitDegree
  calc (insert u (Finset.univ.filter (fun w => unitEdge C u w))).card
      ≤ 1 + (Finset.univ.filter (fun w => unitEdge C u w)).card :=
        (Finset.card_insert_le _ _).trans (by ring_nf; rfl)
    _ = 1 + (Finset.univ.filter (fun j => unitEdge C u j)).card := rfl

/-- **General greedy independence bound.**  If every vertex of a separated
    configuration has unit-degree at most `Δ`, then there is an independent set
    of size at least `n / (Δ + 1)`.

    Proof: take an independent set `S` of *maximum* cardinality.  By
    maximality `S` is dominating — every vertex is in `S` or adjacent to `S` —
    so the closed neighbourhoods of `S` cover all `n` vertices:
    `n ≤ Σ_{u∈S}(1 + deg u) ≤ |S|·(Δ+1)`, whence `|S| ≥ n/(Δ+1)`. -/
theorem greedy_independence_of_maxDegree (C : SepConfig d n) (Δ : ℕ)
    (hdeg : ∀ i, unitDegree C i ≤ Δ) :
    ∃ S : Finset (Fin n), IsIndepSet C S ∧ S.card ≥ n / (Δ + 1) := by
  classical
  -- The family of independent finsets, as a finset of finsets.
  set 𝓘 : Finset (Finset (Fin n)) := Finset.univ.filter (fun S => IsIndepSet C S) with h𝓘
  have hmem : ∀ S, S ∈ 𝓘 ↔ IsIndepSet C S := by
    intro S; simp [h𝓘]
  -- ∅ is independent, so 𝓘 is nonempty.
  have hne : 𝓘.Nonempty := by
    refine ⟨∅, (hmem _).2 ?_⟩
    intro i hi; simp at hi
  -- Choose an independent set of maximum cardinality.
  obtain ⟨S, hS𝓘, hSmax⟩ := 𝓘.exists_max_image Finset.card hne
  have hSind : IsIndepSet C S := (hmem _).1 hS𝓘
  refine ⟨S, hSind, ?_⟩
  -- Domination: every vertex lies in the closed neighbourhood of some u ∈ S.
  have hdom : ∀ v : Fin n, ∃ u ∈ S, v ∈ closedNbhd C u := by
    intro v
    by_cases hv : v ∈ S
    · exact ⟨v, hv, Finset.mem_insert_self _ _⟩
    · -- if v has no neighbour in S, S ∪ {v} is a larger independent set
      by_contra hcon
      push_neg at hcon
      -- no u ∈ S is adjacent to v
      have hno : ∀ u ∈ S, ¬ unitEdge C u v := by
        intro u hu hedge
        exact (hcon u hu) (by
          unfold closedNbhd
          exact Finset.mem_insert_of_mem (by
            simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact hedge))
      -- insert v S is independent
      have hins : IsIndepSet C (insert v S) := by
        intro i hi j hj
        rcases Finset.mem_insert.1 hi with rfl | hiS
        · rcases Finset.mem_insert.1 hj with rfl | hjS
          · rintro ⟨h, _⟩; exact h rfl
          · intro hedge; exact hno j hjS (unitEdge_symm C hedge)
        · rcases Finset.mem_insert.1 hj with rfl | hjS
          · intro hedge; exact hno i hiS hedge
          · exact hSind i hiS j hjS
      -- contradiction with maximality
      have hle : (insert v S).card ≤ S.card := hSmax _ ((hmem _).2 hins)
      rw [Finset.card_insert_of_notMem hv] at hle
      omega
  -- The closed neighbourhoods of S cover everything.
  have hcover : (Finset.univ : Finset (Fin n)) ⊆ S.biUnion (closedNbhd C) := by
    intro v _
    obtain ⟨u, hu, hvu⟩ := hdom v
    exact Finset.mem_biUnion.2 ⟨u, hu, hvu⟩
  -- Cardinality bound.
  have hn : n ≤ S.card * (Δ + 1) := by
    have h1 : (Finset.univ : Finset (Fin n)).card ≤ (S.biUnion (closedNbhd C)).card :=
      Finset.card_le_card hcover
    have h2 : (S.biUnion (closedNbhd C)).card ≤ ∑ u ∈ S, (closedNbhd C u).card :=
      Finset.card_biUnion_le
    have h3 : ∑ u ∈ S, (closedNbhd C u).card ≤ ∑ _u ∈ S, (Δ + 1) := by
      apply Finset.sum_le_sum
      intro u _
      calc (closedNbhd C u).card ≤ 1 + unitDegree C u := card_closedNbhd_le C u
        _ ≤ 1 + Δ := by have := hdeg u; omega
        _ = Δ + 1 := by ring
    have h4 : ∑ _u ∈ S, (Δ + 1) = S.card * (Δ + 1) := by
      rw [Finset.sum_const, smul_eq_mul]
    simp only [Finset.card_univ, Fintype.card_fin] at h1
    omega
  exact Nat.div_le_of_le_mul (by rw [Nat.mul_comm] at hn; exact hn)

-- ============================================================
-- Part III: Specialisation to the kissing number
-- ============================================================

/-- The kissing number τ(d) (re-declared self-contained, matching the parent).
    Known: τ(1)=2, τ(2)=6, τ(3)=12, τ(4)=24, τ(8)=240, τ(24)=196560. -/
noncomputable def kissingNumber : ℕ → ℕ
  | 1 => 2
  | 2 => 6
  | 3 => 12
  | 4 => 24
  | 8 => 240
  | 24 => 196560
  | d => 3 ^ d

/-- **The parent's `greedy_independence`, now a theorem.**  Given the geometric
    degree bound `unitDegree ≤ τ(d)` (the parent's `degree_le_kissing`), the
    `n/(τ(d)+1)` independence bound follows with **no further axioms** — the
    graph-theory content is fully discharged by
    `greedy_independence_of_maxDegree`. -/
theorem greedy_independence_kissing (C : SepConfig d n)
    (hkiss : ∀ i, unitDegree C i ≤ kissingNumber d) :
    ∃ S : Finset (Fin n), IsIndepSet C S ∧ S.card ≥ n / (kissingNumber d + 1) :=
  greedy_independence_of_maxDegree C (kissingNumber d) hkiss

-- ============================================================
-- Part IV: Sanity checks on the kissing values
-- ============================================================

theorem g1_exact : kissingNumber 1 + 1 = 3 := by decide
theorem g2_greedy : kissingNumber 2 + 1 = 7 := by decide
theorem g3_greedy : kissingNumber 3 + 1 = 13 := by decide

/-- A trivial uniform degree bound is always available: every vertex has
    unit-degree ≤ n, giving an (uninformative) independent set of size ≥ n/(n+1).
    This exhibits `greedy_independence_of_maxDegree` with a *provable* bound,
    independent of any kissing-number axiom. -/
theorem greedy_trivial (C : SepConfig d n) :
    ∃ S : Finset (Fin n), IsIndepSet C S ∧ S.card ≥ n / (n + 1) := by
  refine greedy_independence_of_maxDegree C n (fun i => ?_)
  unfold unitDegree
  calc (Finset.univ.filter (fun j => unitEdge C i j)).card
      ≤ (Finset.univ : Finset (Fin n)).card := Finset.card_filter_le _ _
    _ = n := by simp

/-
  Summary

  * `greedy_independence_of_maxDegree` — general 0-axiom greedy bound
    (max independent set is dominating ⇒ n ≤ |S|·(Δ+1)).
  * `greedy_independence_kissing` — the parent's `greedy_independence`
    axiom, recovered as a theorem modulo only the geometric degree bound.
  * `greedy_trivial` — a fully unconditional instantiation (Δ := n).

  Net effect: the parent entry's combinatorial axiom `greedy_independence`
  is ELIMINATED; only the geometric `degree_le_kissing` (= the kissing
  number problem) remains, isolated as the genuine open target.

  0 axioms, 0 sorries.
-/

end Erdos1066OQ04OQ03
