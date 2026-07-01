/-
  Erdős Problem #1015, OQ-05 → OQ-01:
  Toward Moon's Theorem f(3) = 4 — Verified Structural Infrastructure

  Parent question (erdos-1015-oq-05): "Can any of the axioms in the
  Erdős #1015 formalization be proved from Mathlib?" That work eliminated
  `ramseyNumber` and `ramsey_upper_bound`. This child asks specifically:

      Can `moon_f3` — Moon's (1966) result f(3) = 4 — be proved in Lean?

  ## Honest status

  Moon's theorem f(3) = 4 is a genuine 1966 combinatorial result. Proving it
  in full requires:
    • Upper bound f(3) ≤ 4: every 2-coloring of Kₙ (n large) can be
      partitioned into vertex-disjoint monochromatic triangles leaving at
      most 4 vertices. This is a nontrivial extremal-graph argument with
      case analysis on colorings that is NOT available in Mathlib.
    • Lower bound f(3) ≥ 4: an explicit family of colorings forcing ≥ 4
      leftover vertices.
  This is out of reach of a single session and of current Mathlib. The
  entry in `Erdos1015OQ01.lean` therefore keeps `moon_f3 : f 3 = 4` as an
  axiom, and moreover re-axiomatizes `f` itself (`axiom f : ℕ → ℕ`), so in
  that file the statement is uninterpreted and cannot be discharged.

  ## What this file DOES contribute (0 axioms, 0 sorries)

  Working against the **real** definitions from `Erdos1015Problem.lean`
  (`CliquePartition`, `coveredVertices`, `leftover`), we prove a genuine
  structural ingredient of any triangle-packing argument:

    A clique partition into vertex-disjoint monochromatic Kₜ's covers
    exactly (number of cliques) · t vertices. Hence the covered count is a
    multiple of t, and the leftover count satisfies

        n − leftover ≡ 0   (mod t),     i.e.   leftover ≡ n   (mod t).

  For t = 3 this says every triangle partition leaves a number of vertices
  congruent to n mod 3 — the residue constraint underlying why f(3) values
  cluster the way Moon analysed. This does not prove f(3) = 4, but it is a
  correct, machine-checked piece of the mechanism, built without adding any
  assumption on top of the parent's axioms.

  References:
  [Mo66] Moon, "Disjoint triangles in chromatic graphs" (1966)
  [BES75] Burr, Erdős, Spencer, "Ramsey theorems for multiple copies" (1975)

  Tags: graph-theory, ramsey-theory, clique-partition, combinatorics
-/

import Mathlib

open Finset

namespace Erdos1015OQ05OQ01

-- ══════════════════════════════════════════════════════════════════
-- § 0. Definitions mirrored from Erdos1015Problem.lean
--
-- These are copied verbatim (the parent `f`, `ramseyNumber`, and BES are
-- axiomatized there, so we deliberately do NOT import them: this file is
-- self-contained and free of those assumptions). Only the concrete
-- combinatorial structures are needed here.
-- ══════════════════════════════════════════════════════════════════

/-- A two-coloring of edges of a complete graph. -/
def TwoColoring (n : ℕ) := Fin n → Fin n → Bool

/-- A set of vertices forms a monochromatic clique of color `b`. -/
def isMonochromaticClique {n : ℕ} (c : TwoColoring n) (S : Finset (Fin n)) (b : Bool) :
    Prop :=
  ∀ i ∈ S, ∀ j ∈ S, i ≠ j → c i j = b

/-- A collection of vertex-disjoint sets (index-based). -/
def areDisjoint {n : ℕ} (sets : List (Finset (Fin n))) : Prop :=
  ∀ i j (hi : i < sets.length) (hj : j < sets.length), i ≠ j →
    Disjoint (sets.get ⟨i, hi⟩) (sets.get ⟨j, hj⟩)

/-- A partition into monochromatic Kₜ's with some vertices left over. -/
structure CliquePartition {n : ℕ} (c : TwoColoring n) (t : ℕ) where
  cliques : List (Finset (Fin n))
  colors : List Bool
  same_length : cliques.length = colors.length
  all_size_t : ∀ i (h : i < cliques.length), (cliques.get ⟨i, h⟩).card = t
  all_monochromatic : ∀ i (h : i < cliques.length),
    isMonochromaticClique c (cliques.get ⟨i, h⟩) (colors.get ⟨i, by omega⟩)
  disjoint : areDisjoint cliques

/-- Vertices covered by a partition. -/
def CliquePartition.coveredVertices {n : ℕ} {c : TwoColoring n} {t : ℕ}
    (p : CliquePartition c t) : Finset (Fin n) :=
  p.cliques.foldl (· ∪ ·) ∅

/-- Leftover vertices in a partition. -/
def CliquePartition.leftover {n : ℕ} {c : TwoColoring n} {t : ℕ}
    (p : CliquePartition c t) : ℕ :=
  n - p.coveredVertices.card

-- ══════════════════════════════════════════════════════════════════
-- § 1. Pairwise disjointness of the clique list
-- ══════════════════════════════════════════════════════════════════

/-- The index-based `areDisjoint` predicate implies `List.Pairwise Disjoint`. -/
theorem areDisjoint_pairwise {n : ℕ} {sets : List (Finset (Fin n))}
    (h : areDisjoint sets) : sets.Pairwise Disjoint := by
  rw [List.pairwise_iff_get]
  intro i j hij
  have hne : (i.val) ≠ (j.val) := Nat.ne_of_lt hij
  exact h i.val j.val i.isLt j.isLt hne

-- ══════════════════════════════════════════════════════════════════
-- § 2. Cardinality of a fold of pairwise-disjoint equal-size sets
-- ══════════════════════════════════════════════════════════════════

/-- Folding `∪` over a list of pairwise-disjoint Finsets, each of card `t`,
    from a starting set `init` disjoint from all of them, adds exactly
    `(list length) · t` to `init.card`. -/
private theorem card_foldl_union_aux {α : Type*} [DecidableEq α] {t : ℕ} :
    ∀ (l : List (Finset α)) (init : Finset α),
      (∀ s ∈ l, s.card = t) → l.Pairwise Disjoint →
      (∀ s ∈ l, Disjoint init s) →
      (l.foldl (· ∪ ·) init).card = init.card + l.length * t
  | [], init, _, _, _ => by simp
  | a :: l, init, hcard, hpair, hinit => by
    simp only [List.foldl_cons, List.length_cons]
    have hdisj : Disjoint init a := hinit a (by simp)
    have hacard : a.card = t := hcard a (by simp)
    have hpc := List.pairwise_cons.mp hpair
    have hrec := card_foldl_union_aux l (init ∪ a)
      (fun s hs => hcard s (by simp [hs]))
      hpc.2
      (fun s hs => by
        rw [Finset.disjoint_union_left]
        exact ⟨hinit s (by simp [hs]), hpc.1 s hs⟩)
    rw [hrec, Finset.card_union_of_disjoint hdisj, hacard]
    ring

-- ══════════════════════════════════════════════════════════════════
-- § 3. Covered vertices count exactly (number of cliques) · t
-- ══════════════════════════════════════════════════════════════════

/-- **Key structural lemma.** A clique partition covers exactly
    `(number of cliques) · t` vertices. -/
theorem coveredVertices_card {n t : ℕ} {c : TwoColoring n} (p : CliquePartition c t) :
    p.coveredVertices.card = p.cliques.length * t := by
  have hcard : ∀ s ∈ p.cliques, s.card = t := by
    intro s hs
    obtain ⟨i, rfl⟩ := List.mem_iff_get.mp hs
    exact p.all_size_t i.val i.isLt
  have hpair := areDisjoint_pairwise p.disjoint
  have hmain := card_foldl_union_aux p.cliques ∅ hcard hpair
    (fun s _ => Finset.disjoint_empty_left s)
  simpa [CliquePartition.coveredVertices] using hmain

/-- The number of covered vertices is a multiple of `t`. -/
theorem coveredVertices_card_mod {n t : ℕ} {c : TwoColoring n}
    (p : CliquePartition c t) : p.coveredVertices.card % t = 0 := by
  rw [coveredVertices_card]; exact Nat.mul_mod_left _ _

-- ══════════════════════════════════════════════════════════════════
-- § 4. The leftover residue constraint
-- ══════════════════════════════════════════════════════════════════

/-- The covered set has at most `n` vertices. -/
theorem coveredVertices_card_le {n t : ℕ} {c : TwoColoring n}
    (p : CliquePartition c t) : p.coveredVertices.card ≤ n := by
  have := Finset.card_le_univ p.coveredVertices
  simpa [Fintype.card_fin] using this

/-- `leftover = n − (number of cliques) · t`. -/
theorem leftover_eq {n t : ℕ} {c : TwoColoring n} (p : CliquePartition c t) :
    p.leftover = n - p.cliques.length * t := by
  show n - p.coveredVertices.card = n - p.cliques.length * t
  rw [coveredVertices_card]

/-- **Leftover residue constraint.** For any clique partition into Kₜ's,
    `n − leftover ≡ 0 (mod t)`; equivalently the leftover count is
    congruent to `n` modulo `t`. -/
theorem leftover_mod {n t : ℕ} {c : TwoColoring n} (p : CliquePartition c t) :
    (n - p.leftover) % t = 0 := by
  have hle : p.coveredVertices.card ≤ n := coveredVertices_card_le p
  have hlo : p.leftover = n - p.coveredVertices.card := rfl
  have hnl : n - p.leftover = p.coveredVertices.card := by omega
  rw [hnl]; exact coveredVertices_card_mod p

-- ══════════════════════════════════════════════════════════════════
-- § 5. Specialization to triangles (t = 3), the Moon setting
-- ══════════════════════════════════════════════════════════════════

/-- For triangle partitions (t = 3), the covered count is a multiple of 3. -/
theorem triangle_covered_mod3 {n : ℕ} {c : TwoColoring n}
    (p : CliquePartition c 3) : p.coveredVertices.card % 3 = 0 :=
  coveredVertices_card_mod p

/-- **Triangle leftover residue.** Every partition of a 2-colored Kₙ into
    vertex-disjoint monochromatic triangles leaves a number of vertices
    congruent to `n` modulo 3. This is the residue mechanism underlying
    Moon's analysis of f(3); it does not by itself establish f(3) = 4. -/
theorem triangle_leftover_mod3 {n : ℕ} {c : TwoColoring n}
    (p : CliquePartition c 3) : (n - p.leftover) % 3 = 0 :=
  leftover_mod p

/-- Concrete consequence: if `n ≡ 1 (mod 3)`, every triangle partition
    leaves at least 1 vertex; the covered count can never equal `n`. -/
theorem triangle_leftover_pos_of_mod3 {n : ℕ} {c : TwoColoring n}
    (p : CliquePartition c 3) (hn : n % 3 = 1) : 0 < p.leftover := by
  have hcov := triangle_covered_mod3 p
  have hle := coveredVertices_card_le p
  by_contra h
  push_neg at h
  interval_cases hlft : p.leftover
  -- leftover = 0 ⟹ covered.card = n, but n % 3 = 1 contradicts covered % 3 = 0
  have hcard : p.coveredVertices.card = n := by
    have hlo : p.leftover = n - p.coveredVertices.card := rfl
    omega
  rw [hcard, hn] at hcov
  exact absurd hcov (by norm_num)

#check @coveredVertices_card
#check @leftover_mod
#check @triangle_leftover_mod3

end Erdos1015OQ05OQ01
