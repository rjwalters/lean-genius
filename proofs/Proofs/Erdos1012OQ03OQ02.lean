/-
  # The Directed Handshake Lemma and Tournament Score Sums

  The companion file `Erdos1012OQ03` ("Directed Graph Hamiltonian Cycle Thresholds")
  introduces a `Digraph` structure with `outDegree`, `inDegree`, `arcCount`, and
  proves the headline Hamiltonicity theorems — Rédei, Moon–Moser, Ghouila–Houri,
  and the arc-count threshold. Every one of those arguments rests on *degree
  counting*, yet the underlying counting identities are never stated there.

  This file supplies them, self-contained. (It re-declares the small handful of
  digraph definitions verbatim from the companion file so that it stands on its own
  and is fully machine-checked end to end.) The central result is the **directed
  handshake lemma**:

      ∑ᵥ outDegree(v) = arcCount = ∑ᵥ inDegree(v)

  i.e. summing out-degrees and summing in-degrees both recover the total number of
  arcs (each arc `u → v` is counted once as an out-arc of `u` and once as an in-arc
  of `v`). In particular the total out-degree equals the total in-degree.

  Specialised to tournaments, where every unordered pair contributes exactly one
  arc, this pins the global statistics exactly:

  * `tournament_outDegree_add_inDegree`: `outDegree v + inDegree v = n - 1`
    (each vertex either beats or loses to every other vertex),
  * `tournament_two_mul_arcCount`: `2 * arcCount = n * (n - 1)`,
  * `tournament_two_mul_sum_outDegree`: `2 * ∑ᵥ outDegree(v) = n * (n - 1)`
    (the score sequence of a tournament sums to `n.choose 2` — the Landau identity),

  together with a pigeonhole consequence

  * `exists_outDegree_ge_average`: some vertex has `n * outDegree(v) ≥ arcCount`,

  the elementary averaging step that opens degree-threshold arguments such as
  Ghouila–Houri's.

  These are the directed analogue of Euler's handshake lemma and the standard
  bookkeeping of tournament theory.

  Tags: graph-theory, digraph, tournament, handshake-lemma, degree-sum
-/
import Mathlib

namespace Erdos1012OQ03OQ02

open Finset
open scoped Classical

variable {V : Type*} [Fintype V]

/- ============================================================
   § 0 : Digraph definitions (mirroring the companion file)
   ============================================================ -/

/-- A **simple directed graph** (digraph) on vertex type `V`: a loopless arc
    relation. (Identical to the definition in `Erdos1012OQ03`.) -/
structure Digraph (V : Type*) where
  arc : V → V → Prop
  loopless : ∀ v, ¬arc v v

/-- The out-degree of `v`: the number of vertices `u` with an arc `v → u`. -/
noncomputable def Digraph.outDegree (D : Digraph V) (v : V) : ℕ :=
  haveI : DecidablePred (D.arc v) := Classical.decPred _
  Fintype.card {u : V // D.arc v u}

/-- The in-degree of `v`: the number of vertices `u` with an arc `u → v`. -/
noncomputable def Digraph.inDegree (D : Digraph V) (v : V) : ℕ :=
  haveI : DecidablePred (fun u => D.arc u v) := Classical.decPred _
  Fintype.card {u : V // D.arc u v}

/-- A digraph is a **tournament** if every unordered pair has exactly one arc. -/
def Digraph.IsTournament (D : Digraph V) : Prop :=
  ∀ u v : V, u ≠ v → (D.arc u v ∧ ¬D.arc v u) ∨ (D.arc v u ∧ ¬D.arc u v)

/-- The total number of arcs of the digraph. -/
noncomputable def Digraph.arcCount (D : Digraph V) : ℕ :=
  letI : DecidablePred (fun p : V × V => D.arc p.1 p.2) := Classical.decPred _
  Fintype.card {p : V × V // D.arc p.1 p.2}

/- ============================================================
   § 1 : Degrees and arc count as `Finset.filter` cardinalities
   ============================================================ -/

private lemma outDegree_eq_card_filter (D : Digraph V) (v : V) :
    D.outDegree v = (univ.filter fun u => D.arc v u).card := by
  classical
  simp only [Digraph.outDegree, Fintype.card_subtype]

private lemma inDegree_eq_card_filter (D : Digraph V) (v : V) :
    D.inDegree v = (univ.filter fun u => D.arc u v).card := by
  classical
  simp only [Digraph.inDegree, Fintype.card_subtype]

private lemma arcCount_eq_card_filter (D : Digraph V) :
    D.arcCount = (univ.filter fun p : V × V => D.arc p.1 p.2).card := by
  classical
  simp only [Digraph.arcCount, Fintype.card_subtype]

/- ============================================================
   § 2 : The directed handshake lemma
   ============================================================ -/

/-- **Directed handshake lemma (out-degree form).** Summing the out-degrees over all
    vertices counts every arc exactly once, recovering the total arc count. -/
theorem sum_outDegree_eq_arcCount (D : Digraph V) :
    ∑ v : V, D.outDegree v = D.arcCount := by
  classical
  simp only [outDegree_eq_card_filter, arcCount_eq_card_filter, Finset.card_filter]
  rw [← Finset.univ_product_univ, Finset.sum_product]

/-- **Directed handshake lemma (in-degree form).** Summing the in-degrees over all
    vertices also recovers the total arc count. -/
theorem sum_inDegree_eq_arcCount (D : Digraph V) :
    ∑ v : V, D.inDegree v = D.arcCount := by
  classical
  simp only [inDegree_eq_card_filter, arcCount_eq_card_filter, Finset.card_filter]
  rw [← Finset.univ_product_univ, Finset.sum_product, Finset.sum_comm]

/-- **Conservation of degree.** The total out-degree equals the total in-degree:
    every arc leaves exactly one vertex and enters exactly one vertex. -/
theorem sum_outDegree_eq_sum_inDegree (D : Digraph V) :
    ∑ v : V, D.outDegree v = ∑ v : V, D.inDegree v := by
  rw [sum_outDegree_eq_arcCount, sum_inDegree_eq_arcCount]

/- ============================================================
   § 3 : Tournament score sums
   ============================================================ -/

/-- In a tournament, every vertex either beats or loses to each of the other `n − 1`
    vertices, so its out- and in-degrees sum to `n − 1`. -/
theorem tournament_outDegree_add_inDegree [DecidableEq V] (D : Digraph V) (hT : D.IsTournament) (v : V) :
    D.outDegree v + D.inDegree v = Fintype.card V - 1 := by
  classical
  rw [outDegree_eq_card_filter, inDegree_eq_card_filter]
  have hdisj : Disjoint (univ.filter fun u => D.arc v u) (univ.filter fun u => D.arc u v) := by
    rw [Finset.disjoint_left]
    intro u hu hu'
    rw [Finset.mem_filter] at hu hu'
    rcases hT v u (by rintro rfl; exact D.loopless v hu.2) with ⟨_, hno⟩ | ⟨_, hno⟩
    · exact hno hu'.2
    · exact hno hu.2
  rw [← Finset.card_union_of_disjoint hdisj]
  have hunion : (univ.filter fun u => D.arc v u) ∪ (univ.filter fun u => D.arc u v)
      = univ.erase v := by
    ext u
    simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_erase]
    constructor
    · rintro (h | h)
      · exact ⟨fun he => D.loopless v (he ▸ h), trivial⟩
      · exact ⟨fun he => D.loopless v (he ▸ h), trivial⟩
    · rintro ⟨hne, -⟩
      rcases hT v u (Ne.symm hne) with ⟨h, -⟩ | ⟨h, -⟩
      · exact Or.inl h
      · exact Or.inr h
  rw [hunion, Finset.card_erase_of_mem (Finset.mem_univ v), Finset.card_univ]

/-- **Tournament arc count.** A tournament on `n` vertices has exactly `n(n−1)/2`
    arcs — one per unordered pair. Stated multiplicatively to stay in `ℕ`. -/
theorem tournament_two_mul_arcCount [DecidableEq V] (D : Digraph V) (hT : D.IsTournament) :
    2 * D.arcCount = Fintype.card V * (Fintype.card V - 1) := by
  have key : 2 * D.arcCount = ∑ _v : V, (Fintype.card V - 1) := by
    rw [two_mul]
    nth_rewrite 1 [← sum_outDegree_eq_arcCount D]
    rw [← sum_inDegree_eq_arcCount D, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun v _ => tournament_outDegree_add_inDegree D hT v
  rw [key, Finset.sum_const, Finset.card_univ, smul_eq_mul]

/-- **Landau's score-sum identity.** The out-degrees (the *score sequence*) of a
    tournament sum to `n(n−1)/2`. -/
theorem tournament_two_mul_sum_outDegree [DecidableEq V] (D : Digraph V) (hT : D.IsTournament) :
    2 * ∑ v : V, D.outDegree v = Fintype.card V * (Fintype.card V - 1) := by
  rw [sum_outDegree_eq_arcCount, tournament_two_mul_arcCount D hT]

/- ============================================================
   § 4 : Averaging / pigeonhole
   ============================================================ -/

/-- **Averaging.** Some vertex has out-degree at least the average: `n · d⁺(v) ≥ arcCount`.
    This is the elementary first step of degree-threshold Hamiltonicity arguments. -/
theorem exists_outDegree_ge_average [Nonempty V] (D : Digraph V) :
    ∃ v : V, Fintype.card V * D.outDegree v ≥ D.arcCount := by
  classical
  obtain ⟨v, -, hv⟩ := univ.exists_max_image (fun v => D.outDegree v) univ_nonempty
  refine ⟨v, ?_⟩
  calc D.arcCount = ∑ u : V, D.outDegree u := (sum_outDegree_eq_arcCount D).symm
    _ ≤ ∑ _u : V, D.outDegree v := Finset.sum_le_sum fun u _ => hv u (Finset.mem_univ u)
    _ = Fintype.card V * D.outDegree v := by
        rw [Finset.sum_const, Finset.card_univ, smul_eq_mul]

end Erdos1012OQ03OQ02
