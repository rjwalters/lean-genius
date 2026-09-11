import Proofs.Erdos85Problem
import Mathlib.Dynamics.PeriodicPts.Lemmas

namespace Erdos85

/-- A free prime-period map on a set of prime cardinality has a single orbit. -/
theorem exists_iterate_eq_of_prime_card
    {V : Type*} [Fintype V] (τ : V → V) {p : ℕ} [Fact p.Prime]
    (hcard : Fintype.card V = p) (hperiod : τ^[p] = id)
    (hfix : ∀ v, τ v ≠ v) (x y : V) :
    ∃ i : Fin p, τ^[i.val] x = y := by
  classical
  have hmin : Function.minimalPeriod τ x = p :=
    Function.minimalPeriod_eq_prime (congrFun hperiod x) (hfix x)
  let f : Fin p → V := fun i => τ^[i.val] x
  have hinj : Function.Injective f := by
    intro i j hij
    apply Fin.ext
    exact (Function.iterate_eq_iterate_iff_of_lt_minimalPeriod
      (by simpa only [hmin] using i.isLt) (by simpa only [hmin] using j.isLt)).mp hij
  have hsurj : Function.Surjective f := by
    by_contra h
    have hlt := Fintype.card_lt_of_injective_not_surjective f hinj h
    simp only [Fintype.card_fin, hcard, lt_self_iff_false] at hlt
  exact hsurj y

/-- An invariant matching on a free orbit of odd prime size has no edges. -/
theorem not_adj_of_prime_card_free_map_degree_le_one
    {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (τ : V → V) {p : ℕ} [Fact p.Prime]
    (hcard : Fintype.card V = p) (hodd : Odd p)
    (hperiod : τ^[p] = id) (hfix : ∀ v, τ v ≠ v)
    (hmap : ∀ {x y}, G.Adj x y → G.Adj (τ x) (τ y))
    (hdegree : ∀ v, G.degree v ≤ 1) (x y : V) : ¬ G.Adj x y := by
  classical
  intro hxy
  have hiter : ∀ n, G.Adj (τ^[n] x) (τ^[n] y) := by
    intro n
    induction n with
    | zero => exact hxy
    | succ n ih =>
      simpa only [Function.iterate_succ_apply'] using hmap ih
  have hreg : ∀ v, G.degree v = 1 := by
    intro v
    obtain ⟨i, hi⟩ := exists_iterate_eq_of_prime_card τ hcard hperiod hfix x v
    apply SimpleGraph.degree_eq_one_iff_existsUnique_adj.mpr
    refine ⟨τ^[i.val] y, ?_, ?_⟩
    · simpa only [hi] using hiter i.val
    · intro w hw
      have hle : (G.neighborFinset v).card ≤ 1 := hdegree v
      apply Finset.card_le_one.mp hle
      · exact (G.mem_neighborFinset v w).mpr hw
      · exact (G.mem_neighborFinset v (τ^[i.val] y)).mpr
          (by simpa only [hi] using hiter i.val)
  have heven : Even (Fintype.card V) := by
    have h := G.even_card_odd_degree_vertices
    simpa [hreg] using h
  rw [hcard] at heven
  exact (Nat.not_even_iff_odd.mpr hodd) heven

end Erdos85
