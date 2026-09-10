import Proofs.Erdos85OrderFortyNineThreeHighTripleBlockCapacity

/-! A finite Boolean common-neighbor filter is necessary for every injectively
encoded subgraph of a C4-free graph. -/
namespace Erdos85
open SimpleGraph

def encodedC4Free {W : Type*} [Fintype W] [DecidableEq W]
    (B : W → W → Bool) : Bool :=
  decide (∀ p q : W, p ≠ q →
    (Finset.univ.filter fun x => B p x && B q x).card ≤ 1)

theorem encodedC4Free_of_injective_graph
    {V W : Type*} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hfree : ¬ containsC4 V G)
    (f : W → V) (hinj : Function.Injective f) (B : W → W → Bool)
    (hB : ∀ p q, decide (G.Adj (f p) (f q)) = B p q) :
    encodedC4Free B = true := by
  apply decide_eq_true_iff.mpr
  intro p q hpq
  apply Finset.card_le_one.mpr
  intro a ha b hb
  apply hinj
  have hc := (not_containsC4_iff_forall_common_le_one G).mp hfree (f p) (f q)
    (fun he => hpq (hinj he))
  have hmem {x : W} (hx : x ∈ Finset.univ.filter (fun x => B p x && B q x)) :
      f x ∈ G.neighborFinset (f p) ∩ G.neighborFinset (f q) := by
    have hh := (Finset.mem_filter.mp hx).2
    have hb : B p x = true ∧ B q x = true := by simpa using hh
    exact Finset.mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr
      (of_decide_eq_true ((hB p x).trans hb.1)),
      (G.mem_neighborFinset _ _).mpr (of_decide_eq_true ((hB q x).trans hb.2))⟩
  exact Finset.card_le_one.mp hc (f a) (hmem ha) (f b) (hmem hb)

end Erdos85
#print axioms Erdos85.encodedC4Free_of_injective_graph
