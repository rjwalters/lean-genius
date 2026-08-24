import Proofs.Erdos85C4FreeWitnessPairingRelay
import Proofs.Erdos85EvenFinsetInvolutionPairing

/-!
# Existence of the full paired-star relay graph

An even-regular C4-free graph admits simultaneous fixed-point-free pairings
of all neighbor stars.  Their witness-indexed union is an actual regular
Eulerian relay graph.  This is the abstract existence content of the Baer
paired-star construction (73rnz_cjibkn), before imposing its finer
owner-adapted normal form.
-/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- **Paired-star relay existence.**  Every C4-free `q`-regular graph with
even `q` admits local neighbor-star mates whose global relay is again
`q`-regular (and therefore Eulerian). -/
theorem exists_c4Free_evenRegular_neighborStar_relay
    {V : Type*} [Fintype V] [DecidableEq V]
    (A : SimpleGraph V) [DecidableRel A.Adj]
    (hfree : ¬ containsC4 V A) (q : ℕ)
    (hreg : ∀ v, A.degree v = q) (hq : Even q) :
    ∃ (mate : V → V → V)
      (hclosed : ∀ w v, A.Adj w v → A.Adj w (mate w v))
      (hinvol : ∀ w v, A.Adj w v → mate w (mate w v) = v)
      (hfixed : ∀ w v, A.Adj w v → mate w v ≠ v),
      (∀ w v, ¬ A.Adj w v → mate w v = v) ∧
      (∀ v,
        (witnessPairingRelayGraph A.Adj mate
          hclosed hinvol hfixed).degree v = q) ∧
      (∀ v, Even
        ((witnessPairingRelayGraph A.Adj mate
          hclosed hinvol hfixed).degree v)) := by
  have hevenFiber : ∀ w,
      Even ((Finset.univ.filter fun v => A.Adj w v).card) := by
    intro w
    have hcard : (Finset.univ.filter fun v => A.Adj w v).card = A.degree w := by
      simpa [A.adj_comm] using neighborStar_witnessFiber_card A w
    rw [hcard, hreg]
    exact hq
  obtain ⟨mate, hclosed, hinvol, hfixed, houtside⟩ :=
    exists_witnessMate_of_even_fibers A.Adj hevenFiber
  refine ⟨mate, hclosed, hinvol, hfixed, houtside, ?_, ?_⟩
  · intro v
    exact c4Free_neighborStar_relay_degree_eq A hfree mate
      hclosed hinvol hfixed q hreg v
  · intro v
    exact c4Free_neighborStar_relay_even_degree A hfree mate
      hclosed hinvol hfixed q hreg hq v

end

end Erdos85

#print axioms Erdos85.exists_c4Free_evenRegular_neighborStar_relay
