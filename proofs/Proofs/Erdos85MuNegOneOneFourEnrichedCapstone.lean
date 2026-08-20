import Proofs.Erdos85SizeTwoMuNegOneSelfCellOneFourTerminalAssembly
import Proofs.Erdos85MuNegOneOneFourFiniteSemantics

/-!
# Enriched three-mode capstone for the μ=-1 `(1,4)` cell

Node: outline F.3 (μ=-1 lane; graph→valuation bridge, increment 3c-i;
squad msg 13956).

The banked abstract capstone hands its three mode terminals only the
cross split, the sign phases, and the shore modes.  The certificate
embedding additionally needs the pointwise `±1` laws on both shores:
the sigma-coherence bridge between value equality (`su i = sv j`) and
the generator's parity classes fails for unpinned odd-coordinate
values.  This enriched variant re-runs the same routing lemmas but
keeps the pointwise laws in scope for the terminals.  The original
capstone is untouched.
-/

namespace Erdos85

noncomputable section

/-- Abstract three-certificate capstone with pointwise sign laws.  The
mixed terminal is quantified over the ordered shores; the sign laws
travel with the swap. -/
theorem muNegOneOneFour_enriched_false_of_three_mode_terminals
    {X : Type*} (R : SimpleGraph X) [DecidableRel R.Adj]
    (u v : ZMod 8 → X) (su sv : ZMod 8 → ℤ)
    (hsu : ∀ i, su i = -1 ∨ su i = 1)
    (hsv : ∀ j, sv j = -1 ∨ sv j = 1)
    (hflipu : ∀ i, su (i + 1) = -su i)
    (hflipv : ∀ j, sv (j + 1) = -sv j)
    (hgeom : MuNegOneOneFourShoreExteriorModel R u ∧
      MuNegOneOneFourShoreExteriorModel R v ∧
      MuNegOneOneFourCrossExteriorSplit R u v su sv)
    (hTFTF : MuNegOneOneFourCrossExteriorSplit R u v su sv →
      MuNegOneOneFourAlternatingSignPhases su sv →
      (∀ i, su i = -1 ∨ su i = 1) → (∀ j, sv j = -1 ∨ sv j = 1) →
      MuNegOneOneFourTfShoreMode R u →
      MuNegOneOneFourTfShoreMode R v → False)
    (hTFtri : ∀ (w x : ZMod 8 → X) (sw sx : ZMod 8 → ℤ),
      MuNegOneOneFourCrossExteriorSplit R w x sw sx →
      MuNegOneOneFourAlternatingSignPhases sw sx →
      (∀ i, sw i = -1 ∨ sw i = 1) → (∀ j, sx j = -1 ∨ sx j = 1) →
      MuNegOneOneFourTfShoreMode R w →
      MuNegOneOneFourTriangleShoreMode R x → False)
    (htritri : MuNegOneOneFourCrossExteriorSplit R u v su sv →
      MuNegOneOneFourAlternatingSignPhases su sv →
      (∀ i, su i = -1 ∨ su i = 1) → (∀ j, sv j = -1 ∨ sv j = 1) →
      MuNegOneOneFourTriangleShoreMode R u →
      MuNegOneOneFourTriangleShoreMode R v → False) : False := by
  have hmode :=
    muNegOneOneFour_completeExteriorGeometry_modeRouting R u v su sv hgeom
  have hphase := zmodEight_two_alternating_sign_phase_routing su sv
    hsu hsv hflipu hflipv
  rcases hmode.2 with htt | hmixed | hff
  · exact hTFTF hmode.1 hphase hsu hsv htt.1 htt.2
  · rcases muNegOneOneFour_mixed_mode_normalize R u v su sv hmode.1 hmixed
      with huv | hvu
    · exact hTFtri u v su sv huv.2.2 hphase hsu hsv huv.1 huv.2.1
    · exact hTFtri v u sv su hvu.2.2
        ((muNegOneOneFour_alternatingSignPhases_swap su sv).mp hphase)
        hsv hsu hvu.1 hvu.2.1
  · exact htritri hmode.1 hphase hsu hsv hff.1 hff.2

/-! ## Sigma coherence -/

/-- The generator-side sign phase selected by two alternating shores:
`false` when the coordinate-zero phases agree, `true` when they are
opposite. -/
def muNegOneSigmaOf (su sv : ZMod 8 → ℤ) : Bool :=
  decide (su 0 ≠ sv 0)

/-- Value equality between shore signs matches the generator's parity
sign classes under the selected sigma.  Generator coordinates are `Nat`
codes: row `i < 8` on the first shore, column code `8 + j` on the
second. -/
theorem muNegOneSigma_coherence (su sv : ZMod 8 → ℤ)
    (hsu : ∀ i, su i = -1 ∨ su i = 1)
    (hsv : ∀ j, sv j = -1 ∨ sv j = 1)
    (hphase : MuNegOneOneFourAlternatingSignPhases su sv)
    (i j : Nat) (hi : i < 8) (hj : j < 8) :
    (su (i : ZMod 8) = sv (j : ZMod 8)) ↔
      (muNegOneSign (muNegOneSigmaOf su sv) i ==
        muNegOneSign (muNegOneSigmaOf su sv) (8 + j)) = true := by
  obtain ⟨hsu0, hsv0, hpu, hpv, hphase0⟩ := hphase
  have hueven : ∀ k : Nat, k < 8 →
      (su (k : ZMod 8) = su 0 ↔ k % 2 = 0) := by
    intro k hk
    rw [hpu]
    unfold ZModEightEvenOffset
    interval_cases k <;> simp <;> decide
  have hveven : ∀ k : Nat, k < 8 →
      (sv (k : ZMod 8) = sv 0 ↔ k % 2 = 0) := by
    intro k hk
    rw [hpv]
    unfold ZModEightEvenOffset
    interval_cases k <;> simp <;> decide
  have hsgn : muNegOneSign (muNegOneSigmaOf su sv) i = decide (i % 2 = 1) := by
    unfold muNegOneSign
    rw [if_pos hi]
  have hsgn2 : muNegOneSign (muNegOneSigmaOf su sv) (8 + j) =
      decide ((j + (if muNegOneSigmaOf su sv then 1 else 0)) % 2 = 1) := by
    unfold muNegOneSign
    rw [if_neg (by omega)]
    congr 1
    omega
  -- Case on the two coordinate parities and the phase relation.
  have hiu := hueven i hi
  have hjv := hveven j hj
  rcases hsu (i : ZMod 8) with hui | hui <;>
    rcases hsv (j : ZMod 8) with hvj | hvj <;>
    rcases hsu 0 with hu0 | hu0 <;>
    rcases hsv 0 with hv0 | hv0 <;>
    unfold muNegOneSigmaOf <;>
    rw [hsgn2] <;> rw [hsgn] <;>
    simp only [hu0, hv0, hui, hvj] at hiu hjv ⊢ <;>
    (try omega) <;>
    (first
      | (rw [decide_eq_true (by norm_num : (-1 : ℤ) ≠ 1)]
         simp only [if_true]
         omega)
      | (rw [decide_eq_true (by norm_num : (1 : ℤ) ≠ -1)]
         simp only [if_true]
         omega)
      | (rw [decide_eq_false (by norm_num : ¬(-1 : ℤ) ≠ -1)]
         simp only [if_false]
         omega)
      | (rw [decide_eq_false (by norm_num : ¬(1 : ℤ) ≠ 1)]
         simp only [if_false]
         omega))

end

end Erdos85

#print axioms Erdos85.muNegOneOneFour_enriched_false_of_three_mode_terminals
#print axioms Erdos85.muNegOneSigma_coherence
