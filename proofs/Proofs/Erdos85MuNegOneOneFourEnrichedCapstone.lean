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
  have hUeq : ∀ k : Nat, k < 8 → (su (k : ZMod 8) = su 0 ↔ k % 2 = 0) := by
    intro k hk
    rw [hpu]
    interval_cases k <;> decide
  have hVeq : ∀ k : Nat, k < 8 → (sv (k : ZMod 8) = sv 0 ↔ k % 2 = 0) := by
    intro k hk
    rw [hpv]
    interval_cases k <;> decide
  have hU : ∀ k : Nat, k < 8 →
      su (k : ZMod 8) = (if k % 2 = 0 then su 0 else -su 0) := by
    intro k hk
    by_cases hk2 : k % 2 = 0
    · rw [if_pos hk2]
      exact (hUeq k hk).mpr hk2
    · rw [if_neg hk2]
      rcases hsu (k : ZMod 8) with h | h <;> rcases hsu0 with h0 | h0 <;>
        rw [h, h0] <;>
        first
          | norm_num
          | (exfalso; exact hk2 ((hUeq k hk).mp (by rw [h, h0])))
  have hV : ∀ k : Nat, k < 8 →
      sv (k : ZMod 8) = (if k % 2 = 0 then sv 0 else -sv 0) := by
    intro k hk
    by_cases hk2 : k % 2 = 0
    · rw [if_pos hk2]
      exact (hVeq k hk).mpr hk2
    · rw [if_neg hk2]
      rcases hsv (k : ZMod 8) with h | h <;> rcases hsv0 with h0 | h0 <;>
        rw [h, h0] <;>
        first
          | norm_num
          | (exfalso; exact hk2 ((hVeq k hk).mp (by rw [h, h0])))
  -- reduce the generator side to arithmetic parities.
  have hR : ((muNegOneSign (muNegOneSigmaOf su sv) i ==
        muNegOneSign (muNegOneSigmaOf su sv) (8 + j)) = true) ↔
      ((i % 2 = 1) ↔
        ((j + (if muNegOneSigmaOf su sv then 1 else 0)) % 2 = 1)) := by
    have h1 : (muNegOneSign (muNegOneSigmaOf su sv) i = true) ↔
        i % 2 = 1 := by
      unfold muNegOneSign
      rw [if_pos hi]
      exact beq_iff_eq
    have h2 : (muNegOneSign (muNegOneSigmaOf su sv) (8 + j) = true) ↔
        (j + (if muNegOneSigmaOf su sv then 1 else 0)) % 2 = 1 := by
      unfold muNegOneSign
      rw [if_neg (by omega), show (8 + j) % 8 = j from by omega]
      exact beq_iff_eq
    rw [beq_iff_eq, Bool.eq_iff_iff, h1, h2]
  rw [hR, hU i hi, hV j hj]
  rcases hphase0 with hph | hph
  · -- equal phases: sigma is false.
    have hsig : muNegOneSigmaOf su sv = false := by
      unfold muNegOneSigmaOf
      exact decide_eq_false (not_not_intro hph)
    rw [hsig, hph]
    rcases hsv0 with h0 | h0 <;>
      rcases Nat.mod_two_eq_zero_or_one i with hi2 | hi2 <;>
      rcases Nat.mod_two_eq_zero_or_one j with hj2 | hj2 <;>
      rw [h0] <;>
      simp only [hi2, hj2, if_true, if_false, Bool.false_eq_true,
        Nat.add_zero] <;>
      omega
  · -- opposite phases: sigma is true.
    have hne : su 0 ≠ sv 0 := by
      rcases hsv0 with h0 | h0 <;> rw [h0] at hph ⊢ <;> omega
    have hsig : muNegOneSigmaOf su sv = true := by
      unfold muNegOneSigmaOf
      exact decide_eq_true hne
    rw [hsig, hph]
    rcases hsv0 with h0 | h0 <;>
      rcases Nat.mod_two_eq_zero_or_one i with hi2 | hi2 <;>
      rcases Nat.mod_two_eq_zero_or_one j with hj2 | hj2 <;>
      rw [h0] <;>
      simp only [hi2, hj2, if_true, if_false, Bool.true_eq_true] <;>
      omega

end

end Erdos85

#print axioms Erdos85.muNegOneOneFour_enriched_false_of_three_mode_terminals
#print axioms Erdos85.muNegOneSigma_coherence
