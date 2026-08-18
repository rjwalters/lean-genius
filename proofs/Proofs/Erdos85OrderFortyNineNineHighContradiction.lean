import Proofs.Erdos85OrderFortyNineT2RepACertificate
import Proofs.Erdos85OrderFortyNineT2RepBCertificate
import Proofs.Erdos85OrderFortyNineT3Rep0Certificate
import Proofs.Erdos85OrderFortyNineT3Rep1Certificate
import Proofs.Erdos85OrderFortyNineT3Rep2Certificate
import Proofs.Erdos85OrderFortyNineT3Rep3Certificate
import Proofs.Erdos85OrderFortyNineT3Rep4Certificate
import Proofs.Erdos85OrderFortyNineT4Rep0Certificate
import Proofs.Erdos85OrderFortyNineT4Rep1Certificate
import Proofs.Erdos85OrderFortyNineT4Rep2Certificate
import Proofs.Erdos85OrderFortyNineT4Rep3Certificate
import Proofs.Erdos85OrderFortyNineT4Rep4Certificate
import Proofs.Erdos85OrderFortyNineT4Rep5Certificate
import Proofs.Erdos85OrderFortyNineT4Rep6Certificate
import Proofs.Erdos85OrderFortyNineT4Rep7Certificate
import Proofs.Erdos85OrderFortyNineT4Rep8Certificate
import Proofs.Erdos85OrderFortyNineT4Rep9Certificate
import Proofs.Erdos85OrderFortyNineT4Rep10Certificate
import Proofs.Erdos85OrderFortyNineCheckedTerminal

/-! # Closed checked-certificate contradiction for the nine-high order-49 stratum -/

namespace Erdos85

open Std.Tactic.BVDecide

theorem orderFortyNineT2_member_cases
    (rep : OrderFortyNineH9System)
    (hrep : rep ∈ orderFortyNineH9T2Systems) :
    rep = orderFortyNineH9T2Systems[0]! ∨
      rep = orderFortyNineH9T2Systems[1]! := by
  native_decide +revert

theorem orderFortyNineT3_member_cases
    (rep : OrderFortyNineH9System)
    (hrep : rep ∈ orderFortyNineH9T3Systems) :
    rep = orderFortyNineH9T3Systems[0]! ∨
      rep = orderFortyNineH9T3Systems[1]! ∨
      rep = orderFortyNineH9T3Systems[2]! ∨
      rep = orderFortyNineH9T3Systems[3]! ∨
      rep = orderFortyNineH9T3Systems[4]! := by
  native_decide +revert

theorem orderFortyNineT4_member_cases
    (rep : OrderFortyNineH9System)
    (hrep : rep ∈ orderFortyNineH9T4Systems) :
    rep = orderFortyNineH9T4Systems[0]! ∨
      rep = orderFortyNineH9T4Systems[1]! ∨
      rep = orderFortyNineH9T4Systems[2]! ∨
      rep = orderFortyNineH9T4Systems[3]! ∨
      rep = orderFortyNineH9T4Systems[4]! ∨
      rep = orderFortyNineH9T4Systems[5]! ∨
      rep = orderFortyNineH9T4Systems[6]! ∨
      rep = orderFortyNineH9T4Systems[7]! ∨
      rep = orderFortyNineH9T4Systems[8]! ∨
      rep = orderFortyNineH9T4Systems[9]! ∨
      rep = orderFortyNineH9T4Systems[10]! := by
  native_decide +revert

theorem orderFortyNineT2_lratChecks :
    ∀ rep ∈ orderFortyNineH9T2Systems,
      ∃ proof : Array LRAT.IntAction,
        LRAT.check proof
          (orderFortyNineGeneratedSatCnf
            (orderFortyNineH9ProfileMasks rep)) := by
  intro rep hrep
  rcases orderFortyNineT2_member_cases rep hrep with
    h0 |
    h1
  · subst rep
    exact ⟨orderFortyNineT2RepAProof, orderFortyNineT2RepA_check⟩
  · subst rep
    exact ⟨orderFortyNineT2RepBProof, orderFortyNineT2RepB_check⟩

theorem orderFortyNineT3_lratChecks :
    ∀ rep ∈ orderFortyNineH9T3Systems,
      ∃ proof : Array LRAT.IntAction,
        LRAT.check proof
          (orderFortyNineGeneratedSatCnf
            (orderFortyNineH9ProfileMasks rep)) := by
  intro rep hrep
  rcases orderFortyNineT3_member_cases rep hrep with
    h0 |
    h1 |
    h2 |
    h3 |
    h4
  · subst rep
    exact ⟨orderFortyNineT3Rep0Proof, orderFortyNineT3Rep0_check⟩
  · subst rep
    exact ⟨orderFortyNineT3Rep1Proof, orderFortyNineT3Rep1_check⟩
  · subst rep
    exact ⟨orderFortyNineT3Rep2Proof, orderFortyNineT3Rep2_check⟩
  · subst rep
    exact ⟨orderFortyNineT3Rep3Proof, orderFortyNineT3Rep3_check⟩
  · subst rep
    exact ⟨orderFortyNineT3Rep4Proof, orderFortyNineT3Rep4_check⟩

theorem orderFortyNineT4_lratChecks :
    ∀ rep ∈ orderFortyNineH9T4Systems,
      ∃ proof : Array LRAT.IntAction,
        LRAT.check proof
          (orderFortyNineGeneratedSatCnf
            (orderFortyNineH9ProfileMasks rep)) := by
  intro rep hrep
  rcases orderFortyNineT4_member_cases rep hrep with
    h0 |
    h1 |
    h2 |
    h3 |
    h4 |
    h5 |
    h6 |
    h7 |
    h8 |
    h9 |
    h10
  · subst rep
    exact ⟨orderFortyNineT4Rep0Proof, orderFortyNineT4Rep0_check⟩
  · subst rep
    exact ⟨orderFortyNineT4Rep1Proof, orderFortyNineT4Rep1_check⟩
  · subst rep
    exact ⟨orderFortyNineT4Rep2Proof, orderFortyNineT4Rep2_check⟩
  · subst rep
    exact ⟨orderFortyNineT4Rep3Proof, orderFortyNineT4Rep3_check⟩
  · subst rep
    exact ⟨orderFortyNineT4Rep4Proof, orderFortyNineT4Rep4_check⟩
  · subst rep
    exact ⟨orderFortyNineT4Rep5Proof, orderFortyNineT4Rep5_check⟩
  · subst rep
    exact ⟨orderFortyNineT4Rep6Proof, orderFortyNineT4Rep6_check⟩
  · subst rep
    exact ⟨orderFortyNineT4Rep7Proof, orderFortyNineT4Rep7_check⟩
  · subst rep
    exact ⟨orderFortyNineT4Rep8Proof, orderFortyNineT4Rep8_check⟩
  · subst rep
    exact ⟨orderFortyNineT4Rep9Proof, orderFortyNineT4Rep9_check⟩
  · subst rep
    exact ⟨orderFortyNineT4Rep10Proof, orderFortyNineT4Rep10_check⟩

theorem false_of_orderFortyNine_nine_high
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    (hmin : ∀ x : V, 7 ≤ G.degree x)
    (hcard : Fintype.card V = 49)
    (hHigh : (orderFortyNineHighVertices G).card = 9) : False := by
  rcases orderFortyNine_highIncidence_profile_of_nine_high_final_three
      G hfree hmin hcard hHigh with hp | hp | hp
  · exact false_of_orderFortyNine_t2_of_lratChecks
      G hfree hmin hcard hHigh hp.2.2.2 orderFortyNineT2_lratChecks
  · exact false_of_orderFortyNine_t3_of_lratChecks
      G hfree hmin hcard hHigh hp.2.2.2 orderFortyNineT3_lratChecks
  · exact false_of_orderFortyNine_t4_of_lratChecks
      G hfree hmin hcard hHigh hp.2.2.2 orderFortyNineT4_lratChecks

end Erdos85
