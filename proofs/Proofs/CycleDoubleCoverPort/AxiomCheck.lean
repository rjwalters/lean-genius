import Proofs.CycleDoubleCoverPort.PathCut

/- TEMPORARY axiom-audit module for the step-5b slice; deleted before the PR. -/

namespace CycleDoubleCover
namespace FiniteGraph

-- FlowCount.lean
#print axioms endSum
#print axioms endSum_eq_sum_filter
#print axioms endSum_add
#print axioms endSum_neg
#print axioms endSum_zsmul
#print axioms divergence
#print axioms isFlow_iff_divergence
#print axioms divergence_add
#print axioms divergence_neg
#print axioms divergence_sub
#print axioms divergence_zsmul
#print axioms isFlow_add
#print axioms isFlow_neg
#print axioms isFlow_sub
#print axioms isFlow_int_smul
#print axioms NowhereZeroFlows
#print axioms Flows
#print axioms ZeroOnFlows
#print axioms zeroOnFlowsUnivEquiv
#print axioms card_zeroOnFlows_univ
#print axioms zeroOnFlowsCongr
#print axioms card_zeroOnFlows_eq_of_addEquiv
#print axioms unitChain
#print axioms unitChain_of_ne
#print axioms endSum_unitChain
#print axioms divergence_unitChain
#print axioms HasIntegerPath
#print axioms hasIntegerPath_refl
#print axioms hasIntegerPath_single
#print axioms HasIntegerPath.symm
#print axioms HasIntegerPath.trans
#print axioms HasCycleCorrection
#print axioms hasCycleCorrection_of_integerPath
#print axioms allowEdgeEquivOf
#print axioms allowEdgeEquiv
#print axioms card_zeroOnFlows_erase_of_cycleCorrection
#print axioms IsForcedZero
#print axioms sum_divergence_eq_cut
#print axioms not_crosses_iff
#print axioms crosses_iff
#print axioms HasCutSeparation
#print axioms isForcedZero_of_cutSeparation
#print axioms allowForcedEdgeEquiv
#print axioms card_zeroOnFlows_erase_of_forced
#print axioms FlowReduction
#print axioms card_zeroOnFlows_eq_of_reduction
#print axioms card_nowhereZeroFlows_eq_sum_zeroOn
#print axioms card_nowhereZeroFlows_eq_of_zeroOn
#print axioms ZeroOnCardinalityInvariant
#print axioms zeroOnCardinalityInvariant_of_reductions
#print axioms reductions_of_step_classification
#print axioms zeroOnCardinalityInvariant_of_step_classification
#print axioms IntegralPathCutDichotomy
#print axioms zeroOnCardinalityInvariant_of_pathCut
#print axioms FlowCardinalityInvariant
#print axioms flowCardinalityInvariant_of_zeroOn
#print axioms flowCardinalityInvariant_of_pathCut
#print axioms nowhereZeroFlowEquiv
#print axioms transfer_of_cardinality
#print axioms card_zmodEight_eq_gamma
#print axioms zmodEight_to_gamma
#print axioms sixFlow_to_gamma
#print axioms sixFlow_to_gamma_of_pathCut

-- PathCut.lean
#print axioms integralPathCutDichotomy
#print axioms tutteFlowCardinalityInvariant
#print axioms zmodEight_to_gamma_unconditional
#print axioms sixFlow_to_gamma_unconditional
#print axioms nonempty_nowhereZeroFlow_gamma_of_seymour

end FiniteGraph
end CycleDoubleCover
