import Proofs.CycleDoubleCoverPort.JaegerKilpatrickPacking

-- TEMPORARY axiom-audit module for the JaegerKilpatrickPacking segment.
-- Deleted before the PR is opened; never committed to main.

open CycleDoubleCover FiniteGraph

#print axioms CycleDoubleCover.FiniteGraph.mem_classFinset
#print axioms CycleDoubleCover.FiniteGraph.classFinset_nonempty
#print axioms CycleDoubleCover.FiniteGraph.classFinset_ne_univ
#print axioms CycleDoubleCover.FiniteGraph.crossingEdges_doubleGraph_card
#print axioms CycleDoubleCover.FiniteGraph.mem_cut_classFinset
#print axioms CycleDoubleCover.FiniteGraph.sum_card_cut_classFinset
#print axioms
  CycleDoubleCover.FiniteGraph.doubleGraph_satisfiesTreePackingCondition_of_threeEdgeConnected
#print axioms CycleDoubleCover.FiniteGraph.exists_three_spanningTrees_omitting_each_edge
#print axioms CycleDoubleCover.FiniteGraph.nowhereZeroGammaFlow_of_threeEdgeConnected
