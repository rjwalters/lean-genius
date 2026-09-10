# R-swap gate on the recorded eight crosses

Ordinary Lean kernel checks prove that the R14 swap table passes runtime validation, and that the executable binary-score ordering gate retains exactly input indices0 and6 among eight explicit cross matrices. The matrices are copied exactly from the earlier bounded Lean traversal's standalone terminal batch. This certificate checks the gate results; it does not prove exhaustive cross enumeration, the cross-domain conditions, terminal rejections, or total runtime improvement.

The generic wrapper separately proves joint-witness completeness and validates the swap data once before cross enumeration. Generated C inspection confirms ordering precedes the terminal callback. The original Python orbit representatives were labelled0 and2; the numeric-score ordering chooses leaves0 and6. Those are different choices of orbit representative, so indices must not be conflated.

Compile from the integration proofs directory after building RSwapJointSearch and RSwapTable:

```
lake env lean ../research/problems/erdos-85-wip-01/r_swap_gate_canary/GateCanary.lean
```

Both exported facts use only standard axioms or subsets; no native_decide or sorry.
