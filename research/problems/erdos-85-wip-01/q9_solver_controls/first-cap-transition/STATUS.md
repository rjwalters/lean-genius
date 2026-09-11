# First one-hour transitions

N80/m10 run002 ended UNKNOWN at3600.009144542 seconds; N80/m8 run003 ended UNKNOWN at3600.010286708 seconds. Both were stopped at their wall caps (exit−15), neither log has a SAT/UNSAT status line, and no SAT was observed. These are inconclusive attempts, not action-class exclusions.

N63/m7 run004 used the freed slot and returned SAT in15.332060083 seconds. The decoded control has63 vertices,252 edges, degree8 throughout, no C4 and nine free7-cycles. The separate control artifact and independent review bind the exact model and adjacency.

The controller then launched the single authorized4-hour requeues: run005 N80/m10 PID35563 and run006 N80/m8 PID38298. Both retain their original CNF/map hashes and seed0; there are exactly two live solver processes at this snapshot. Terminal solver time including controls is7592.599376292 seconds. Active requeues continue accruing time against the unchanged48-hour aggregate budget.

Terminal receipts/logs/maps and the new control CNF are preserved. The original q9 CNFs are already archived under amended-launch/inputs; hashes bind them to these receipts. Live-launch records are timestamped observations, not final verdicts. No solver was launched by the audit checker. Its first diagnostic assumed all completed attempts were UNKNOWN and correctly stopped when the newly completed control was SAT; the final checker explicitly validates that control against the independent receipt.
