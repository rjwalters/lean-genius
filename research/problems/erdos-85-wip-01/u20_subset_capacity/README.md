# U20 / R14 subset-capacity exclusion

Five Lean modules prove that no admissible, externally capped cross exists for
full U compact code (9,9,16) and R representative14. The production-coordinate
`U20Hall.no_joint` theorem excludes the corresponding joint witness.

The subset {0,1,2,5,6,7,9,10,11,12,14} requires 11 cross edges by the exact row
margins. Every checked allowed column meets this subset in at most the corresponding
entry of [0,2,2,2,1,1,1,1], whose sum is 10. A double-counting identity contradicts
these two bounds. Witnessed column-domain completeness links the finite checks to
an arbitrary actual cross. No coverage tree or terminal search is used.

All five modules passed ordinary Lean checking, with nine printed exports using
only standard axioms or subsets. Exact source hashes, logs, and terminal receipts
are retained in `evidence/`. Independent review and a fresh complete portable checker run passed.

From repository proofs with imported modules built, run
`lake env python3 PACKAGE/check.py --workers 2`. The optional `--build-dir PATH`
must be empty. The checker verifies hashes, compiles all five sources in dependency
order, and audits all nine exports. Build logs and objects are retained.

This excludes pair (20,14); other representative pairs and Erdős85 remain open.
