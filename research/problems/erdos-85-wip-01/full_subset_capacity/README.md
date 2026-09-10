# Thirteen full-pair subset-capacity certificates

All13 pair certificates and the combined theorem passed ordinary Lean checks:40 modules,120 printed exports using standard axioms or subsets. The12-case batch and final assembly completed in137.24s with2workers. Independent final-source and package reviews are pending; the full portable checker was not rerun.

The proposed family is U20×R{3,14,15,16} and U26×R{3,6,8,12,14,15,16,17,18}. U20 is compact(9,9,16), U26 compact(9,9,82). Each certificate selects U rows whose required cross-degree total exceeds the sum of all eight allowed column maxima. An actual cross would violate this counting inequality.

For each pair, Data defines literal U/R adjacency, complete candidate column lists, a row subset, and capacity bounds. Inputs checks the domain reasons, production-coordinate equalities, every listed column bound, and strict total deficit. Exclusion applies the generic witnessed-domain capacity theorem and exports both impossibility and no_joint at production coordinates. No tree, ordering, joint witness, orbit representative or per-leaf rejection is needed.

SubsetCapacityBatch lists the13 pairs and combines their individual proofs. Its U/R arrays are the explicit production compact/secondary definitions; transport to the full-U representative array and removal from the actual275 obligations is a separate downstream artifact. The broader Erdős85 problem remains unresolved.

Reproduce from the repository proofs directory:

```sh
lake env python3 /path/to/package/check.py --build-dir /new/empty/build-directory
```

The checker verifies40 source hashes, follows the dependency stages, and expects120 printed exports using only standard axioms or subsets. It uses two workers and180-second per-module limits by default, stops scheduling after failure, preserves logs and receipts, and requires an empty build directory placed first on LEAN_PATH. A Python survey or numeric witness audit alone does not establish any Lean theorem.
