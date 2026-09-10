# U32/R14 empty-table certificate

All 41 modules passed ordinary Lean checks, with 45 printed exports using only standard axioms or subsets. Independent final review is pending; the full portable checker has not been rerun.

This package excludes full U representative 32, compact code (9,10,58), paired with R representative 14. Its ordered column tree has 120246 subtree nodes and zero leaves. The table has type Fin 0 → ThreeHighCross, so its entry rejection follows from Fin.elim0.

Zero32Inputs checks 1728 domain reasons, production coordinates, valid R swaps, and empty-table rejection. The 36 Zero32Shard modules check all depth-two subtrees. Zero32Structure assembles those premises in domain order; Zero32Assembly supplies all checked proofs. Zero32Exclusion uses the witnessed-domain coverage theorem to exclude an actual cross under its cross-domain and external-cap hypotheses.

From the repository proofs directory:

```sh
lake env python3 /path/to/package/check.py --build-dir /new/empty/build-directory
```

The checker validates source hashes, stages dependencies, and checks all 45 exports. Defaults are two workers and 180 seconds per module. It rejects nonempty build directories and places fresh outputs first in LEAN_PATH. Evidence retains every module log and terminal receipt. The largest pilot, shard 5, passed independent review 1979 before the remaining 35 checks started.

This is one fixed-pair exclusion. The other pairs and the broader Erdős 85 problem remain open.
