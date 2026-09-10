# Fixed-pair coverage certificate

All 42 coverage modules and both final-link modules passed ordinary Lean checks in the retained staged builds: 47 printed declarations, all using only standard axioms or subsets. The full 34-shard batch completed in 1230.21 seconds; root assembly passed in 5.19 seconds and final exclusion in 8.12 seconds. Independent final package review is pending.

This package covers the full U compact code (6,6,15), R secondary representative14. It uses explicit complete column domains, validated R swaps and a tree with 140 listed leaves. Rejection of those leaves is supplied separately by the repository's fixed_pair_rejections package. Erdős85 is not resolved by this single pair.

To reproduce the coverage checks, run from the repository `proofs` directory:

```sh
lake env python3 /path/to/coverage_package/check.py --build-dir /new/empty/build-directory
```

The checker verifies 42 source hashes, compiles in dependency order, and expects 43 printed declarations with only propext, Classical.choice and Quot.sound (or subsets). It uses two workers and a 180-second limit per module by default. A failed or timed-out module stops further scheduling. Logs, compiled objects and individual receipts remain in the supplied build directory. That directory must initially be empty and is placed first in LEAN_PATH.

LiteralData defines the numeric data. CoverageCoordinates connects its adjacency functions to production definitions. DomainReasons checks positional witnesses for domain completeness; Inputs supplies valid R swaps. LiteralDataPilot and LeafPilot are subtrees31 and16. CoverageShardN supplies each of the other34 subtrees. CoverageAssemblyStructure takes all36 checks explicitly and assembles the two upper branch levels; CoverageAssembly supplies the concrete checked subtrees.

The original numerical batch, the two independently reviewed pilots, and the independent literal-data receipt are separate retained evidence. A fresh full invocation of this portable checker has not yet been run. Complete source checking must be distinguished from the Python proposal of the tree.

After coverage and the separate fixed_pair_rejections package both compile, check the two final links with:

```sh
lake env python3 /path/to/coverage_package/check_exclusion.py \
  --coverage-build /checked/coverage-build \
  --rejections-build /checked/rejections-build \
  --build-dir /new/empty/final-build
```

If the rejection modules and their representative modules were compiled in different directories, also supply `--representatives-build`. A fresh portable rejection-package build places them together and needs no extra argument. EXCLUSION_MANIFEST.json pins TableRejections and FixedPairExclusion. Their successful compilation establishes this fixed pair's exclusion under the explicit cross-domain and external-cap hypotheses; the other U/R pairs and other strata remain separate obligations.
