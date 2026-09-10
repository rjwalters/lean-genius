# Local H1 DRAT inventory, unreplayed

The editor supplied 20 historically verified and 25 historically not-verified DRAT tag lists. All 45 tags are distinct frozen H1 cases; none overlaps the reviewed 95-case MONO historical overlay. All 97 located tag-named verdict records say CUBE25. The 45 are a subset of the 1,257 H1 targets, not additional targets and not newly closed cases.

A read-only archive scan found 55 nonempty `cubes-<tag>.v2` directories. Every one of 710 retained `cN.cnf` inputs reconstructs to its tag's unique frozen base SHA256 after removing exactly two final unit clauses and reducing the DIMACS header clause count by two. The original cube hash, two units, reconstructed base hash, and expected frozen hash are recorded per file. No solver or proof replay ran; no archived file was changed.

Retained CNFs cover 38 of 45 tags. Taking the union of retained directory copies, 18 tags have all 25 input filenames, 27 have all 25 proof filenames, and 18 have both. No same-tag/same-cube-name retained input has conflicting unit pairs. These are filename-availability counts, not proof validity or a mathematical cube-cover proof. The seven tags without any retained cube input cannot receive an input-identity claim from this audit. Missing inputs or proofs, CUBE25 coverage, and proof verification remain separate obligations.

`inventory.json` retains the 45 rows and proof paths/sizes; no proof bytes were read. `results.json` holds all cube/base comparisons. `cube-directories.json` and `tag-named-paths.json` retain the archive scan. The exact editor lists are copied with hashes in the receipt. `audit.py` preserves the executed local experiment (machine-specific source paths); it reads CNFs and produces small JSON, never CNFs or proofs. This package does not authorize trimming, uploading, deletion, or reclassification as closed.

Independent review 2016 passed: all list/set/count joins and package pins were checked, and 40 sampled cube inputs were independently rehashed and reconstructed to their frozen bases. The 5×5 cube-cover argument and per-cube historical verification records remain separate work; the review does not establish proof validity.
