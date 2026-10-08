# H5Fast: independent soundness and build review

The optimized conditional soundness link passed the read-only cloud audit.
Job `20261008T112110-erdos85__h5-formal-20261008-450285` exited zero at
`f7117ae8d261c6a0ad7176503983d6938532c1ae`, freshly building H5Fast in 4.7 seconds.
Its source is byte-identical at the reviewed 40-part build commit
`99bc3e3413008ca13d5efb29bee5e855af961976`.

Both printed exports use exactly `propext`, `Classical.choice`, `Quot.sound`:

- `Erdos85.H5.searchF_sound`;
- `Erdos85.H5.fiveHighCanonicalRepresentativeExcluded_of_partsF`.

The audit binds the execution commit, retained source and raw job records,
nonempty object, build interval and axiom reports. Source and object hashes
were stable across two observations. H3PairEngine, H5Engine and H5Bridge
sources and objects match the prior independent review in
`../h5_engine_review_20261008/`. No `sorry` or additional trust escape was
found. The audit runs no Lean build or finite search.

## Source review

`foldl_or_testBit` identifies bits in the union of neighbour rows.
`okF_of_allowed` uses it to show that every admissible edge satisfies the
optimized bit test. `vertDead_sound` uses the model's required colour
neighbour: a full vertex contradicts the missing required edge, while the
other branch contradicts admissibility of that neighbour. `deadAll_sound`
lifts this argument over the core vertices.

`dfs1G_sound_fam` retains an arbitrary remaining clause list and the whole
family of leaf tests. Twin transport preserves the family indices and uses
the same remaining clauses. The edge insertion arguments retain
well-formedness and compatibility. The split argument selects the prefix
state's own residue when the number of parts is positive; it does not assume
that hashing is invariant under relabelling.

No issue was found in these links or `partsF_sound`. This is a soundness
review, not a proof that the optimized and original searches visit identical
trees.

## Scope and calibration

The retained successful calibration log reports 151 seconds for CalibB
(optimized) and 209 seconds for CalibA (original). These are module elapsed
times in that build, not isolated CPU measurements or a bound on other parts.

This review credits the conditional link only. It does not audit the native
calibration premises or assert completion of the 40 production parts or the
H5 stratum. At the time of this review, Claude's separate production job
`20261008T112746-erdos85__h5-formal-20261008-455708` was still pending.
