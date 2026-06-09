# Lean files for fermat-defect-one

- `proofs/Proofs/FermatDefectOne.lean` — main formalization. Contains:
  - The four predicates (`FermatDefectWitness`, `FermatDefectExists`,
    `FermatDefectPositive`, `FermatDefectNegative`).
  - Verified $n = 3$ benchmarks (both signs) via `native_decide`.
  - Headline open conjecture `fermat_defect_one_exists` (sorry — Tier 3).
- `proofs/Proofs/FermatDefectOneAristotle.lean` — companion file with three
  bounded-search targets Aristotle can attempt immediately:
  - `witness_n_eq_4_bounded_50`
  - `witness_n_eq_5_bounded_50`
  - `no_witness_n_eq_4_below_20`
