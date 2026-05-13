# Erdős Problem #501 — Independent Sets for Bounded Outer Measure Families

**Source**: https://erdosproblems.com/501

**Status**: OPEN — answer depends on set-theoretic axioms (CH-sensitive).

## Statement

For every `x ∈ ℝ`, let `A_x ⊂ ℝ` be a bounded set with outer measure `< 1`.
A set `X ⊆ ℝ` is **independent** if `x ∉ A_y` for all distinct `x, y ∈ X`.

Two questions:

1. Must there exist an **infinite** independent set?
2. If the `A_x` are **closed** with measure `< 1`, must size-3 independent
   sets exist?

## Known Results

| Result | Year | Statement | Lean status |
|--------|------|-----------|-------------|
| Erdős–Hajnal | 1960 | Arbitrarily large **finite** independent sets exist (for bounded outer-measure families) | `erdos_hajnal_finite` reduces to `exists_independent_tuple` (`sorry` at n≥2) |
| Gladysz | 1962 | Size-2 independent sets exist for **closed** families | `gladysz_pairs` proved from `nps_closed_infinite` via Finset extraction |
| Hechler | 1972 | Under **CH**, Q1 has answer NO (a family with no infinite independent set exists) | `hechler_under_CH` (`sorry`) |
| Newelski–Pawlikowski–Seredyński | 1987 | For **closed** `A_x`, Q1 has answer YES (infinite independent sets exist) | `nps_closed_infinite` (`sorry`) |

Combined: Q1 is **independent of ZFC** (`question1_independent_of_ZFC` —
proved as a logical corollary of the two `sorry` theorems above, currently
vacuous as both are sorried).

## Why it matters

This is one of the rare Erdős problems whose answer **depends on set-theoretic
axioms**. The Hechler / NPS dichotomy is delicate:

- Hechler uses **transfinite induction** indexed by `ω_1` under CH to build a
  pathological family avoiding all infinite independent sets.
- NPS uses **descriptive set theory** (closed sets have stronger combinatorial
  regularity) to construct infinite independent sets without CH.

Formalizing either direction would be a substantial Mathlib contribution
in axiomatic set theory.

## Lean files

- `proofs/Proofs/Erdos501Problem.lean` (278 lines) — main file: definitions
  + Erdős–Hajnal (with reduction to `exists_independent_tuple`) + Hechler/NPS
  statements (sorried) + ZFC-independence corollary.
- `proofs/Proofs/Erdos501ProblemProvable.lean` (267 lines) — duplicate of main
  file with `continuum_hypothesis` definition fixed (`Cardinal.aleph 1 =
  Cardinal.continuum` rather than trivially-provable surjection form).
- `proofs/Proofs/Erdos501Aristotle.lean` (158 lines) — Aristotle companion
  with supporting lemmas (bounded set lemmas, outer-measure monotonicity,
  size-0 / size-1 independence base cases).

## Outstanding sorries

| Theorem | File | Line | Description | Depth |
|---------|------|------|-------------|-------|
| `exists_independent_tuple` | `Erdos501Problem.lean` | 100 | Product-measure / counting argument for size-n independence (Erdős-Hajnal n≥2 case) | Moderate — needs outer-measure Tonelli/Cavalieri on `[0,L]^n` |
| `hechler_under_CH` | `Erdos501Problem.lean` | 140 | Hechler 1972 CH construction (no infinite independent family) | Deep — transfinite induction over `ω_1` |
| `nps_closed_infinite` | `Erdos501Problem.lean` | 148 | NPS 1987 closed-sets construction (infinite independent set exists) | Deep — descriptive set theory |
| (mirror) `exists_independent_tuple` | `Erdos501ProblemProvable.lean` | (mirror) | Same | Same |
| (mirror) `hechler_under_CH` | `Erdos501ProblemProvable.lean` | (mirror) | Same | Same |
| (mirror) `nps_closed_infinite` | `Erdos501ProblemProvable.lean` | (mirror) | Same | Same |
| Aristotle | `Erdos501Aristotle.lean` | varies | Supporting lemma (`exists_not_mem_of_outerMeasure_lt_Icc` or `measure_compl_Icc_pos`) | Easy — outer-measure manipulation |

## Tags

`set-theory`, `measure-theory`, `combinatorics`, `independence`, `CH-sensitive`, `descriptive-set-theory`
