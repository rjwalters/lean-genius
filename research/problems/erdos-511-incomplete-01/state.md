# Current State

**Phase**: ACT (axiomatized — both axioms are deep classical theorems)
**Path**: full
**Last Updated**: 2026-05-08 (state.md sync, researcher-11)
**Status**: available
**Iteration**: 5

## Current Focus

The Lean formalization in `proofs/Proofs/Erdos511Problem.lean`
(285 lines, 4 theorems, 2 axioms, 0 sorries, 1 def) **encodes the answer**:
Erdős' #511 is DISPROVED (Pommerenke 1961).

The two remaining axioms are both deep classical theorems whose proofs
are extensive complex analysis:

1. `polya_diameter_bound` (Pólya 1928) — every connected component of
   the sublevel set `{z ∈ ℂ : |f(z)| ≤ 1}` of a monic polynomial has
   diameter `≤ 4`. (Proof: Pólya's distortion theorem for univalent
   functions, beyond the current Mathlib coverage.)

2. `pommerenke_theorem` (Pommerenke 1961) — for any `0 < d < 4` and
   `k ≥ 1`, there exist monic polynomials whose sublevel set
   `{z : |f(z)| ≤ 1}` has at least `k` connected components of
   diameter `≥ d`. Independently rediscovered by Huang (2025).

Both axioms remain because their proofs require infrastructure
(univalent function distortion theorems for `polya_diameter_bound`;
explicit polynomial constructions plus connectivity analysis for
`pommerenke_theorem`) not currently accessible in Mathlib v4.26.0.

## Iteration History

- **Iter 1** (2026-01-18, PR #354 batch): initial bootstrap with
  axiomatic statement and DISPROVED conclusion.
- **Iter 2** (2026-01-23, PR #660): substantive enrichment of the
  gallery entry with historical context, proof strategy, etc.
- **Iter 3** (2026-04-04, PR #9239): resolved 1 sorry + repaired
  pre-existing build errors. File reached 285 lines, 4 theorems,
  2 axioms, 0 sorries.
- **Iter 4** (2026-04-30, PR #13935 + #14326): metadata audits —
  removed 90 phantom axiom entries from `originalContributions`
  (batch 3, included erdos-511); fixed phantom axioms in `sections`
  + line range drift (PR #14326).
- **Iter 5** (2026-05-08, this PR, researcher-11): state.md sync to
  reflect actual state (was empty `Phase: OBSERVE` placeholder despite
  ~5 substantive merged PRs).

## Built Items

- **Theorems** (4):
  - `erdos_511`: the disproof structured as a `∀ c, ∀ bound, ∃ f, …`
    statement, derived from `pommerenke_theorem` by choosing
    `d = (c + 4) / 2`.
  - `no_component_reaches_4`: corollary of `polya_diameter_bound`,
    showing the bound `4` is the absolute upper limit.
  - `erdos_511_summary`: combines both axioms into a single
    statement of the complete picture.
  - `erdos_511_answer`: NO bounding function exists — explicit
    refutation of the original conjecture.

- **Definitions** (1):
  - `rootsOfUnityPoly (n : ℕ) := Polynomial.X ^ n - 1` — the
    canonical example `z^n − 1`. The Erdős–Herzog–Piranian bound
    `Σ_C diam(C) ≤ n · 2^(1/n)` is essentially tight on this example.
    (No theorems about `rootsOfUnityPoly` are proved yet.)

- **Axioms** (2): both deep classical theorems, see Current Focus.

## Active Approach

The DISPROVED status is fully encoded; eliminating either axiom
would require substantial Mathlib infrastructure additions. The
practical incremental path is:

1. **Theorems about `rootsOfUnityPoly`** — the file declares
   `def rootsOfUnityPoly (n : ℕ) := Polynomial.X ^ n - 1` but proves
   nothing about it. Adding `rootsOfUnityPoly_monic`,
   `rootsOfUnityPoly_natDegree`, `rootsOfUnityPoly_eval_root_of_unity`,
   etc. would flesh out the canonical-example side without touching
   the deep axioms. Each is ~5 lines via `Polynomial.monic_X_pow_sub_C`,
   `Polynomial.natDegree_X_pow_sub_C`, etc.
2. **Connectivity / petal-structure lemmas** for `z^n − 1`, currently
   only described in block comments (Parts IV–V). Would require
   importing `Mathlib.Analysis.NormedSpace.Basic` for the petal
   geometry; nontrivial Mathlib work.

Path 1 is the highest-leverage near-term iteration.

## Blockers

- **Pólya 1928 distortion theorem**: Mathlib v4.26.0 lacks the
  univalent-function distortion machinery needed to prove
  `polya_diameter_bound`. Substantial Mathlib contribution.
- **Pommerenke 1961 / Huang 2025 explicit construction**: requires
  explicit polynomial perturbation analysis on `z^n − 1` (Parts IV–VII
  of the Lean file, currently in block-comment form).

## Next Action

**Iter 6 candidate**: prove `rootsOfUnityPoly_monic`,
`rootsOfUnityPoly_natDegree`, and `rootsOfUnityPoly_X_eval_one_eq_zero`.

Statement (rough):
```lean
theorem rootsOfUnityPoly_monic {n : ℕ} (hn : 1 ≤ n) :
    (rootsOfUnityPoly n).Monic
theorem rootsOfUnityPoly_natDegree {n : ℕ} (hn : 1 ≤ n) :
    (rootsOfUnityPoly n).natDegree = n
theorem rootsOfUnityPoly_eval_one : (rootsOfUnityPoly n).eval 1 = 0  -- since 1^n - 1 = 0
```

Each ~3–5 lines via `Polynomial.monic_X_pow_sub_C`,
`Polynomial.natDegree_X_pow_sub_C`, and direct `eval` evaluation.

Beyond Iter 6, the path forks: (a) keep adding `rootsOfUnityPoly`
properties toward proving `rootsOfUnityPoly` is the canonical
extremal example for the Erdős–Herzog–Piranian bound; (b) wait
for Mathlib's univalent-function machinery to mature before
attempting `polya_diameter_bound` axiom elimination.

## Attempt Counts

- Total attempts: 5
- Current approach attempts: 1 (state.md sync, this PR)
- Approaches tried: bootstrap + DISPROVED encoding (Iter 1–3);
  metadata fixes (Iter 4); state.md sync (Iter 5).

## References

- `proofs/Proofs/Erdos511Problem.lean` — main file (285 lines, 4
  theorems, 2 axioms, 0 sorries, 1 def).
- `src/data/proofs/erdos-511/meta.json` — gallery integration.
- Pommerenke, "On metric properties of complex polynomials",
  *Michigan Math. J.* 8 (1961).
- Pólya, "Beitrag zur Verallgemeinerung des Verzerrungssatzes auf
  konforme Abbildungen mehrfach zusammenhängender Gebiete",
  *Sitzungsber. Preuss. Akad. Wiss. Berlin Phys.-Math. Kl.* (1928).
- Hayman, *Research problems in function theory*, problem 4.9 (1974).
- Huang, "Many lemniscates with large diameter" (2025).
