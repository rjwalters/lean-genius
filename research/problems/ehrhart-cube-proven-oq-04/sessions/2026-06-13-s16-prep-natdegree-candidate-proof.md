# S16 PREP — `cubeHStarPoly_natDegree` Candidate Proof (build-unverified during infra outage)

**Date**: 2026-06-13
**Researcher**: researcher-2
**Phase**: S16 PREP (doc-only; ships a complete candidate proof for the one remaining optional corollary)
**Base commit**: `fa3d62c1ef0` (origin/main HEAD at write time)
**Mathlib pin**: `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` (v4.26.0, unchanged since S11)

## 1. Why PREP and not ACT

`EhrhartCubeProvenOQ04.lean` is **VERIFIED** (PR #19101, Docker-clean,
7743 jobs): 30 theorems, 2 defs, 0 sorries, 0 axioms. The only concrete
math item left in the slug's Next-Action list is **S16**: the third
classical h\*-vector invariant for the cube,

$$ \deg h^{\ast}([0,1]^d) = d - 1 \qquad (d \ge 1), $$

i.e. `(cubeHStarPoly d).natDegree = d - 1`. The palindrome
(`cubeHStarPoly_palindromic`, S7) and the value-at-1 (`cubeHStarPoly_eval_one`
= d!, S7) are already proved; the degree completes the trio.

At this session's time the **Docker build daemon is down** (verification
infra outage, 2026-06-13). Injecting unverified Lean into a *verified*
file would silently demote its `status: verified` to build-pending with
no way to re-confirm. Per the slug's own proven **PREP → ACT** discipline
(S9/S10/S11 PREP fed the single-iteration clean S9-ACT fix, PR #19101),
this session ships the full candidate proof as a drop-in for a future
Docker-equipped ACT session, leaving the verified file untouched.

## 2. Candidate proof (drop-in for SECTION VIII, after `cubeHStarPoly_palindromic`)

```lean
/--
  **Degree of the h*-polynomial** (S16): the h*-polynomial of the unit
  d-cube has degree exactly `d - 1`,
  $$ \deg h^{\ast}([0,1]^d) = d - 1 \qquad (d \ge 1). $$
  Completes the three classical h*-vector invariants for the cube alongside
  `cubeHStarPoly_palindromic` (palindromic coefficient sequence) and
  `cubeHStarPoly_eval_one` (coefficient sum = d!). The leading coefficient
  is `A(d, d-1) = A(d, 0) = 1` (via `eulerian_palindrome` + `eulerian_zero_eq_one`),
  and all coefficients of index ≥ d vanish because the defining sum ranges
  only over `k < d`.
-/
theorem cubeHStarPoly_natDegree (d : ℕ) (hd : 0 < d) :
    (cubeHStarPoly d).natDegree = d - 1 := by
  have hd_ne : d ≠ 0 := hd.ne'
  apply le_antisymm
  · -- Upper bound: natDegree ≤ d - 1, i.e. coeff N = 0 for all N > d - 1.
    rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
    intro N hN
    unfold cubeHStarPoly
    rw [if_neg hd_ne, Polynomial.finset_sum_coeff]
    simp only [Polynomial.coeff_smul, Polynomial.coeff_X_pow, smul_eq_mul,
               mul_ite, mul_one, mul_zero]
    -- ∑ k ∈ range d, (if N = k then A(d,k) else 0) = if N ∈ range d then A(d,N) else 0
    rw [Finset.sum_ite_eq (Finset.range d) N (fun k => eulerianNumber d k)]
    -- N ≥ d (from hN : d - 1 < N, hd : 0 < d) so N ∉ range d.
    rw [if_neg (by rw [Finset.mem_range]; omega)]
  · -- Lower bound: d - 1 ≤ natDegree, i.e. the (d-1)-coefficient is nonzero.
    apply Polynomial.le_natDegree_of_ne_zero
    rw [cube_h_star_eulerian d (d - 1) hd (by omega)]
    -- A(d, d-1) = A(d, d-1-(d-1)) = A(d, 0) = 1 ≠ 0.
    rw [eulerian_palindrome d (d - 1) hd (by omega)]
    rw [show d - 1 - (d - 1) = 0 from by omega, eulerian_zero_eq_one]
    exact one_ne_zero
```

Also append to the file header's "Main theorems" block:

```
  • `cubeHStarPoly_natDegree`               — deg h*([0,1]^d) = d - 1          (S16: PROVED)
```

## 3. Proof walkthrough

`cubeHStarPoly d = ∑ k ∈ range d, A(d,k) • X^k` for `d ≥ 1` (the `if d = 0`
branch is discharged by `if_neg hd_ne`).

**Upper bound** (`natDegree ≤ d - 1`). `Polynomial.natDegree_le_iff_coeff_eq_zero`
reduces the goal to: for every `N` with `d - 1 < N`, the `N`-th coefficient
is `0`. Distribute `coeff` through the finite sum (`Polynomial.finset_sum_coeff`),
simplify each monomial coefficient (`coeff_smul` + `coeff_X_pow` collapse
`A(d,k) • (X^k).coeff N` to `if N = k then A(d,k) else 0`), then
`Finset.sum_ite_eq` collapses the indicator sum to `if N ∈ range d then A(d,N) else 0`.
Since `hN : d - 1 < N` and `hd : 0 < d` give `N ≥ d`, we have `N ∉ range d`,
so `if_neg` closes it. This is the exact tactic shape already used and
build-verified in `cube_h_star_eulerian` (SECTION V) — only the final
`if_pos`/`if_neg` branch differs — which is strong evidence the simp set
and lemma names are correct at this pin.

**Lower bound** (`d - 1 ≤ natDegree`). `Polynomial.le_natDegree_of_ne_zero`
reduces the goal to `(cubeHStarPoly d).coeff (d-1) ≠ 0`. Rewrite the
coefficient via `cube_h_star_eulerian` (valid: `d - 1 < d` for `d ≥ 1`)
to `A(d, d-1) ≠ 0`, apply `eulerian_palindrome` to get `A(d, d-1-(d-1))`,
simplify the index to `0`, and `eulerian_zero_eq_one` gives `1 ≠ 0`.

## 4. Lemma-name risk register (verify at ACT before committing)

All Mathlib lemmas below are over a commutative semiring; `Polynomial ℕ`
qualifies and is nontrivial, so `one_ne_zero` and the `le_natDegree`/
`natDegree_le_iff` API apply. The three project lemmas
(`cube_h_star_eulerian`, `eulerian_palindrome`, `eulerian_zero_eq_one`)
are already build-verified in this file.

| Lemma | Expected signature | Confidence | Fallback if name/shape differs |
|-------|--------------------|------------|--------------------------------|
| `Polynomial.natDegree_le_iff_coeff_eq_zero` | `p.natDegree ≤ n ↔ ∀ N, n < N → p.coeff N = 0` | high | `Polynomial.natDegree_le_iff_degree_le` + `Polynomial.degree_le_iff_coeff_zero`; or `Polynomial.natDegree_lt_iff_degree_lt` |
| `Polynomial.le_natDegree_of_ne_zero` | `p.coeff n ≠ 0 → n ≤ p.natDegree` | high | derive from `Polynomial.coeff_eq_zero_of_natDegree_lt` (contrapositive) |
| `Polynomial.finset_sum_coeff` | `(∑ b ∈ s, f b).coeff n = ∑ b ∈ s, (f b).coeff n` | high (used in S2) | `Polynomial.coeff_sum` / `map_sum` |
| `Polynomial.coeff_X_pow` | `(X^k).coeff n = if n = k then 1 else 0` | high (used in S2) | — |
| `Finset.sum_ite_eq` | `∑ x ∈ s, (if a = x then f x else 0) = if a ∈ s then f a else 0` | high (used in S2) | `Finset.sum_ite_eq'` (swap eq direction with `eq_comm`) |

The only genuinely new lemma vs. the already-verified S2/S7 corpus is
`Polynomial.natDegree_le_iff_coeff_eq_zero` / `Polynomial.le_natDegree_of_ne_zero`.
If either name is stale at the v4.26.0 pin, the fallbacks in the right
column reconstruct the same step.

## 5. ACT instructions (when Docker is back up)

1. Paste the §2 theorem into `proofs/Proofs/EhrhartCubeProvenOQ04.lean`
   at the end of SECTION VIII (after `cubeHStarPoly_palindromic`, before
   `end EhrhartCubeProvenOQ04`), and add the header line from §2.
2. `./proofs/scripts/docker-build.sh Proofs.EhrhartCubeProvenOQ04`
3. If clean: bump `theoremCount` 30 → 31 and `lineCount` in both
   `src/data/research/problems/ehrhart-cube-proven-oq-04.json` and
   `src/data/proofs/ehrhart-cube-proven-oq-04/meta.json` to the new
   `wc -l` value; status stays `verified`.
4. If a lemma name fails, apply the matching §4 fallback and rebuild;
   the proof *strategy* (degree-bound + nonzero-leading-coeff) is robust
   to lemma-name churn.

## 6. Scope / conflict-free guarantee

This PR is **doc-only**. It touches exactly:
- this new session memo, and
- the `state.md` head (Phase line + Current Focus pointer to S16 PREP).

No Lean source edit, no `meta.json` edit, no research-JSON edit, no
sibling-session edit. The verified file and its build status are
unchanged. There is no overlap with any other slug's tracked files.
