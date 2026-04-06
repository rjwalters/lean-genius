# Knowledge Base: minkowski-theorem-oq-02-oq-01

Eliminate 3 measure-theoretic axioms from MinkowskiTheoremOQ02.lean:
- `dirichletSet_convex`
- `dirichletSet_measurable`
- `dirichletSet_volume`

**Status: COMPLETED** — 0 axioms, 0 sorries. File: `proofs/Proofs/MinkowskiTheoremOQ02OQ01.lean`

---

## Session 2026-04-05 (Session 1) — Axiom Elimination Complete

**Mode**: FRESH
**Outcome**: completed

### What I Did

1. Proved `dirichletSet_measurable`: set is open (preimage of `Ioo × Ioo` under continuous maps) → `IsOpen.measurableSet`
2. Proved `dirichletSet_convex`: intersection of two halfspaces, each preimage of `Ioo` under a linear functional → `Convex.linear_preimage`
3. Proved `dirichletSet_volume`: shear map `T(x,y)=(x,αx−y)` has matrix `!![1,0;α,-1]` with `det=-1`, `|det|=1` → measure-preserving; image is axis-aligned rectangle with area `4(Q+1)/Q`
4. Resolved 6 Lean 4 build errors across two sessions

### Key Technical Insights

- `zsmul_eq_mul` fires on `c • f : Fin 2 → ℝ` before `Pi.smul_apply` can distribute — split into separate simp calls
- `ENNReal.ofReal_lt_ofReal_iff` requires `0 < q` (strict), use `positivity` not `norm_num`
- `exact_mod_cast` handles `|(c : ℝ)| = (|c| : ℝ)` (Int.cast_abs direction) cleanly
- `fin_cases` produces `⟨0, _⟩` form; `show x_val 0 = 0` normalizes before `rw`
- `map_matrix_volume_pi_eq_smul_volume_pi` is the key Mathlib lemma for volume under matrix maps

### Files Created

- `proofs/Proofs/MinkowskiTheoremOQ02OQ01.lean` — 267 lines, 0 axioms, 0 sorries
- `src/data/research/problems/minkowski-theorem-oq-02-oq-01.json`

### Next Steps

- Simultaneous Dirichlet approximation in ℝⁿ
- Hurwitz theorem: `|α-p/q| < 1/(√5·q²)` for infinitely many p/q
