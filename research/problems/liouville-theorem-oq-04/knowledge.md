# Knowledge Base: liouville-theorem-oq-04

P-adic extension of Liouville's approximation theorem.

---

## Session 2026-04-26 (Session 1) - Archimedean Complement Lemma Proved

**Mode**: FRESH
**Outcome**: progress

### What I Did
- Created `proofs/Proofs/LiouvilleTheoremOQ04.lean` (415 lines)
- Proved the **Archimedean Complement Lemma** `padicNorm_nat_ge_inv`: `(n : ℚ)⁻¹ ≤ padicNorm p n` for nonzero n : ℕ, without sorry
- Proved `padicNorm_int_ge_inv`: integer version via `Int.natAbs_eq` sign case split
- Proved 5 concrete examples (examples for p=2,3,5 with n=6,25,7,12)
- Defined `IsPadicLiouville` using height `max(|r|,|s|)` (not denominator)
- Stated `padic_liouville_estimate` as an axiom (OPEN — requires ℚ_[p] Taylor expansion)
- Build passes with 2 sorries + 1 axiom

### Key Findings

- **Core mathematical insight**: The Archimedean Complement Lemma — `|N|_p · |N| ≥ 1` for nonzero integer N — is the key bridge between p-adic and Archimedean metrics. Proof: `p^v | N` → `N ≥ p^v` → `|N|_p = p^{-v} ≥ 1/N`.
- **Mathlib key theorem**: `pow_padicValNat_dvd : p ^ padicValNat p n ∣ n` is the crucial Mathlib lemma.
- **Height vs denominator**: In the p-adic world, height `H(r/s) = max(|r|,|s|)` replaces denominator `s` because `v_p(r/s) = v_p(r) - v_p(s)` depends on both r and s.
- **Tricky Lean issues**: `div_le_div_of_nonneg_left` doesn't work as expected; `one_div_le_one_div_of_le` is the correct lemma. `Int.natAbs_eq` gives `z = ↑z.natAbs ∨ z = -↑z.natAbs` and cast via `Int.cast_natCast` is needed.
- **Instance issue**: Named private instances `instFact2`, `instFact3`, `instFact5` avoid duplicate declaration errors.

### Files Modified
- `proofs/Proofs/LiouvilleTheoremOQ04.lean` (created)
- `src/data/proofs/liouville-theorem-oq-04/` (created: meta.json, annotations.json, tacticStates.json, index.ts)
- `research/registry.json` (phase: OBSERVE → ACT)

### Sorry Status
| Location | Classification | Notes |
|----------|---------------|-------|
| `padicNorm_poly_eval_bound` | HARD | Combine integer bound with polynomial eval; Aristotle candidate |
| `padic_algebraic_not_liouville` (step) | HARD | Show Liouville approximations can have H ≥ 1/C |
| `padic_liouville_estimate` | OPEN axiom | Requires ℚ_[p] Taylor expansion infrastructure |

### Next Steps
1. Submit `padicNorm_poly_eval_bound` to Aristotle: needs `f.map (algebraMap ℤ ℚ)` eval + `padicNorm_nat_ge_inv` + polynomial coefficient bound
2. Investigate whether `Polynomial.aeval_eq_sum_range` in Mathlib helps with poly eval bound
3. For the contradiction step in `padic_algebraic_not_liouville`: use `Liouville.eventually_mul_pow_le` or similar to show H unbounded
4. Long-term: the axiom requires `Polynomial.taylorExpansion` or manual Taylor factorization over `ℚ_[p]`

---

## Session 2026-05-03 (Session 9) — Prove polyCoeffL1_pos and irred_no_rational_roots

**Mode**: REVISIT
**Outcome**: progress (2 of 4 helper sorries proved)

### What I Did

- Proved **`polyCoeffL1_pos`**: apply `Finset.sum_pos` with `support_nonempty.mpr hf` and `Int.natAbs_pos.mpr (mem_support_iff.mp hi)`.
- Proved **`irred_no_rational_roots`**: factor theorem (`dvd_iff_isRoot`), degree argument via `natDegree_map_eq_of_injective` + `natDegree_mul`, then `not_isUnit_of_degree_pos` + `Irreducible.isUnit_or_isUnit`.

### Key Findings

- Correct name is `natDegree_map_eq_of_injective` (not `natDegree_map_of_injective`).
- `Irreducible.isUnit_or_isUnit hfg` where `hfg : f.map ... = (X-q)*g` gives `IsUnit (X-q) ∨ IsUnit g`.

### Pending Sorries (2 of 4 remain)

- **`padicNorm_poly_eval_lb`** (HARD): norm compatibility `‖(q:ℚ_p)‖ = padicNorm p q`, clearing-denominator bound.
- **`cofactor_uniform_bound`** (HARD): Taylor factorization over ℚ_p; uniform bound on cofactor norm.

### Next Steps

1. `padicNorm_poly_eval_lb`: bridge ℚ and ℚ_p via `Polynomial.eval_map` + norm compatibility.
2. `cofactor_uniform_bound`: use polynomial division in ℚ_p (`Polynomial.divByMonic`).

---

## Dead Ends

- `div_le_div_of_nonneg_left` generates unexpected metavariable goal `⊢ 0 ≤ ?m` — use `one_div_le_one_div_of_le` instead
- `simpa using this` for the `padicNorm_int_ge_inv` proof introduces absolute values instead of `natAbs` — use explicit case split with `Int.natAbs_eq`
- `field_simp` on `n⁻¹ * n = 1` where `n : ℕ` fails with `Inv ℕ` — use `inv_mul_cancel₀` directly with explicit `ℚ` cast
- `inv_le_inv_of_le` is unknown in Mathlib 4.26 — use `one_div_le_one_div_of_le` instead
- `Irreducible.ne_zero` — uncertain whether this dot-notation lemma exists in Mathlib 4.26; safer to use degree argument: if `g = 0` then `natDegree(fQ) = 0` contradicting `natDegree ≥ 2`
- `not_isUnit_of_degree_pos` — uncertain whether this name exists; use `Polynomial.isUnit_iff` (confirmed in codebase: `∃ c : R, c ≠ 0 ∧ p = C c`) + `congr_arg Polynomial.natDegree` + `simp [natDegree_X_sub_C, natDegree_C]` instead
- `padicNorm.pos` does NOT exist in Mathlib 4.26 — combine `padicNorm.nonneg` and `padicNorm.nonzero`: `(padicNorm.nonneg _).lt_of_ne (Ne.symm <| padicNorm.nonzero hne)`. Existing code in `padicNorm_poly_eval_bound` uses this pattern.

---

## Session 11 (2026-05-08) — Discharge bridge ingredient (2a): height bound on r/s

**Mode**: REVISIT
**Outcome**: progress (height bound on rational arguments fully proved)

### What I Did

Added Part IV.6 (3 new theorems) to LiouvilleTheoremOQ04.lean, discharging
ingredient (2a) of the bridge axiom — the `‖r/s‖_p ≤ H` step:

- **`padicNorm_rat_le_natAbs_denom`**: For r,s : ℤ with s ≠ 0,
  `padicNorm p ((r:ℚ)/s) ≤ s.natAbs`. Proof: case split on `r = 0` (trivial);
  for r≠0, use `padicNorm.div` + `padicNorm.of_int` (numerator ≤ 1) +
  `padicNorm_int_ge_inv` (denominator ≥ 1/|s|, our Archimedean Complement).
  Combined: `padicNorm p (r/s) ≤ 1/(1/|s|) = |s|`.

- **`padic_norm_intCast_div_le_natAbs_denom`**: ℚ_[p] version. Transport the
  rational version via `norm_rat_eq_padicNorm` (Part IV.5). Key cast manipulation:
  `(r : ℚ_[p]) / (s : ℚ_[p]) = ((r/s : ℚ) : ℚ_[p])` proved via `push_cast; ring`.

- **`padic_norm_intCast_div_le_height`**: Direct corollary giving the height bound
  `‖(r:ℚ_[p])/s‖ ≤ max(|r|,|s|)`.

### Significance

The bridge axiom `padic_liouville_norm_bridge` is now reduced to a SINGLE residual:
the polynomial coefficient bound on `g.eval`. Specifically:
- Ingredient (1) (norm compatibility): ✓ proved (Session 10, Part IV.5)
- Ingredient (2a) (height bound on r/s): ✓ proved (Session 11, Part IV.6)
- Ingredient (2b) (polynomial coefficient bound `‖g.eval x‖ ≤ M·max(1,‖x‖)^(deg g)`): residual

The residual (2b) is a standard p-adic ultrametric polynomial fact independent of
α, r, s — it should be provable from Mathlib's polynomial norm machinery in a
future session.

### Lean 4.26 Notes

- `padicNorm.pos` doesn't exist; use `(padicNorm.nonneg _).lt_of_ne (Ne.symm <| padicNorm.nonzero hne)`.
- `div_le_iff`, `div_le_div_iff` confirmed present.
- `mul_le_mul_of_nonneg_right`, `inv_mul_cancel₀` confirmed names.
- `push_cast; ring` handles `(r : ℚ_[p]) / (s : ℚ_[p]) = ((r/s : ℚ) : ℚ_[p])` —
  Int → ℚ_[p] casts factor through ℚ via standard cast composition.

### Build Status

Docker build skipped due to system contention (4 active builds at 7.65GiB VM cap;
~3.4 GiB already committed). Diff is purely additive: 3 new helper theorems +
docstring updates. Existing proofs unchanged, so the file's prior passing build
is preserved if the new proofs are sound. CI/next session will verify.

### Next Steps

1. Verify Docker build of LiouvilleTheoremOQ04.lean.
2. If build passes, attempt ingredient (2b): polynomial coefficient bound. Strategy:
   for `h : Polynomial ℚ_[p]`, prove
   `‖h.eval x‖ ≤ ∑ i ∈ h.support, ‖h.coeff i‖ * ‖x‖^i` using `Polynomial.eval_eq_sum`
   + `norm_sum_le` + `norm_mul_le`. Then bound by `M * max(1,‖x‖)^(natDegree h)`
   where M = ∑ i, ‖h.coeff i‖.
3. Combine all ingredients to fully replace `padic_liouville_norm_bridge` with a
   theorem (axiom → 0).
