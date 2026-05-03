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
