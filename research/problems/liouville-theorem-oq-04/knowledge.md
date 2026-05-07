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

---

## Session 2026-05-08 (Session 11) — Cofactor Bound + Height Bound (researcher-6)

**Mode**: REVISIT
**Outcome**: progress (ingredient (2) of bridge axiom now formally proved at the helper level)

### What I Did

Added two new sections to `LiouvilleTheoremOQ04.lean`:

**Part IV.7** — P-adic height bound on rationals:
- `padicNorm_rat_int_div_le_natAbs (r s : ℤ) (hs : s ≠ 0) : padicNorm p ((r:ℚ)/s) ≤ |s|`
  Proof: `padicNorm.div` (multiplicativity) + `padicNorm.of_int` (≤ 1) +
  `padicNorm_int_ge_inv` (Archimedean Complement) + `div_le_iff₀` + `mul_inv_cancel₀`.
- `padicNorm_rat_int_div_le_height`: corollary with `max(|r|,|s|)`.
- `padic_norm_intCast_eq_padicNorm (z : ℤ) : ‖((z:ℤ):ℚ_[p])‖ = padicNorm p (z:ℚ)` —
  bridges integer-cast form to rational-cast form via `norm_cast`.
- `padic_norm_int_div_le_height (r s : ℤ) (hs : s ≠ 0) : ‖((r:ℚ_[p])/s)‖ ≤ max(|r|,|s|)`.

**Part IV.8** — Polynomial cofactor evaluation bound:
- `coeffNormSum (g : Polynomial ℚ_[p]) : ℝ := g.support.sum fun i => ‖g.coeff i‖`
- `coeffNormSum_nonneg`: nonneg of the cofactor magnitude.
- `padic_polynomial_eval_norm_bound (g : Polynomial ℚ_[p]) (x : ℚ_[p]) (H : ℝ)
    (hH : 1 ≤ H) (hxH : ‖x‖ ≤ H) : ‖g.eval x‖ ≤ coeffNormSum p g · H^(natDegree g)`.
  Proof: rewrite via `Polynomial.eval_eq_sum`, then `norm_sum_le` + `norm_mul` +
  `norm_pow` + `pow_le_pow_left₀` + `pow_le_pow_right₀` + factor out `H^natDegree`.
- `padic_cofactor_bound_rat`: rational-point specialization with `H = max(|r|,|s|)`.

Updated bridge axiom docstring + Sorry Summary to reflect new state. File builds
cleanly (Docker, lean 4.26.0): 1 axiom, 0 sorries, 732 lines, 26 theorems, 4 defs.

### Key Findings

- **Cast-rewrite isDefEq blowup**: The natural pattern `have hcast : ((r:ℚ_[p])/s) = (((r:ℚ)/s):ℚ_[p]) := by push_cast; rfl; rw [hcast, norm_rat_eq_padicNorm]` triggers a deterministic timeout at `isDefEq` (heartbeats=400000). The rewrite engine can't reconcile the cast layers inside `‖·‖` quickly enough.
- **Robust pattern**: rewrite `norm_div` first (breaks the norm into integer norms), then use a separate `padic_norm_intCast_eq_padicNorm` helper on each integer norm. The integer-cast bridge uses `norm_cast` (not `push_cast; rfl`) which is more efficient for one-step cast equalities.
- **Bridge ingredient (2) anatomy**: the cofactor bound packages naturally as `‖g.eval x‖ ≤ M · max(1, ‖x‖)^(natDegree g)`, where `M = ∑ i ∈ support, ‖g.coeff i‖` is the L¹ coefficient norm. This is a direct application of triangle + multiplicativity to `g.eval x = ∑ g.coeff i · x^i`.
- **Residual obstruction is purely algebraic**: with all three sub-ingredients formally proved, discharging the bridge axiom reduces to handling the case `f(r/s) = 0 ∧ r/s ≠ α`. Since this set is the rational roots of `f` minus α (finite, ≤ deg f elements), one can take `C ≤ min ‖α - r₀‖` over the set.

### Pending — Bridge Discharge Sketch

```
theorem padic_liouville_norm_bridge_proof (...) :
    ∃ C : ℝ, 0 < C ∧ ∀ r s : ℤ, s ≠ 0 → α ≠ (r:ℚ_[p])/s →
      C / H^(2d) ≤ ‖α - (r:ℚ_[p])/s‖ := by
  -- Get C₁ from the algebraic case f(r/s) ≠ 0
  obtain ⟨C₁, hC₁_pos, hC₁⟩ := /- combine padicNorm_poly_eval_bound + padic_norm_int_poly_eval + padic_cofactor_bound_rat -/
  -- Get δ = min over rational roots of f distinct from α
  let RatRoots : Finset ℚ := /- rational roots of f.map (algebraMap ℤ ℚ) -/
  let RatRootsExceptAlpha := RatRoots.filter (fun q => (q : ℚ_[p]) ≠ α)
  by_cases hempty : RatRootsExceptAlpha.Nonempty
  case pos =>
    let δ := RatRootsExceptAlpha.inf' hempty (fun q => ‖α - (q : ℚ_[p])‖)
    use min C₁ δ
    -- C₁ handles f(r/s) ≠ 0 case; δ handles the finite rational-root case
    ...
  case neg => use C₁; ...
```

### Next Steps

1. Identify the right Mathlib name for "finite set of rational roots of an integer polynomial". Candidates: `Polynomial.roots`, `Polynomial.aroots`. Need a ℚ-version with finiteness from degree.
2. Prove the bridge using the case-split sketched above.
3. After bridge discharge: convert `axiom padic_liouville_norm_bridge` to `theorem ... := by <proof>`, drop the `axiomCount: 1` to 0, change `status: "axiomatized"` to `"verified"`, change `badge: "axiom"` to `"verified"` (or `"original"` since this is a from-scratch p-adic Liouville).
