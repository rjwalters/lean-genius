# Knowledge: brouwer-fixed-point-oq-04-oq-02

## Key Facts

### Nash Equilibrium Setup
- n-player game: each player i has finite strategy set Sᵢ
- Mixed strategy: probability distribution σᵢ ∈ Δ(Sᵢ) (probability simplex)
- Expected payoff: Uᵢ(σ) = Σ_{s ∈ ∏ Sⱼ} σ₁(s₁)·...·σₙ(sₙ)·uᵢ(s)
- Nash equilibrium: σ* s.t. Uᵢ(σᵢ*, σ₋ᵢ*) ≥ Uᵢ(τᵢ, σ₋ᵢ*) for all i, τᵢ

### Key Insight: Nash's Original Proof Uses Brouwer, Not Kakutani
- Nash (1950) defined a **single-valued** continuous deviation map, avoiding UHC entirely
- `excess_i(k, σ) = max(0, EU_i(eₖ, σ) − EU_i(σᵢ, σ))`: improvement from deviating to eₖ
- `φᵢ(k, σ) = (σᵢ(k) + excess_i(k, σ)) / (1 + Σₗ excess_i(l, σ))`: normalized deviation map
- φ maps ProductSimplex → ProductSimplex, continuous ⟹ Brouwer applies
- Fixed point algebra: at σ*, `excess_ik = σᵢk * Ci` where `Ci = Σ excess_il ≥ 0`
- If Ci > 0: all positive-weight pure strategies have positive excess, so EU_i(σ*) > EU_i(σ*). Contradiction.
- Hence Ci = 0, all excesses zero, σ* is Nash equilibrium ✓

### Why This Beats OQ01's Approach
- OQ01 needs 2 axioms: `bestResponse_uhc` (Berge) + `kakutani_product_simplex`
- OQ02 needs 1 axiom + 1 sorry: `brouwer_product_simplex` + `mixedUtility_linear_in_i`
- Key: Berge's maximum theorem (UHC of argmax) avoided by switching to Nash's map
- Continuous single-valued map avoids all UHC machinery

### Remaining Open Issues
1. `brouwer_product_simplex` (axiom): Brouwer FPT on ∏ᵢ Δᵢ
   - Follows from `kakutani_fixed_point_axiom` + `Fin.append` embedding
   - ∏ᵢ (Fin(G.strategies i) → ℝ) ≅ Fin(Σᵢ G.strategies i) → ℝ via concatenation
   - This embedding is routine topology (homeomorphism of finite-dim vector spaces)

## References
- Nash, J.F. (1950): "Equilibrium Points in n-Person Games" — original Brouwer-based proof
- Nash, J.F. (1951): "Non-Cooperative Games" — Kakutani-based proof (longer)
- Kakutani, S. (1941): "A Generalization of Brouwer's Fixed Point Theorem"
- Parent proof: `proofs/Proofs/BrouwerFixedPointOQ04.lean`
- OQ01 file: `proofs/Proofs/BrouwerFixedPointOQ04OQ01.lean` (Nash from Kakutani, 2 axioms)

---

## Session 2026-04-21 (Session 1) — Nash's Brouwer Proof Formalized

**Mode**: FRESH
**Outcome**: PROGRESS — Nash existence proved with 1 sorry + 1 axiom (vs OQ01's 2 axioms)

### What I Did

1. Read `BrouwerFixedPointOQ04.lean` (structure, Kakutani axiom, FiniteGame, MixedStrategy)
2. Read `BrouwerFixedPointOQ04OQ01.lean` (Nash from Kakutani; 2 axioms: bestResponse_uhc + kakutani_product_simplex)
3. Assessed `bestResponse_uhc` as provable from joint continuity + compactness gap argument, but requiring Berge's theorem machinery (not in Mathlib)
4. Chose Nash's original Brouwer argument instead (from 1950 paper), which avoids UHC entirely
5. Created `proofs/Proofs/BrouwerFixedPointOQ04OQ02.lean` (~280 lines)
6. Created gallery data: `src/data/proofs/brouwer-fixed-point-oq-04-oq-02/`

### Key Proofs

- `MultilinearGame` structure: explicit payoff per pure strategy profile
- `mixedUtility_continuous`: joint continuity proved via `continuous_finset_sum` + `continuous_finset_prod`
- `nashMap_maps_simplex`: each component is a valid probability distribution (sum=1, nonneg)
- `nashMap_continuous`: division by continuous positive denominator is continuous
- `fixed_point_is_nash`: algebraic argument from fixed-point equation; `Finset.sum_lt_sum` for contradiction

### Files Modified

- `proofs/Proofs/BrouwerFixedPointOQ04OQ02.lean` (new, ~280 lines)
- `src/data/proofs/brouwer-fixed-point-oq-04-oq-02/meta.json` (new)
- `src/data/proofs/brouwer-fixed-point-oq-04-oq-02/index.ts` (new)
- `src/data/proofs/brouwer-fixed-point-oq-04-oq-02/annotations.json` (new)
- `research/problems/brouwer-fixed-point-oq-04-oq-02/knowledge.md` (this file)
- `src/data/research/problems/brouwer-fixed-point-oq-04-oq-02.json` (updated)

### Next Steps

1. Derive `brouwer_product_simplex` from `kakutani_fixed_point_axiom` via `Fin.append`
2. If proved: file has 0 sorries + 0 axioms beyond Kakutani (inherited)

---

## Session 2026-04-22 (Session 2) — mixedUtility_linear_in_i Proved

**Mode**: REVISIT
**Outcome**: completed — 0 sorries, 1 axiom (brouwer_product_simplex)

### What I Did

1. Fixed 5 compilation errors from Session 1:
   - `mixedUtility_continuous_in_i`: `subst hij` was eliminating `i` (outer param); fixed with `rw [hij]` + `congr_fun (Function.update_self i τ σ) (s i)` via `simp_rw [key]`
   - `hprod_upd.hi`: `show pureStrat...` failed (Function.update semireducible); fixed with `.trans` using `Function.update_self`
   - `hprod_upd.hne`: `Function.update_of_ne` couldn't infer implicit `f`; fixed with `(f := σ)` annotation
   - `mixedUtility_linear_in_i` (sum_comm): needed `simp_rw [Finset.mul_sum]` to push `σ i k *` inside the inner sum before `rw [Finset.sum_comm]`
   - `nashExcess_continuous`: same `subst h` issue; fixed same way as continuous_in_i
2. Fixed `hind` proof (indicator sum): `simp_rw [mul_ite, ...]` silently failed; replaced with `trans ∑ k, if s i = k then σ i k else 0 / congr 1; ext k; split_ifs <;> ring / simp [Finset.sum_ite_eq']`

### Key Technical Findings

- **`Function.update` is `@[semireducible]`**: `show` tactic fails to unfold it; must use `Function.update_self` term proof with `congr_fun`
- **`subst h : j = i`** when both `j` and `i` are free variables: Lean 4 may eliminate `i` (outer param) instead of `j` (intro'd var); safer to use `rw [h]`
- **`Function.update_of_ne` implicit `f`**: when `hj : j ≠ i` and value are given, `f = σ` may not be inferred; use `(f := σ)` named argument
- **Double sum pattern for `Finset.sum_comm`**: requires `∑ a ∈ s, ∑ b ∈ t, f a b`; must first use `simp_rw [Finset.mul_sum]` to pull scalar inside before swapping

### Files Modified

- `proofs/Proofs/BrouwerFixedPointOQ04OQ02.lean` (multiple fixes, ~490 lines, 0 sorries, 1 axiom)
- `research/problems/brouwer-fixed-point-oq-04-oq-02/knowledge.md` (this file)

### Next Steps

Remaining axiom `brouwer_product_simplex` — could attempt via `Fin.appendEquiv` homeomorphism + `kakutani_fixed_point_axiom` singleton correspondence. Low priority since 1-axiom Nash existence is already a strong result.
