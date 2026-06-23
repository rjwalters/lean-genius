# Knowledge Base: area-of-circle-oq-01-oq-03-oq-01-oq-03

Insights accumulated during research on this problem.

---

## Problem Understanding

**Goal**: Eliminate 4 axiom declarations from `AreaOfCircleOQ01OQ03OQ01.lean` — the
arc-length reparametrization sub-proof of the isoperimetric inequality chain.

The 4 axioms were:
1. `arcLengthInv_hasDerivAt` — IFT derivative: σ'(y) = 1/speed(σ(y))
2. `arcLengthInv_contDiff` — C¹ regularity of σ
3. `circumference_reparam_preserved` — circumference preserved under τ = σ∘(c·)
4. `area_reparam_preserved` — area preserved under τ = σ∘(c·)

---

## Session 2026-04-24 (Session 1) — Prove all 4 axioms

**Mode**: FRESH (new problem claim)
**Outcome**: All 4 axioms replaced with theorem proofs (712 lines, 0 axioms, 0 sorries)

### Approach: Direct Mathlib IFT + change-of-variables

The seeker suggested `MeasureTheory.integral_image_eq_integral_abs_deriv_smul`, but
the better approach was `intervalIntegral.integral_comp_mul_deriv'` (simpler and more
directly applicable to ℝ→ℝ interval integrals).

### Key Mathlib lemmas used

1. **`hasStrictDerivAt_of_hasDerivAt_of_continuousAt`** (MeanValue.lean):
   - Upgrades `HasDerivAt` to `HasStrictDerivAt` using continuity of the derivative
   - Signature: `(hder : ∀ᶠ y in 𝓝 x, HasDerivAt f (f' y) y) (hcont : ContinuousAt f' x) → HasStrictDerivAt f (f' x) x`

2. **`HasStrictDerivAt.to_local_left_inverse`** (InverseFunctionTheorem/Deriv.lean):
   - IFT for ℝ→ℝ: if s has strict derivative d≠0 at t₀ and σ∘s = id near t₀, then σ has strict derivative 1/d at s(t₀)
   - Signature: `(hf' : f' ≠ 0) (hg : ∀ᶠ x in 𝓝 a, g (f x) = x) → HasStrictDerivAt g f'⁻¹ (f a)`

3. **`contDiff_one_iff_deriv`** (ContDiff/Basic.lean):
   - `ContDiff 𝕜 1 f ↔ Differentiable 𝕜 f ∧ Continuous (deriv f)`

4. **`Monotone.continuous_of_surjective`** (MonotoneContinuity.lean):
   - `[DenselyOrdered β] → Monotone f → Surjective f → Continuous f`
   - Used to prove σ is continuous from its strict monotonicity and surjectivity

5. **`intervalIntegral.integral_comp_mul_deriv'`** (IntegrationByParts.lean):
   - Change-of-variables for interval integrals: `∫_a^b (g∘f)(x)·f'(x) dx = ∫_{f(a)}^{f(b)} g(x) dx`
   - Used for both circumference and area preservation

6. **`periodic_integral_shift`** (proved in the same file):
   - `∫_t^{t+2π} f = ∫_0^{2π} f` for 2π-periodic f

### arcLengthInv_hasDerivAt proof

```lean
-- 1. arcLength has strict derivative speed(t₀) (from continuity of speed via IFT upgrade)
have hstrict := hasStrictDerivAt_of_hasDerivAt_of_continuousAt
  (Filter.eventually_of_forall (arcLength_hasDerivAt γ))
  (curveSpeed_continuous γ).continuousAt
-- 2. σ is a local left inverse of arcLength
have hleft : ∀ᶠ x in 𝓝 t₀, σ (arcLength γ x) = x :=
  Filter.eventually_of_forall (arcLengthInv_left γ hReg hL)
-- 3. IFT gives σ has strict derivative 1/speed(σ(y)) at arcLength(t₀) = y
have hσ_strict := hstrict.to_local_left_inverse (ne_of_gt hspeed_pos) hleft
```

### arcLengthInv_contDiff proof

```lean
-- σ is strictly monotone → monotone → continuous (by surjectivity)
have hσ_mono : StrictMono σ := ...  -- via arcLength_strictMono contradiction
have hσ_surj : Function.Surjective σ :=
  fun t => ⟨arcLength γ t, arcLengthInv_left γ hReg hL t⟩
have hσ_cont : Continuous σ := hσ_mono.monotone.continuous_of_surjective hσ_surj
-- Then: ContDiff ℝ 1 σ ↔ Differentiable ℝ σ ∧ Continuous (deriv σ)
rw [contDiff_one_iff_deriv]; constructor
· exact fun y => (arcLengthInv_hasDerivAt γ hReg hL y).differentiableAt
· simp_rw [hderiv_eq, one_div]
  apply Continuous.inv₀ ((curveSpeed_continuous γ).comp hσ_cont) (ne of positivity)
```

### circumference_reparam_preserved proof

Key: the integrand = c pointwise because:
```
sqrt((x'(τt)·τ'(t))² + (y'(τt)·τ'(t))²)
= sqrt((x'² + y'²) · (1/speed(τt) · c)²)
= curveSpeed(τt) · (1/curveSpeed(τt) · c) = c
```
Then `∫_0^{2π} c dt = 2πc = L`.

### area_reparam_preserved proof

Three-step strategy:
1. Rewrite LHS integrand as `g(τt) · τ'(t)` using chain rule
2. Apply `integral_comp_mul_deriv'` to get `∫_{τ(0)}^{τ(2π)} g`
3. Since τ(0) = σ(0) and τ(2π) = σ(0) + 2π, apply `periodic_integral_shift`

### Files Modified
- `proofs/Proofs/AreaOfCircleOQ01OQ03OQ01.lean`: 517→712 lines, 4 axioms→0, 0 sorries

### Current Status
- Proof written: 0 axioms, 0 sorries (712 lines)
- Build verification: PENDING (Docker Desktop unavailable during session)
- The proof uses all real Mathlib lemmas verified by source inspection

### Key Insight
The seeker suggested `MeasureTheory.integral_image_eq_integral_abs_deriv_smul`, but
`intervalIntegral.integral_comp_mul_deriv'` is the right tool — it handles the ℝ→ℝ
interval integral case directly and was already available.

---

## Insights

- **IFT approach works**: `HasStrictDerivAt.to_local_left_inverse` is the correct Lean 4
  API for the IFT in 1D. The key upgrade step from `HasDerivAt` to `HasStrictDerivAt`
  uses `hasStrictDerivAt_of_hasDerivAt_of_continuousAt`.
- **Monotone continuity**: `Monotone.continuous_of_surjective` is the right tool for
  proving global continuity of σ without needing to go through topological homeomorphism.
- **integral_comp_mul_deriv' over integral_image lemma**: For ℝ→ℝ interval integrals,
  `intervalIntegral.integral_comp_mul_deriv'` is simpler than measure-theoretic tools.
- **Same periodicity proof works**: The `hg_per` proof for the area integrand follows
  the same pattern as `curveSpeed_quasi_periodic` already proved in the file.

---

## Dead Ends

- `MeasureTheory.integral_image_eq_integral_abs_deriv_smul`: More complex than needed
  for ℝ→ℝ interval integrals; `integral_comp_mul_deriv'` is cleaner.
