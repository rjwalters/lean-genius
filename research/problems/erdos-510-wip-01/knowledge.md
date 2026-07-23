# Knowledge Base: erdos-510-wip-01

## Session 2026-07-22b (researcher-1) — Chowla's √N bound PROVED for sum-free sets

Added 4 axiom-free theorems to `Erdos510WIP01.lean` (host-verified v4.31, `lake env lean` exit 0;
`#print axioms` = [propext, Classical.choice, Quot.sound]; no sorry/native_decide):
- `integral_cos_mul_cos_mul_cos_eq_zero`: ∫₀^{2π} cos(aθ)cos(bθ)cos(cθ) = 0 when none of
  a+b=c, a+c=b, b+c=a holds. Product-to-sum twice → four cosines at signed ℤ-frequencies
  a+b+c, a+b−c, a−b+c, a−b−c, all nonzero (first =0 only if a=b=c=0, violating a+b≠c —
  so NO positivity hypotheses needed). Reuses `integral_cos_int_mul_eq_zero`; the trig
  identity is `simp only [cos_add, cos_sub, sin_add, sin_sub]; ring` after `push_cast`.
- `integral_cosineSum_cube_eq_zero`: **the third moment vanishes on sum-free sets**
  (∀ a b ∈ A, a+b ∉ A). Cube → triple sum via `sum_mul_sum`/`sum_mul`/`mul_sum`; three
  nested `integral_finsetSum` swaps; sum-freeness kills every triple. (General identity
  ∫f³ = (3π/2)·#{(a,b): a+b∈A} noted but not needed.)
- `minCosineSum_le_neg_sqrt_half_card`: **minCosineSum A ≤ −√(N/2) for nonempty sum-free A**
  — the conjectured √N growth rate of Erdős #510 with explicit constant 1/√2, on the
  sum-free subclass. Mechanism (MATERIALLY NEW vs. second-moment and vs. the blocked
  elementary-trig route): three-moment Cauchy–Schwarz bootstrap. u := f−m ≥ 0; the *scaled*
  optimal integrand u·((−2m)u − (N+2m²))² ≥ 0 integrates via (∫f, ∫f², ∫f³) = (0, πN, 0)
  to EXACTLY 2πmN(N−2m²); m<0<N forces N ≤ 2m². Scaling the linear factor by −2m clears
  all denominators — closed form is a pure `ring` identity, final step one `nlinarith`
  with hint `m*(π*N) < 0`.
- `exists_angle_cosineSum_lt_neg_half_sqrt`: existential conjecture-shaped form —
  ∃ θ, cosineSum A θ < −(1/2)√N (strict; 1/2 < 1/√2 absorbed via √(N/4) < √(N/2)).

Notes: sum-freeness ⇒ 0 ∉ A for free (0∈A would need 0+0∉A). All-odd sets are sum-free —
consistent with their exact minimum −N. Sum-free hypothesis taken raw
(∀ a ∈ A, ∀ b ∈ A, a + b ∉ A), no extra imports.

### Remaining open
- The general −c√N bound for sets WITH additive structure (third moment large positive) —
  that is exactly the hard case (Bedert N^{1/7} frontier). Deep imported; still the mission.
- Sidon B−B example for √N-optimality (tied to the deep route).


## Session 2026-07-22 (researcher-1) — dilation invariance (reduction to primitive sets)

Added 2 axiom-free theorems to `Erdos510WIP01.lean` (host-verified v4.31, `lake env lean` exit 0;
`#print axioms` = [propext, Classical.choice, Quot.sound]; no sorry/native_decide):
- `cosineSum_dilate (d ≠ 0) : cosineSum (A.image (d*·)) θ = cosineSum A (d*θ)` — dilating every
  frequency by `d` merely rescales the angle. Proof: `Finset.sum_image` (injectivity of `n↦d*n`
  for `d≠0` via `Nat.eq_of_mul_eq_mul_left`) + `(d*n)*θ = n*(d*θ)`.
- `minCosineSum_dilate (d ≠ 0) : minCosineSum (A.image (d*·)) = minCosineSum A` — **the Chowla
  cosine minimum is dilation-invariant**. `Set.range (cosineSum (d·A)) = Set.range (cosineSum A)`
  since `θ↦d·θ` surjects `ℝ` onto itself (`d≠0`); the two infima (`sInf ∘ range`, by defeq of
  `iInf`) coincide. This is the standard reduction letting one assume `gcd A = 1` (a *primitive*
  set): every set has the same minimum as its primitive core `A/gcd A`.

Idiom: `minCosineSum X = sInf (Set.range (cosineSum X))` holds by `rfl`/`show` (`iInf f :=
sInf (range f)`), so range equality transports directly to `sInf` equality — no `ciInf` reindex
lemma needed (ℝ is only conditionally complete, so `Function.Surjective.iInf_comp` does NOT apply).

### Remaining open (unchanged)
- Sharp `−c√N` bound (Bourgain/Ruzsa/Bedert) — deep imported, the genuine open mission. The
  elementary sign structure + attainment + all-odd sharp extreme + dilation invariance are done.

# Knowledge Base: erdos-510-wip-01

## Session 2026-07-21 (researcher-1) — θ=π alternating bound + sharp all-odd minimum

Added 2 axiom-free theorems to `Erdos510WIP01.lean` (host-verified v4.31 fresh-parent-olean;
`#print axioms` = propext/Classical.choice/Quot.sound):
- `minCosineSum_le_alternating (A) : minCosineSum A ≤ ∑_{n∈A} (−1)ⁿ` — evaluate at θ=π
  (`cosineSum_pi` already on file) + `minCosineSum_le`. Computable upper bound on the Chowla
  minimum for any A (= #even − #odd), negative when A is odd-heavy.
- `minCosineSum_forall_odd (A) (∀ n∈A, Odd n) : minCosineSum A = −A.card` — **sharp**. For
  all-odd A each cos(nπ)=−1 so cosineSum A π = −N, meeting the global lower bound
  `neg_card_le_minCosineSum`; `le_antisymm`. An explicit infinite family attaining the extreme
  −N (≪ the conjectured −c√N, but exact), generalizing `minCosineSum {n} = −1`.

Idiom: `(hodd n hn).neg_one_pow : (-1:ℝ)^n = -1`; then `Finset.sum_congr rfl · , sum_const,
nsmul_eq_mul, mul_neg_one`.

### Remaining open (unchanged)
- Sharp `−c√N` bound (Bourgain/Ruzsa/Bedert) — deep imported, the genuine open mission.
  Elementary sign structure + attainment (incl. the sharp all-odd extreme) is now complete.


## Session 2026-07-20 (researcher-1) — strict minCosineSum < 0 for nonempty positive-frequency sets

**Mode**: build on the nonpositivity result. **Outcome**: progress — 2 axiom-free theorems,
host-verified v4.31 (`lake env lean` exit 0; `#print axioms` = `[propext, Classical.choice,
Quot.sound]`; no sorry/native_decide).

`minCosineSum_neg : 0 ∉ A → A.Nonempty → minCosineSum A < 0`. Strengthens `minCosineSum_nonpos`.
Argument (by contradiction on `minCosineSum A = 0`): then `cosineSum A ≥ 0` pointwise, but
`cosineSum A 0 = A.card ≥ 1 > 0`, so `{θ | 0 < cosineSum A θ}` is open (`isOpen_lt`) and contains
`0`, hence contains a ball `(−ε, ε)`. On `[δ/2, δ]` (`δ = min ε π ⊂ (0,2π)`) the integrand is
strictly positive, so `∫_{δ/2}^{δ} cosineSum > 0` (`intervalIntegral.intervalIntegral_pos_of_pos_on`
— NOTE: lives in `namespace intervalIntegral`, so double-qualified). Splitting
`∫₀^{2π} = ∫₀^{δ/2} + ∫_{δ/2}^{δ} + ∫_δ^{2π}` via `integral_add_adjacent_intervals`, the outer
pieces are `≥ 0` (`integral_nonneg`) and the middle `> 0`, so the period integral is `> 0` —
contradicting `integral_cosineSum_eq_zero = 0`.

`exists_angle_cosineSum_neg : 0 ∉ A → A.Nonempty → ∃ θ, cosineSum A θ < 0`. Immediate from
`minCosineSum_neg` + `exists_eq_minCosineSum` (minimizing angle realises a negative value).

**Key idiom**: `intervalIntegral_pos_of_pos_on` needs strict positivity on the WHOLE open
interior, so it can't hit the full period (cosineSum isn't positive everywhere) — instead
carve a small subinterval where it IS positive (via continuity + `isOpen_lt` ball) and split
the period integral; outer nonneg + middle strict-pos.

### Next
- Sharp `−c√N` bound (Chowla; Bourgain/Ruzsa/Bedert) stays a deep imported result — the
  elementary sign structure (≤0, strict <0, attainment) is now COMPLETE. Remaining elementary
  targets are thin: perhaps `cosineSum A π = ∑ (−1)^n` sharpness, or lower bounds for specific
  structured A (e.g. arithmetic progressions). The genuine open mission is quantitative only.

## Session 2026-07-20 (researcher-1) — minCosineSum ≤ 0 for positive-frequency sets

**Mode**: build on the attainment result. **Outcome**: progress — 3 axiom-free theorems,
host-verified v4.31 (`lake env lean` exit 0; `#print axioms` = `[propext, Classical.choice,
Quot.sound]`; no sorry/native_decide).

`minCosineSum_nonpos : 0 ∉ A → minCosineSum A ≤ 0`. Each positive-frequency term integrates
to zero over a full period (`integral_cos_mul_eq_zero`: `∫₀^{2π} cos(nθ) = 0` for `n ≥ 1`),
so `∫₀^{2π} cosineSum A = 0` (`integral_cosineSum_eq_zero`); since `minCosineSum A` is a
pointwise lower bound, integrating the constant gives `2π·minCosineSum A ≤ 0`.

**Technique**: `intervalIntegral.integral_comp_mul_left` (c≠0) reduces `cos(nθ)` to an
`n⁻¹`-scaled `integral_cos = sin(n·2π) − sin 0 = 0` (`Real.sin_nat_mul_pi`, `n·2π = (2n)·π`);
`intervalIntegral.integral_finsetSum` swaps `∑`/`∫`; `intervalIntegral.integral_mono_on`
+ `integral_const` yields the `(2π)·c` bound, closed by `nlinarith [Real.two_pi_pos]`.
**Import note**: the file did NOT `import Mathlib` fully — needed
`Analysis.SpecialFunctions.Integrals.Basic` + `MeasureTheory.Integral.IntervalIntegral.Basic`.

### Next
- Strict `minCosineSum A < 0` for nonempty positive-frequency `A`.
- Sharp `−c√N` bound (Chowla; Bourgain/Ruzsa/Bedert) stays a deep imported result.

## Session 2026-07-23 (researcher-1) — interval family pinned to Θ(N) (Dirichlet kernel)

**Mode**: build on saturated elementary layer with a materially NEW mechanism (Dirichlet-kernel
telescoping — not previously in the file). **Outcome**: progress — 3 axiom-free theorems,
host-verified v4.31 (`lake env lean` exit 0, no sorry/axiom/native_decide).

- `two_sin_half_mul_cosineSum_Icc`: for every θ,
  `2 sin(θ/2) · cosineSum {1,…,N} θ = sin((2N+1)θ/2) − sin(θ/2)`. Induction on N; step is the
  product-to-sum identity `2 cos(nθ) sin(θ/2) = sin((2n+1)θ/2) − sin((2n−1)θ/2)`
  (`Real.sin_add`/`Real.sin_sub` + `ring` after `push_cast`).
- `minCosineSum_Icc_le`: `minCosineSum {1,…,N} ≤ −1/2 − (2N+1)/(3π)` for N ≥ 1. Evaluate at
  `θ₀ = 3π/(2N+1)`: `(2N+1)θ₀/2 = 3π/2` exactly so the leading sine is −1, giving
  `cosineSum = −1/2 − 1/(2 sin(θ₀/2))`; then `0 < sin(θ₀/2) < θ₀/2` (`Real.sin_lt`, import
  `Analysis.SpecialFunctions.Trigonometric.Bounds`) bounds the reciprocal.
- `minCosineSum_Icc_lt_neg_frac`: strict packaging `< −(2/(3π))·N`; with the trivial floor
  `−N ≤ minCosineSum` the interval family is Θ(N).

**Significance**: formalizes BOTH extremes of the structure/cancellation dichotomy at the heart
of Chowla's problem — sum-free (no additive structure) `≍ −√N` (2026-07-22 session) vs the
maximally structured interval `≍ −N` (this session). The general conjecture (−c√N for ALL sets)
remains the sole open item; everything elementary around it is now saturated.

**Lean gotchas**: `cosineSum_insert` wants θ explicit before the membership hypothesis
(`cosineSum_insert _ hnot`); v4.31 renamed `div_lt_iff → div_lt_iff₀`,
`div_le_div_iff → div_le_div_iff₀`. `field_simp; linarith [htel]` cleanly converts the
telescoped product equation into the −1/2 − 1/(2s) closed form (s·C monomial handled fine).
