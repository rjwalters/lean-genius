# Knowledge Base: erdos-510-wip-01

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

## Session 2026-07-22 (researcher-1-9) — union superadditivity + candidate-target assessment

**Mode**: build on saturated elementary layer. **Outcome**: small progress — 2 axiom-free
theorems (host-verified `lake env lean` exit 0, standard triple), plus a scoping
assessment of the remaining elementary targets.

### Added (Erdos510WIP01.lean)
- `cosineSum_union` — disjoint frequency sets add pointwise (`Finset.sum_union`).
- `add_minCosineSum_le_minCosineSum_union` — **superadditivity**: `min A + min B ≤
  min (A ∪ B)` for disjoint A, B; i.e. the negativity m = −min is subadditive.
  The elementary union-bound backbone: −N floor = union of singletons (each −1),
  against which the conjectured sublinear −c√N is measured.

### Candidate-target assessment (why nothing bigger this session)
- **Interval family {1..N}**: computed min ~ −(2N+1)/(3π) − 1/2 (θ = 3π/(2N+1) via
  the telescoped Dirichlet identity 2sin(θ/2)Σcos(nθ) = sin((N+½)θ) − sin(θ/2)).
  Linear negativity — but SUBSUMED: all-odd sets already attain the exact floor −N
  (`minCosineSum_forall_odd`), so an interval example adds no strength. REJECTED.
- **Sidon √N-optimality** (min ≥ −C√N for Sidon A, showing conjectured floor tight):
  needs ∫f⁴ = π·(count of ±a±b±c±d = 0 solutions) via 4-fold product-to-sum, then
  Hölder ∫f² ≤ (∫f⁴)^{1/3}(∫|f|)^{2/3} → ∫|f| ≥ c√N → |min| ≥ c√N... WAIT that
  direction gives min ≤ −c√N for Sidon (a LOWER bound on negativity for a special
  class — the interesting direction!). Route: Sidon ⇒ ∫f⁴ ≤ CπN² ⇒ (πN)³ ≤
  (∫f⁴)(∫|f|)² ⇒ ∫|f| ≥ c√N·π ⇒ ∫f_− = ∫|f|/2 (since ∫f = 0) ⇒
  2π|min| ≥ ∫f_− ⇒ min ≤ −c√N. **This is the strongest feasible elementary
  target**: proves the CONJECTURED −c√N bound for the Sidon class. Est. 2 sessions:
  (1) 4-fold product-to-sum + ∫f⁴ orthogonality count under B₂[1]; (2) Hölder
  (Mathlib `inner_mul_le_norm_mul_norm`/`MeasureTheory.integral` Hölder exists as
  `MeasureTheory.integral_mul_le_Lp_mul_Lq`-style) + negative-part bookkeeping.
  Distinct from the blocked route (which demanded −c√N for ALL A).
- **Uniform −1/2 → −1**: L² method is tight at −1/2 (kept terms saturate); −1
  would need a new mechanism; singleton shows −1 would be sharp. Not attempted.

### Next
Sidon-class −c√N (2-session plan above) is the recommended BUILD target.
