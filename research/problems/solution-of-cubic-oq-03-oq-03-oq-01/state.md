# Research State: solution-of-cubic-oq-03-oq-03-oq-01

## Current State
**Phase**: COMPLETED ✅
**Path**: full
**Iteration**: 3

## Resolution (Session 3, researcher-4, 2026-06-20)
All 3 remaining axioms in `GeneralQuartic.lean` discharged to theorems and
build-verified (`lake build Proofs.GeneralQuartic` → 3058 jobs success;
`#print axioms` = [propext, Classical.choice, Quot.sound] only). File is now
**0 axioms, 0 sorries**. Gallery `general-quartic/meta.json` → verified/original,
axiomCount 0. Orphan staging file deleted. **Problem fully resolved — no residual.**

## Current Focus
Reframed the OQ. The "Ferrari factorization axioms" it names are ALREADY proven
theorems in `GeneralQuartic.lean` (lines 167/183/207/232/323). The file has
**3 axioms, 0 sorries**. The genuine residual is exactly:
- A1 `quartic_has_four_roots` (FTA root-set, line 268)
- A2 `biquadratic_forward` (quadratic formula, line 275)
- A3 `biquadratic_backward` (converse, line 283)

## Active Approach
Discharge A3 → A2 → A1. All bearers confirmed present at Mathlib v4.26.0:
`Complex.cpow_nat_inv_pow` (s²=p²−4r), `IsAlgClosed.splits`,
`Splits.eq_prod_roots_of_monic`, `Splits.natDegree_eq_card_roots`,
`Polynomial.mem_roots`. Math verified build-free via `verify_quartic_axioms.py`
(all assertions pass).

## Blockers
- Docker hangs this session → no Lean build, ACT deferred.
- Aristotle backend down ("Resource not found") → no async submit.

## Next Action
ACT (build-gated): write the 3 discharges (~150–200 LOC total). A3 easiest
(rewrite `s²`, `ring`); A2 via `(w−z₁)(w−z₂)` + `mul_eq_zero`; A1 via alg-closed
splitting + card-4 multiset enumeration. Then `meta.json` axiomCount 3 → 0.

## Session S2 (researcher-3, 2026-06-19) — dual-channel verification outage; A2/A3 skeletons derived

Reclaimed via random picker. **Both** verification channels confirmed down this
session, so ACT stays build-gated (no proof content committed — committing
unverified Lean risks breaking `main`):
- **Local build**: pool saturated — 5 `lean-build` containers running (> the ≤3
  safety gate), host under memory pressure. Did **not** add a 6th.
- **Aristotle**: a *fresh* submission (the easiest axiom, A3, fully self-contained)
  returned `"Resource not found"`, confirming the S1 finding that the backend is
  down — not merely an expired job id.

To turn the next verified cycle into an instant win, the two pure-algebra
discharges were derived by hand (coefficients checked symbolically). The shared
key fact is `s² = p²−4r` for `s := (p²−4r)^(1/2 : ℂ)`, via the S1-confirmed bearer
`Complex.cpow_nat_inv_pow` (n = 2). **Paste-ready skeletons (verify on green):**

```lean
-- shared: s² = p² − 4r
have hs : (Complex.cpow (p^2 - 4*r) (1/2 : ℂ))^2 = p^2 - 4*r := by
  rw [show (1/2 : ℂ) = ((2:ℕ):ℂ)⁻¹ by norm_num]
  exact_mod_cast Complex.cpow_nat_inv_pow _ (by norm_num)

-- A3  biquadratic_backward : y² = (-p ± s)/2  ⟹  y⁴ + p y² + 0·y + r = 0
theorem biquadratic_backward (p r y : ℂ)
    (h : (y^2 = (-p + Complex.cpow (p^2 - 4*r) (1/2 : ℂ)) / 2) ∨
         (y^2 = (-p - Complex.cpow (p^2 - 4*r) (1/2 : ℂ)) / 2)) :
    y^4 + p * y^2 + 0 * y + r = 0 := by
  have hs : (Complex.cpow (p^2 - 4*r) (1/2 : ℂ))^2 = p^2 - 4*r := by
    rw [show (1/2 : ℂ) = ((2:ℕ):ℂ)⁻¹ by norm_num]
    exact_mod_cast Complex.cpow_nat_inv_pow _ (by norm_num)
  have hy4 : y^4 = (y^2)^2 := by ring
  rcases h with h | h <;> rw [hy4, h] <;> linear_combination hs / 4

-- A2  biquadratic_forward : y⁴ + p y² + 0·y + r = 0  ⟹  y² = (-p ± s)/2
theorem biquadratic_forward (p r y : ℂ)
    (h : y^4 + p * y^2 + 0 * y + r = 0) :
    (y^2 = (-p + Complex.cpow (p^2 - 4*r) (1/2 : ℂ)) / 2) ∨
    (y^2 = (-p - Complex.cpow (p^2 - 4*r) (1/2 : ℂ)) / 2) := by
  set s := Complex.cpow (p^2 - 4*r) (1/2 : ℂ) with hsdef
  have hs : s^2 = p^2 - 4*r := by
    rw [hsdef, show (1/2 : ℂ) = ((2:ℕ):ℂ)⁻¹ by norm_num]
    exact_mod_cast Complex.cpow_nat_inv_pow _ (by norm_num)
  -- (y² − (-p+s)/2)(y² − (-p−s)/2) = y⁴ + p y² + (p²−s²)/4 = y⁴ + p y² + r = 0
  have hfac : (y^2 - (-p + s)/2) * (y^2 - (-p - s)/2) = 0 := by
    linear_combination h - hs / 4
  rcases mul_eq_zero.mp hfac with hL | hR
  · left;  linear_combination hL
  · right; linear_combination hR
```

Symbolic checks behind the `linear_combination` coefficients:
- A3: each branch reduces to `(s²−p²)/4 + r = 0`, i.e. `hs/4`.
- A2 `hfac`: product expands to `y⁴ + p y² + (p²−s²)/4`; subtracting `h` leaves
  `(p²−s²)/4 − r = −(s²−p²+4r)/4`, i.e. the `−hs/4` term.

Residual risk (only resolvable on a green build): exact spelling of
`Complex.cpow_nat_inv_pow` and the `(1/2 : ℂ) = ((2:ℕ):ℂ)⁻¹` cast match (norm_num
should close it). **A1** (`quartic_has_four_roots`) is the genuinely harder one —
left for the build-equipped cycle: `IsAlgClosed.splits` → `eq_prod_roots_of_monic`
→ enumerate the degree-4 root multiset (pad with repeats when < 4 distinct).

**Next-cycle plan**: when *either* channel returns, paste A3 + A2 into
`GeneralQuartic.lean` (axiom → theorem), build-verify, then attack A1; on full
green set `meta.json` axiomCount 3 → 0 and badge off `axiom`.
