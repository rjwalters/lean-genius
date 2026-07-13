# Knowledge Base: lhopital-oq-04-oq-01

Insights accumulated during research on this problem.

---

## Session 2026-06-30 (Session 1) — SOLVED (FRESH)

**Mode**: FRESH · **Outcome**: completed (0 sorries, 0 axioms, no native_decide)
**File**: `proofs/Proofs/LHopitalOQ04OQ01.lean` (200 lines, 6 theorems)

### What I Did
Formalized iterated L'Hôpital as a ratio of n-th Taylor coefficients via the
recommended little-o / `Real.taylor_tendsto` route (Approach 1 from problem.md).

### Key Findings / Techniques
- **`Real.taylor_tendsto (convex_univ) (Set.mem_univ a) hf.contDiffOn`** is the whole
  analytic input: `(f x − taylorWithinEval f n univ a x)/(x−a)^n → 0` along `𝓝[univ] a`.
  Rewrite `nhdsWithin_univ` then `.mono_left nhdsWithin_le_nhds` restricts to `𝓝[≠] a`.
- **Polynomial collapse** (`taylorWithinEval_collapse`): `taylor_within_apply` +
  `Finset.sum_range_succ` splits off the k=n term; the range-n remainder is
  `Finset.sum_eq_zero` because each summand carries `iteratedDeriv k f a = 0`. Use
  `iteratedDerivWithin_univ` to bridge within→plain derivatives, `smul_eq_mul` for ℝ.
  Note: `rw [iteratedDerivWithin_univ]` after `sum_range_succ` only hits the *outer*
  k=n term (the bound-variable occurrences inside the sum are shielded from rw).
- **Coefficient limit** built by `htaylor'.add tendsto_const_nhds` then `Tendsto.congr'`;
  pointwise `field_simp; ring` after `rw [taylorWithinEval_collapse]`.
- **Ratio step** = parent template: `hF.div hG hgn'`, then `div_div_div_cancel_right₀`
  cancels the shared `n!` in the limit value AND the shared `(x−a)^n` pointwise. Needed
  `simp only [Pi.div_apply]` before the pointwise cancel (Tendsto.div gives a `Pi.div`,
  not a beta-reduced `fun x => …/…`).
- **Example** `(1−cos x)/x² → 1/2`: computed f''(0)=1, g''(0)=2 via `iteratedDeriv_succ`/
  `iteratedDeriv_one` + `HasDerivAt.deriv` (deriv(1−cos)=sin, deriv(x²)=2x); vanishing of
  order 0,1 by `interval_cases k`. All plain tactics → 0-axiom.

### Gotchas
- Factorial `!` notation is `scoped notation … => Nat.factorial` in namespace `Nat` →
  **must `open Nat`** or `(n ! : ℝ)` fails to parse ("unexpected token ':'").
- `Nat.factorial_pos n |>.ne'` for `(n! : ℝ) ≠ 0` via `Nat.cast_ne_zero.mpr`.

### Status
COMPLETE. Verified 0-axiom. PR pending.

---

## Follow-up open questions generated
- One-sided Lagrange-remainder route (`taylor_mean_remainder_lagrange_iteratedDeriv`).
- Mismatched vanishing orders: `g^(n)(a)=0` but `g^(m)(a)≠0`, m>n.
