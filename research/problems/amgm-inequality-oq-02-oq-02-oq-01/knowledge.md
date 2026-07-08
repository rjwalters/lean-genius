# Knowledge: amgm-inequality-oq-02-oq-02-oq-01 — Signed-input Newton inequality

## Problem
Newton's inequality `p_k² ≥ p_{k-1} p_{k+1}` (normalized `p_k = e_k/C(n,k)`) for
**signed** (arbitrary real) inputs, generalizing the parent
`amgm-inequality-oq-02-oq-02` (`NewtonLogConcavity`), which proves it only for
**non-negative** inputs.  Classically the inequality holds for all real inputs
because `∏(t - xᵢ)` is real-rooted regardless of the signs of its roots.

## State of the art in the gallery (before this session)
- `maclaurin_sq_m1_ge_m2_general` (`AmgmInequalityOQ02Defs`) already proves the
  **k = 1** case for arbitrary real `x`, with **no sign hypothesis**:
  `C(n,2)·(∑xᵢ)² ≥ n²·e₂`.  It is exactly Cauchy–Schwarz `∑ᵢⱼ (xᵢ-xⱼ)² ≥ 0`.
- The small cases `maclaurin_m1sq_ge_m2_n3` / `_n4` are also stated for reals
  (no sign hypothesis).
- The general **k ≥ 2** case (`newton_log_concavity_proved`) requires
  non-negativity — the cleared-denominator induction uses `eⱼ ≥ 0` essentially.

## Session 2026-07-07 (REVISIT) — first genuinely intermediate index n=4, k=2

**Mode:** REVISIT (MODERATE-tier knowledge, highest priority in pool)
**Outcome:** progress — **build-VERIFIED** (docker 7744 jobs, 0 sorry / 0 axiom).

### What I did
Added `newton_n4_k2_signed` to `NewtonSignedInputs.lean`. This is the **first
Newton index that is genuinely interior**: for `n = 4`, `k = 2` satisfies
`1 < 2 < 3 = n-1`, so it is neither the Cauchy–Schwarz base (`k = 1`, already
signed) nor the reciprocal-duality top (`k = n-1`, `newton_signed_top`). Prior
to this session every signed case in the file was one of those two endpoints (or
`n = 3, k = 2`, which is the top index for `n = 3`).

### Key finding — the interior case is still elementary (SOS)
The normalized inequality `p₂² ≥ p₁ p₃` (with `p₁=e₁/4, p₂=e₂/6, p₃=e₃/4`),
cleared of its `144` denominator, is `4 e₂² ≥ 9 e₁ e₃`, and the **exact
identity** (verified by expansion in sympy)

    4 e₂² − 9 e₁ e₃
      = 3·[(ab−cd)² + (ac−bd)² + (ad−bc)²]
        + ½·[((a−b)(c−d))² + ((a−c)(b−d))² + ((a−d)(b−c))²]

certifies non-negativity for **all** real `a,b,c,d`. The two square families are
indexed by the three complementary-pair splits of `{a,b,c,d}`. `nlinarith` with
these six `sq_nonneg` hints closes the goal directly. So the smallest interior
Newton inequality does **not** require the real-rootedness / Rolle machinery.

### Files modified
- `proofs/Proofs/NewtonSignedInputs.lean` (+`newton_n4_k2_signed`, Part IV +
  header/frontier note updates)
- `src/data/research/problems/amgm-inequality-oq-02-oq-02-oq-01.json` (knowledge)

### Next steps
- Probe how far plain SOS reaches: try `n=5, k=2` and other small interior
  `(n,k)`. Newton differences are PSD but not always plain SOS in the elementary
  symmetric variables; the first `nlinarith` failure flags where a genuine
  multiplier/denominator (hence real-rootedness) becomes necessary.
- Long-term uniform route: formalize "derivative of a real-rooted polynomial is
  real-rooted" (Rolle across the root multiset + Vieta for `P'`).

## Session 2026-07-04 (FRESH) — top-index via reciprocal duality

**Outcome:** progress (proof written, 0 sorry / 0 axiom by construction) but
**build-unverified** — the Docker build infrastructure was corrupt the entire
session (containerd `meta.db` I/O error blocking image build; earlier attempts
hit a corrupt Mathlib `.ir` header and SIGBUS exit 135).  The failing target was
`AmgmInequalityOQ02Defs`, an *existing verified* dependency, confirming the
failure is infrastructure, not the new file.

### What was proved (`proofs/Proofs/NewtonSignedInputs.lean`)
1. **`elemSymm_inv_mul`** — reciprocal identity: for nonzero `x` and `k ≤ n`,
   `eₖ(1/x₁,…,1/xₙ)·eₙ(x) = e_{n-k}(x)`.
   Proof: multiply by `eₙ(x) = ∏xᵢ`; the `k`-subset term becomes
   `(∏_{i∈S}xᵢ⁻¹)·∏xᵢ = ∏_{i∈Sᶜ}xᵢ`, and `S ↦ Sᶜ` bijects `k`-subsets with
   `(n-k)`-subsets (`Finset.sum_bij'` + `Finset.prod_mul_prod_compl`).
2. **`newton_signed_top`** — Newton at the **top index** `k = n-1`, all `n ≥ 2`,
   all nonzero reals: `C(n,2)·e_{n-1}² ≥ n²·e_{n-2}·eₙ`.
   Proof: apply the (already signed) `k = 1` inequality to `yᵢ = 1/xᵢ`, then use
   `eₖ(y) = e_{n-k}(x)/eₙ(x)` and clear the positive factor `eₙ(x)²`.
   This transports signedness from the bottom index to the top index for all n.
3. **`newton_n3_k2_signed`** — `n=3, k=2` for arbitrary reals (incl. zeros):
   `((ab+bc+ca)/3)² ≥ ((a+b+c)/3)·abc`, via the SOS identity
   `(ab+bc+ca)² − 3abc(a+b+c) = ½[(ab−bc)²+(bc−ca)²+(ca−ab)²]`.
   The gallery's `newton_n3_k2` assumed `a,b,c ≥ 0` unnecessarily.

### Frontier (still open)
Intermediate indices `1 < k < n-1` for general `n` need the real-rootedness /
Rolle machinery: differentiate `P(t)=∏(t-xᵢ)` (stays real-rooted), its
coefficients are `(n-j)eⱼ`, reduce Newton at `k` to a real quadratic
discriminant.  Mathlib lacks a packaged "derivative of a real-rooted polynomial
is real-rooted" lemma.

### Next steps
- Build-verify `NewtonSignedInputs.lean` once Docker recovers.  Mechanical
  risks: `Finset.sum_bij'` argument order; the `rw` chains in `newton_signed_top`.
- Formalize the real-rootedness route for intermediate `k`.
- Drop the `xᵢ ≠ 0` hypothesis on the top index via a continuity/`eₙ=0` split.
