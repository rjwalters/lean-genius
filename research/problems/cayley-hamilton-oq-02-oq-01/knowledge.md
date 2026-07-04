
## Session 2026-07-03 (researcher-16) - Algebraic Ṁ = A·M bridge

**Mode**: FRESH (claimed from available pool, WEAK knowledge tier)
**Outcome**: progress (3 new verified lemmas, 0 sorries, 0 axioms)

### What I Did
- The gallery entry proved only the algebraic *core* (telescoping identity `A·ρ_k = ρ_{k+1}+λ_k•ρ_k`
  and the Cayley–Hamilton truncation `ρ_n = 0`). The analytic completion (`Ṁ = A·M`, ODE uniqueness)
  was fully deferred.
- Isolated the single most important missing bridge: the identity `Ṁ = A·M` is, *before any analysis*,
  the pure-algebra statement
    `A·∑_{k<m} P_k•ρ_k = ∑_{k<m} (λ_k P_k + P_{k-1})•ρ_k`,
  which holds **iff the boundary product `ρ_m = 0` vanishes** — exactly what Cayley–Hamilton provides.
- Formalized it as `A_mul_putzer_sum` (general boundary hypothesis) and `A_mul_putzer_sum_charpoly`
  (boundary discharged by `rho_card` at length `n`), plus the reindexing helper `sum_P_rho_succ`.

### Key Findings
- The `P_{-1} = 0` convention is cleanly encoded without ℕ-subtraction by a second family `Pprev`
  with `Pprev 0 = 0`, `Pprev (k+1) = P k`. Avoids `if k = 0` / `Nat.sub` pain in the sum reindexing.
- The boundary term that the ODE argument must kill is exactly `Pprev m • ρ_m = P_{m-1} • ρ_n`;
  `rho_card` (ρ_n = 0) deletes it. This pins down *where* Cayley–Hamilton enters the analytic proof.
- Proof is pure `CommRing` algebra: `Finset.sum_range_succ'`, `add_smul`, `smul_smul`, `sum_add_distrib`.

### Files Modified
- proofs/Proofs/CayleyHamiltonOQ02OQ01.lean (+3 lemmas, 167→244 lines)
- src/data/proofs/cayley-hamilton-oq-02-oq-01/meta.json (counts + originalContributions)

### Next Steps
- Analytic layer: define P_k(t) as ODE solutions (variation of parameters,
  P_k(t)=∫_0^t e^{λ_k(t-s)}P_{k-1}(s)ds), show M(0)=I, differentiate the finite sum term-by-term to
  get Ṁ = ∑(λ_k P_k + P_{k-1})•ρ_k, then apply `A_mul_putzer_sum_charpoly` to conclude Ṁ = A·M.
- Final step needs matrix-valued ODE uniqueness vs `NormedSpace.exp` — assess Mathlib coverage
  (`NormedSpace.exp`, `hasDerivAt` for `exp (t•A)`); likely the true remaining blocker.

## Session 2026-07-04 (researcher-14) - Algebraic initial condition M(0)=I + IVP packaging

**Mode**: FRESH (claimed from available pool, WEAK knowledge tier)
**Outcome**: progress (2 new verified lemmas, 0 sorries, 0 axioms; build OK via docker)

### What I Did
- The prior sessions supplied the telescoping identity, ρ_n=0 truncation, and the *algebraic*
  `Ṁ = A·M` right-hand side (`A_mul_putzer_sum_charpoly`). The knowledge doc listed "show M(0)=I"
  as the next algebraic gap before the analytic layer.
- Added `putzer_sum_initial`: if `c 0 = 1` and `c k = 0` for all `k > 0`, then
  `∑_{k<m} c_k • ρ_k = 1` (m ≥ 1). Only the k=0 term survives and ρ₀=1. With `c_k = P_k(0)`
  this is exactly the Putzer initial condition `M(0) = I`. One-liner via `Finset.sum_eq_single 0`.
- Added `putzer_ivp_charpoly`: packages BOTH algebraic IVP halves at full length n into a single
  conjunction — `A·M = ∑(λ_k P_k + P_{k-1})•ρ_k` AND `M = 1` — from χ_A = ∏(X-λᵢ) plus Putzer's
  initial data (P₀=1, Pₖ=0 for k>0). This is the complete algebraic skeleton of Putzer's theorem.

### Key Findings
- Both halves of the linear matrix IVP `Ṁ = A·M, M(0)=I` are now pure `CommRing` algebra; the
  ONLY remaining work is genuinely analytic: (1) construct coefficient FUNCTIONS P_k(t) with the
  right HasDerivAt relations and initial values, (2) assemble HasDerivAt over the finite sum,
  (3) matrix-valued ODE uniqueness vs `NormedSpace.exp`. The algebra no longer blocks anything.

### Files Modified
- proofs/Proofs/CayleyHamiltonOQ02OQ01.lean (+2 lemmas, +new section; 244→292 lines, 14→16 thms)
- src/data/proofs/cayley-hamilton-oq-02-oq-01/meta.json (counts, contributions, openQuestions)

### Next Steps
- Analytic layer only (no algebra left): define P_k(t) as ODE solutions (variation of parameters),
  prove HasDerivAt.sum assembly using A_mul_putzer_sum_charpoly for the algebraic step, feed
  M(0)=I from putzer_sum_initial, then matrix ODE uniqueness. Assess Mathlib `ODE_solution_unique`
  / `NormedSpace.exp` coverage for M_n(ℂ)-valued functions — the true remaining blocker.
