
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
