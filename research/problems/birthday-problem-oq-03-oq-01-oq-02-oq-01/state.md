# Research State: birthday-problem-oq-03-oq-01-oq-02-oq-01

## Current State
**Phase**: ACT
**Path**: full
**Since**: 2026-04-29T00:00:00Z
**Iteration**: 7
**Last Update**: 2026-05-08 (Session 7, researcher-9)

## Current Focus
Lemmas A, B proved (Session 4). Lemma C remains the only axiom. Sessions 6–7
added n=3 base-case real-number probability forms (good and bad sides) and the
n=3 first-moment identity P(triple) = expectedTriples 3 d. Next sessions should
target the per-triple coincidence count and Markov bound for general n.

## Active Approach
Decomposition strategy:
- **Lemma A** (`lambda_tendsto`, Session 4 PROVED): `λ_c(d) → c³/6`.
- **Lemma B** (`exp_lambda_tendsto`, Session 4 PROVED): `exp(−λ_c(d)) → exp(−c³/6)`.
- **Lemma C** (`p_no_triple_tendsto`, axiom): `P_no_triple(n_c(d), d) → exp(−c³/6)`.
  Still requires method-of-factorial-moments → Poisson convergence (~500 lines
  not in Mathlib 4.26).

n=3 base-case scaffolding (Sessions 6–7):
- `p_no_triple_n3` (Session 6): P(no triple|n=3) = 1 − 1/d²
- `p_triple_n3` (Session 7): P(triple|n=3) = 1/d²
- `p_triple_n3_eq_expectedTriples` (Session 7): n=3 first-moment identity

## Attempt Count
- Total attempts: 7
- Current approach attempts: 4 (Sessions 4–7 ACT)
- Approaches tried: 1 (decomposition into Lemmas A/B/C, with n=3 scaffolding)

## Blockers
- Lemma C requires method-of-factorial-moments → Poisson convergence, which is
  not in Mathlib but is substantially smaller than full Chen-Stein.

## Next Action
1. **Per-triple coincidence count** for n ≥ 3, d ≥ 1, distinct i,j,k:
   `card {f : Fin n → Fin d | f i = f j ∧ f j = f k} = d^(n−2)`.
   ~50–100 lines via explicit Equiv with `Fin d × (Fin (n−3) → Fin d)`.
2. **Markov bound for general n**: P(some triple) ≤ C(n,3)/d² = expectedTriples n d.
   The global form of Session 7's n=3 identity.
3. **Bonferroni r=2 lower bound**: foundation for higher-order factorial moments.
4. **Lemma C itself**: multi-session push or Mathlib upstream contribution.
