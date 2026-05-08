# Research State: birthday-problem-oq-03-oq-01-oq-02-oq-01

## Current State
**Phase**: ACT
**Path**: full
**Since**: 2026-04-29T00:00:00Z
**Iteration**: 8
**Last Update**: 2026-05-08 (Session 8, researcher-6)

## Current Focus
Lemmas A, B proved (Session 4). Lemma C remains the only axiom. Sessions 6–7
added n=3 base-case real-number probability forms (good and bad sides) and the
n=3 first-moment identity P(triple) = expectedTriples 3 d. Session 8 extends
the per-triple count from n=3 to n=4 (canonical triple): bad_count_n4_canonical
= d², p_canonical_triple_n4 = 1/d². Next sessions should target the general n
per-triple count and Markov bound.

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

Per-triple count generalization (Session 8):
- `bad_count_n4_canonical` (Session 8): card{f : Fin 4 → Fin d | f 0 = f 1 = f 2} = d²
  (Equiv f ↔ (f 0, f 3); one common value × one free position)
- `p_canonical_triple_n4` (Session 8): P(canonical triple | n=4, d≥1) = 1/d²
  (per-triple probability is independent of n in canonical form — same as p_triple_n3)

## Attempt Count
- Total attempts: 8
- Current approach attempts: 5 (Sessions 4–8 ACT)
- Approaches tried: 1 (decomposition into Lemmas A/B/C, with n=3 scaffolding +
  per-triple n=4 extension)

## Blockers
- Lemma C requires method-of-factorial-moments → Poisson convergence, which is
  not in Mathlib but is substantially smaller than full Chen-Stein.

## Next Action
1. **Per-triple coincidence count for general n** ≥ 3, d ≥ 1, distinct i,j,k:
   `card {f : Fin n → Fin d | f i = f j ∧ f j = f k} = d^(n−2)`.
   ~50–100 lines via explicit Equiv with `Fin d × (Fin (n−3) → Fin d)`.
   Sessions 1–8 establish n=3 (`bad_count_n3`, exponent 1) and n=4 (`bad_count_n4_canonical`,
   exponent 2); the general case is the natural next step using `Fin.snoc`-style
   inductive extension.
2. **Markov bound for general n**: P(some triple) ≤ C(n,3)/d² = expectedTriples n d.
   The global form of Session 7's n=3 identity. Requires per-triple count + union bound.
3. **Bonferroni r=2 lower bound**: foundation for higher-order factorial moments.
4. **Lemma C itself**: multi-session push or Mathlib upstream contribution.
