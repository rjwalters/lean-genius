# erdos-728-factorial-divisibility-oq-04 — knowledge

## Problem
"How do the #728 techniques extend to #729?" Concretely: formalize the elementary
O(log n) barrier `a!·b! ∣ n! ⇒ a + b ≤ n + O(log n)` (the lower bound #728/#729
surpass), in exact Legendre/popcount form.

## Session 2026-06-28 (researcher-8) — SOLVED: integration + prime-uniform sharpening
The Lean file `proofs/Proofs/Erdos728FactorialDivisibilityOQ04.lean` already existed
(committed in PR #31101, 0-axiom/0-sorry, 4 theorems) but was **never integrated**:
not in `Proofs.lean`, no gallery `meta.json`/`annotations.json`, no research json.

This session:
1. **Integrated** the file: added `import Proofs.Erdos728FactorialDivisibilityOQ04`
   to the aggregator; created `src/data/proofs/erdos-728-factorial-divisibility-oq-04/
   {meta,annotations}.json` and the research json. status=verified, badge=original.
2. **Sharpened** the barrier to a prime-uniform form (3 new theorems):
   - `factorial_pval_add_digitsum p m`: Legendre at general prime p,
     `m = (p−1)·v_p(m!) + s_p(m)` (p=2 collapses to the existing p=2 lemma).
   - `log_barrier_prime p`: `a!·b! ∣ n! ⇒ a + b + s_p(n) ≤ n + s_p(a) + s_p(b)` for
     EVERY prime p. Strictly stronger than the classical statement: adds the +s_p(n)
     term (dropped classically) AND holds for all primes (take the best p).
   - `log_barrier_of_prime`: recovers the original `log_barrier` (p=2, drop s₂(n)).

Now 7 theorems, 0 def, 0 axioms, 0 sorries. Host-verified exit 0; #print axioms →
propext/Classical.choice/Quot.sound only.

### Key technique / gotcha
- For a VARIABLE prime p, the term `(p−1)·v_p(m!)` is nonlinear, but **omega
  atomizes identical nonlinear subterms**. So: take `hmono : v_p(a!)+v_p(b!) ≤ v_p(n!)`,
  scale by (p−1) via `Nat.mul_le_mul (le_refl (p-1)) hmono` then `rw [Nat.mul_add]`,
  and feed ha/hb/hn (each containing the SAME `(p−1)·v_p(·!)` syntactic atom) to omega.
- `Nat.digit_sum_le p m` and `sub_one_mul_padicValNat_factorial (p:=p) m` both work
  for general prime p (need `[Fact p.Prime]`).

## Still open (follow-ups, NOT done here)
- Sharpness: infinite families achieving equality in log_barrier_prime at p=2
  (central binomial / multinomial cases).
- Multinomial barrier: a₁!·…·a_k! ∣ n! ⇒ ∑aᵢ + s_p(n) ≤ n + ∑s_p(aᵢ).
- This is the barrier #728/#729 surpass; the actual #729 resolution (large-prime
  carry analysis) is in `Erdos728FactorialDivisibility.lean`, not here.
