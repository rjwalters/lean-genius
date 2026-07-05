# Knowledge Base: euler-totient-oq-06-oq-02

Insights accumulated during research on this problem.

---

## Problem Understanding

[Initial observations about the problem will be recorded here]

---

## Insights

[Insights from research attempts will be accumulated here]

---

## Dead Ends

[Approaches known not to work will be documented here]

---

## RESOLVED (researcher-4, 2026-07-02) — PR #32932 [VERIFIED, 0-axiom]

**Answer.** v₂(φ(n)) = 1  (⟺ φ(n) ≡ 2 mod 4)  ⟺  n ∈ {4} ∪ {p^k, 2p^k : p prime, p≡3 mod4, k≥1}.

**Key correction:** the problem's proposed characterization "n = p^k or 2p^k" MISSES n=4
(φ(4)=2≡2 mod4, but 4 is a pure 2-power with no odd prime factor). Recorded as
`four_is_extra_solution`. Also the exponent need not be 1: p^k works for any k≥1 since
p^(k-1) is odd.

**Proof engine.** Reduce mod-4 → valuation (v₂(m)=1 ↔ m≡2 mod4 via padicValNat_dvd_iff_le).
Master split v₂(φ n)=(v₂(n)−1)+Σ_{odd p∣n} v₂(p−1) via ordProj/ordCompl decomposition +
padicValNat.mul. Each odd summand ≥1, so sum=1 ⟹ single odd prime (Finset.card_nsmul_le_sum
+ isPrimePow_iff_card_primeFactors_eq_one). Finite case on a=v₂(n): a≤1→n=p^k/2p^k; a=2→n=4;
a≥3→impossible. Lean file EulerTotientOQ06OQ02.lean, 12 thm / 334 L, verified lake env lean.
