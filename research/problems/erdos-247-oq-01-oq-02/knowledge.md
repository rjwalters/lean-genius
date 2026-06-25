# Knowledge Base: erdos-247-oq-01-oq-02

The Exact Reach of Liouville's Method for Lacunary Sums — Erdős Problem #247

Parent: erdos-247-oq-01 (Erdos247Problem.lean), which axiomatizes Erdős's 1975
super-polynomial transcendence theorem (`erdos_transcendence_strong`) and removes
the axiom only for n_k = k!.

---

## Session 2026-06-25 (Session 1) — FRESH → COMPLETED

**Mode**: FRESH
**Outcome**: COMPLETED (verified, 0 axioms, 0 sorries)

### Question addressed
Parent open question: "Prove the Erdős strong-growth theorem without axioms using
the Liouville/Mahler framework in Mathlib." Resolved **partially and precisely**.

### Key mathematical observation
The lacunary sum Σ 1/2^{n_k} is a Liouville number iff its gaps grow fast in
*ratio*, not merely super-polynomially. With head a/2^{n_N} and tail ≤ 2/2^{n_{N+1}},
the Liouville bound 1/(2^{n_N})^m is beaten exactly when n_{N+1} > m·n_N + 1, i.e.
when limsup n_{k+1}/n_k = ∞. This is the **ratio-growth** condition.

- Factorial n_k=(k+1)! has ratio growth (N=m+1: (m+3)! > m·(m+2)!+1) → in the class.
- Geometric n_k=2^k has CONSTANT ratio 2 → NOT ratio growth, even though it satisfies
  the parent's strong-growth condition. So the Liouville-reachable class is a PROPER
  subclass of strong growth, and the axiom is genuinely needed for 2^k.

### Built (Proofs/Erdos247RatioGrowth.lean, self-contained, imports only Mathlib)
- `HasRatioGrowth` definition (∀ m, ∃ N, n_N ≥ 1 ∧ n_{N+1} > m·n_N+1)
- Generic infra: self_le, shift_le, lacunary_summable, tail, tail_summable,
  lacunarySum_split (via Summable.sum_add_tsum_nat_add), partialSum_eq_div,
  tail_pos, tail_le — all for arbitrary StrictMono n (generalize parent's
  factorial-specific lemmas)
- `lacunarySum_liouville` : StrictMono ∧ HasRatioGrowth ⇒ Liouville (axiom-free)
- `lacunarySum_transcendental` : ⇒ Transcendental ℚ
- `factorial_hasRatioGrowth`, `factorial_sum_transcendental_via_ratio`
- `pow2_not_hasRatioGrowth`, `pow2_strong_growth`, `strongGrowth_not_implies_ratioGrowth`
- `ratio_growth_summary`

### Verification
- `lake env lean Proofs/Erdos247RatioGrowth.lean` against prebuilt Mathlib: EXIT 0
  (Docker was down host-wide; verified single-file off main `.lake` per the
  established Docker-down procedure).
- `#print axioms` on all main theorems: only propext / Classical.choice / Quot.sound
  (pow2_not_hasRatioGrowth: propext / Quot.sound). No sorryAx, no Lean.ofReduceBool.
- 19 theorems, 4 definitions, 317 lines, 0 sorries, 0 axiom declarations.

### Honest scope (NOT resolved)
- The general Erdős #247 conjecture (weak growth limsup n_k/k = ∞) — still OPEN.
- Removing the axiom for bounded-ratio strong-growth sequences (e.g. 2^k) — needs
  Mahler's method, beyond Liouville's inequality.

### Next steps
- Formalize Mahler's method to reach 2^k (large undertaking).
- Investigate whether ratio growth is also *necessary* for the sum to be Liouville.
