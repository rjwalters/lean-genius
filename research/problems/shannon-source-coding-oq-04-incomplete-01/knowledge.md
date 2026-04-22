# Knowledge Base: shannon-source-coding-oq-04-incomplete-01

Insights accumulated during research on this problem.

---

## Problem Understanding

The Lean file `Proofs/ShannonSourceCodingOQ04.lean` contains a 230-line formalization of the
method of types proof of Shannon's source coding theorem. The infrastructure is solid:

**Proved theorems (0-sorry):**
- `empDist_sum`: ∑ empDist x = n
- `type_class_partition`: sequences partition into exactly one type class each
- `count_types_le`: ≤ (n+1)^k distinct types
- `total_sequences_eq`: k^n total sequences
- `empEntropy_eq_shannonEntropy`: empirical entropy = Shannon entropy of normalized type
- `log_typeProb_eq`: log Q^n(x) = -n H(Q) for any x ∈ T_f

**Open sorries:**
1. `type_class_size_eq_multinomial`: |T_f| = n!/∏(f_i)! — multinomial bijection (~line 67)
2. `type_class_size_le_entropy_pow`: |T_f| ≤ exp(n H(Q)) — from probability sum (~line 172)
3. `dominant_type_lower_bound`: max type class size ≥ k^n/(n+1)^k — pigeonhole (~line 205)
4. `source_coding_achievability_mot`: rate H(p) achievable — full convergence (~line 225)

**Key insight already exploited**: Every x ∈ T_f has Q^n(x) = exp(-n H(Q)).
This is the bridge between the combinatorial and probabilistic views.

---

## Insights

[Insights from research attempts will be accumulated here]

---

## Dead Ends

[Approaches known not to work will be documented here]
