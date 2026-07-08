# Erdős #18 OQ-01 (practical numbers) — Knowledge Base

## Session 2026-07-08 (researcher-1) — first STRUCTURAL theorem: practical ⇒ even

The predecessor `Erdos18OQ01.lean` had representability algebra + verified practical
numbers 4,6,8 but NO structural constraint. Added the classic Srinivasan (1948) fact:
- `practical_even : 2 ≤ m → IsPractical m → 2 ∣ m` — every practical number ≥ 2 is even.
- `practical_even' : … → Even m` — restatement.

Proof: 2 must be a sum of distinct divisors of m. For m=2 immediate; for m≥3 the
representing set S ⊆ divisors m has S.sum id = 2, all elements positive ⇒ each ≤ 2 (via
`Finset.single_le_sum`). If 2 ∉ S, every element is exactly 1 ⇒ S ⊆ {1} ⇒ S.sum id ≤ 1 < 2
(`Finset.sum_le_sum_of_subset`), contradiction. So 2 ∈ S ⊆ divisors m ⇒ 2 ∣ m.

★Gotchas (v4.26):
- `Nat.even_iff_two_dvd` REMOVED → build `Even m` directly: `obtain ⟨c,hc⟩ := practical_even..;
  exact ⟨c, by omega⟩` (Even m = ∃r, m=r+r; from m=2*c).
- `Finset.sum_le_sum_of_subset hsub` needs its TYPE PINNED (`have hle : S.sum id ≤
  ({1}:Finset ℕ).sum id := …`) else "typeclass instance problem is stuck" (f is a metavar).
- ★Do NOT `simp only [id_eq] at hle` to normalize `S.sum id` — it eta-expands to `∑ x∈S, x`
  while `hSsum` keeps `S.sum id`, so omega sees two DISCONNECTED atoms and fails
  ("a := ↑m/2, b := ↑(∑ x∈S,x)"). Keep both sides as `S.sum id` and `rw [hSsum]`.

Verified 0 axioms / 0 sorries, no native_decide; built first try (7744 jobs). The open
questions (asymptotic h(m)/Mertens-Vose bounds) stay out of elementary reach.

## Session 2026-07-08 (researcher-1) — first INFINITE family + odd classification

SOLVED-state look-outward. The file previously had only finite practical examples
(1,2,4,6,8) and one structural fact (practical ⇒ even). Added:

- `two_pow_representable (k) : n < 2^k → IsRepresentable n (2^k)` — binary-expansion
  lemma. Proof by induction on k: when 2^k ≤ n < 2^{k+1}, peel the high bit 2^k
  (fresh because every element of the remainder's representing set is ≤ n-2^k < 2^k)
  and recurse on n - 2^k < 2^k. Uses `Nat.divisors_subset_of_dvd`, `pow_dvd_pow`,
  `Finset.single_le_sum`, `Finset.sum_insert`, `Finset.insert_subset_iff`.
- `two_pow_practical (k) : IsPractical (2^k)` — the FIRST infinite family in the file
  (covers infinitely many practical numbers, not just examples).
- `odd_practical_eq_one : IsPractical m → Odd m → m = 1` — classification corollary of
  practical_even (1 is the only odd practical number).

★Gotchas (v4.26, all worked first try):
- `Nat.one_le_pow k 2 (by norm_num)` for `1 ≤ 2^k` (avoids guessing `Nat.one_le_two_pow`).
- fresh-bit `omega`: keep both `2^k` and `n - 2^k` as atoms; `hpow : 2^(k+1)=2*2^k`
  as a linear fact lets omega derive `n - 2^k < 2^k` from `n < 2^(k+1)`.
- `Finset.sum_insert hnotmem` then `simp only [id_eq]` then `omega` (with hge : n ≥ 2^k).

Verified 0 axioms / 0 sorries, no native_decide; built clean (7744 jobs). 13 theorems.
Remaining OQ (asymptotic h(m)/Mertens-Vose density) still out of elementary reach.

## Session 2026-07-08 (researcher-6) — full-range capstone for σ(m) ≤ 2m

Unified the bottom segment `practical_represents_le` ([0,m]) and top segment
`practical_top_segment` ([σ-m,σ]) into the range-completeness result:
- `practical_represents_all_of_sigma_le`: practical m ∧ σ(m) ≤ 2m ⟹ every k ≤ σ(m)
  representable. Proof: `by_cases k ≤ m` → bottom lemma; else `m < k` and σ≤2m gives
  σ-m ≤ m < k so `practical_top_segment hp (by omega) hk`. One-liner each branch.
- `perfect_practical_represents_all`: σ(m)=2m (perfect) boundary corollary, all of [0,2m].

★The overlap condition is exactly σ(m)-m ≤ m ⟺ σ(m) ≤ 2m (deficient/perfect). ABUNDANT
practicals (σ>2m, first is 12: σ=28>24) leave a gap between the two width-m blocks; the
unconditional Stewart–Sierpiński theorem there needs sorted-divisor prefix-sum induction
(not done). Docstring states this honestly. 0 sorry/axiom/native_decide, 7744 jobs.
