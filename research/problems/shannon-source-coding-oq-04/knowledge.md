# Knowledge Base: shannon-source-coding-oq-04

Insights accumulated during research on this problem.

---

## Problem Understanding

The method of types (Csiszár-Körner 1981) gives a combinatorial proof of Shannon's source
coding theorem. Key objects:
- `empDist n x i` = #{j : x j = i} (empirical distribution of sequence x)
- `typeClass n f hf` = {x : Fin n → Fin k | empDist n x = f} (type class)
- `shannonEntropy p` = -∑ p_i * log p_i (Shannon entropy)
- `empEntropy n hn f` = shannonEntropy of (f i / n) (empirical entropy)
- `typeProb n hn f` = ∏ i, (f i / n)^(f i) = exp(-n H(f/n)) (probability weight per sequence in type class)

---

## Insights

### Proved Theorems (Session 2026-04-25)

**`type_class_size_le_entropy_pow`**: |T_f| ≤ exp(n H(Q)) proved via probability argument:
1. For x ∈ T_f, `∏ j, Q(x j) = typeProb n hn f` (proved via `Finset.prod_fiberwise'`)
   - `prod_fiberwise'` rewrites `∏ j : Fin n, Q (x j)` into `∏ b : Fin k, Q b ^ (empDist n x b)`
   - Since x ∈ T_f means empDist n x = f, this equals `∏ i, Q i ^ (f i) = typeProb`
2. Total probability = 1: `∑ x : Fin n → Fin k, ∏ j, Q (x j) = 1` via `Finset.prod_univ_sum`
   - `prod_univ_sum` gives: `∏ i, (∑ j, f i j) = ∑ x ∈ piFinset, ∏ i, f i (x i)`
   - With f i j = Q j (constant in i): ∏ i, (∑ j, Q j) = ∏ i, 1 = 1
   - `Fintype.piFinset_univ`: piFinset (fun _ => univ) = univ
3. |T_f| * typeProb ≤ 1 via `sum_le_univ_sum_of_nonneg`
4. |T_f| ≤ 1/typeProb = exp(n H(Q)) via `le_div_iff` + exp algebra

**`dominant_type_lower_bound`**: ∃ f, |T_f| ≥ k^n / (n+1)^k proved via pigeonhole:
1. Map sequences to Fin k → Fin (n+1) via empDist (values in {0,...,n})
2. Apply `Finset.exists_le_card_fiber_of_mul_le_card_of_maps_to` (requires `import Mathlib.Combinatorics.Pigeonhole`)
3. Convert fiber to type class using `empDist_sum` for sum constraint

### Key Mathlib Lemmas

- `Finset.prod_fiberwise'`: groups `∏ j ∈ s, f (g j)` by value of g — crucial for rewriting
  sequence product as type-indexed product
- `Finset.prod_univ_sum`: `∏ i, ∑ j, f i j = ∑ x ∈ piFinset, ∏ i, f i (x i)`
  (product of sums = sum of products; multinomial expansion)
- `Fintype.piFinset_univ`: `piFinset (fun _ => Finset.univ) = Finset.univ`
  (converts piFinset form to Finset.univ for total probability sum)
- `Finset.exists_le_card_fiber_of_mul_le_card_of_maps_to`: pigeonhole for cardinality
  (requires `import Mathlib.Combinatorics.Pigeonhole` — not auto-imported via Mathlib.Tactic)
- `sum_le_univ_sum_of_nonneg`: ∑ x ∈ s, f x ≤ ∑ x : α, f x when f ≥ 0

---

## Dead Ends

**Forward references**: Lean 4 does not allow forward references. `total_sequences_eq` (defined in Section 4)
cannot be used in `dominant_type_lower_bound` (Section 2). Fix: inline the proof.

**Missing import**: `Finset.exists_le_card_fiber_of_mul_le_card_of_maps_to` requires explicit
`import Mathlib.Combinatorics.Pigeonhole` — not available via `Mathlib.Tactic` alone.

---

## Remaining Sorries

1. **`type_class_size_eq_multinomial`** (HARD): |T_f| = n! / ∏(f i)! — requires explicit bijection
   between type class and multiset arrangements. ~60 lines. Aristotle candidate.

2. **`source_coding_achievability_mot`** (OPEN): Formal achievability at rate H(p) + ε.
   Requires concentration inequalities and formal coding rate definition. Not tractable soon.

---

## Session 2026-04-25 (Session 1) — Proved 2 of 4 Sorries

**Mode**: FRESH
**Outcome**: PROGRESS — 4 → 2 sorries

### What I Did

1. Surveyed meta.json and existing Lean file structure
2. Proved `type_class_size_le_entropy_pow` via probability argument
3. Proved `dominant_type_lower_bound` via pigeonhole
4. Added `import Mathlib.Combinatorics.Pigeonhole` to imports
5. Fixed build errors: forward reference (inlined `total_sequences_eq`), missing import

### Files Modified

- `proofs/Proofs/ShannonSourceCodingOQ04.lean` (247 → 352 lines, 4 → 2 sorries)
- `src/data/proofs/shannon-source-coding-oq-04/meta.json` (updated sorries, lineCount, contributions)
- `research/problems/shannon-source-coding-oq-04/knowledge.md` (this file)

### Next Steps

1. Submit `type_class_size_eq_multinomial` to Aristotle (HARD — known bijection, ~60 lines)
2. Leave `source_coding_achievability_mot` as OPEN (requires LLN/concentration infrastructure)
3. Advance phase to ACT
