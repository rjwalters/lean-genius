# Knowledge Base: erdos-1-oq-04

Insights accumulated during research on this problem.

The OQ-04 question asks: characterize the structure of extremal sets
achieving the minimum N for n-element subsets of {1,...,N} with all 2^n
subset sums distinct. The minimum values f(n) form OEIS A005318:
0, 1, 2, 4, 7, 13, 24, 44, 84, 161, 309, ...

The Conway-Guy conjecture (1968) provides the conjectured exact extremal
sets and the recurrence aₙ = aₙ₋₁ + ⌈Sₙ₋₁/2⌉.

---

## Problem Understanding

The Lean file `proofs/Proofs/Erdos1OQ04.lean` (245 lines, 0 sorries, 0
axioms) contains:

- `hasDistinctSubsetSums` — Prop that all subset sums are distinct
- Decidable instance via powerset enumeration
- `achievesDistinctSums n N` — exists n-element DSS set in {1,...,N}
- `conwayGuySeq` — explicit values for n ≤ 8 (case-by-case, since the
  ceiling-based recurrence is awkward in Lean ℕ recursion)
- `conwayGuyConjecture` — the open conjecture statement
- Verified small cases: f(1)=1, f(2)=2, f(3)≤4, f(4)≤7, f(5)≤13, all
  via `native_decide`
- `powers_of_two_dss`: the binary set {1,2,4,...,2^{n-1}} achieves DSS,
  giving f(n) ≤ 2^n - 1 as a baseline

---

## Insights

### 2026-04-27 (researcher-4)

1. **File is fully verified, 0 axioms** — a rare "clean" file in the
   gallery. No axiom-elimination work needed.

2. **The `conwayGuyConjecture` Prop is the open question** — proving it
   would solve OQ-04 affirmatively. Two parts:
   - achievesDistinctSums n (conwayGuySeq n) — exists witness set; for
     small n this is just `native_decide` with the right set, but
     Conway-Guy's general construction is what's needed
   - ¬achievesDistinctSums n (conwayGuySeq n - 1) — the genuinely hard
     direction (no smaller set exists)

3. **Added monotonicity lemma** `achievesDistinctSums_mono`: relaxing N
   preserves the property. Standalone proof, 5 lines, useful for any
   future "this candidate works at this loose bound" reasoning. Pure
   structural infrastructure addition — does not advance the conjecture
   but is a natural building block.

4. **The Conway-Guy recurrence in Lean** — the documented difficulty is
   that aₙ = aₙ₋₁ + ⌈Sₙ₋₁/2⌉ requires carrying partial sums Sₙ. A clean
   formulation would use a tuple-valued auxiliary recursion:
   ```
   def cgAux : ℕ → ℕ × ℕ
     | 0 => (0, 0)
     | n+1 => let (a, s) := cgAux n
              let a' := a + (s + 1) / 2  -- ceiling division
              (a', s + a')
   ```
   This is tractable but needs sanity-checking against the OEIS values.

5. **Adding more verified small cases** — f(6) = 24 via Conway-Guy set
   (the n=6 set is in the Conway-Guy 1968 paper; literature lookup
   needed for the exact set). `native_decide` would have to check
   64×64 = 4096 sum-pair equalities; may be slow during compilation
   but should finish.

6. **Suspicious file structure**: the file ends with a bare `end` at
   line 245 without a matching `namespace`. The file presumably builds
   (0 sorries, 0 axioms in metadata; recent commit), but if the
   bare-end is rejected by a future Lean version, this needs cleanup.
   Did not modify in this session.

---

## Dead Ends

- **Don't try to prove the optimality direction** of the Conway-Guy
  conjecture from scratch — that's the open conjecture itself.
- **Don't use `native_decide` recklessly** — for n ≥ 7 the powerset has
  128 elements, 16384 sum-pair checks; compile time risk.
- **Don't replace the case-by-case `conwayGuySeq`** with the recurrence
  unless the auxiliary function is sanity-checked against OEIS A005318.

---

## Next Session

- Replace the case-by-case `conwayGuySeq` with the auxiliary recurrence
  formulation (sketch in insight #4). Verify by computing a few values.
- Add f(6) ≤ 24 with the documented Conway-Guy 6-element set (literature
  lookup needed for the exact set).
- Optionally clean up the bare `end` at line 245 (cosmetic).
