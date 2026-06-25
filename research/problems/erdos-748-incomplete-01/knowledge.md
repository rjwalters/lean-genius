# Knowledge: erdos-748-incomplete-01

## Research Notes

### Session 2026-06-25 (researcher-9)

File `Erdos748Problem.lean` was already 0-sorry / 2-axiom on arrival (prior
session eliminated `trivial_lower_bound` and fixed mathlib v4.26 breakages).
The two remaining axioms — `green_upper_bound` (Green 2004) and
`precise_asymptotic` (Green/Sapozhenko) — are genuinely deep results; full
formalization is a large project, not a single session.

**Contribution this session:** proved the *maximum size* of a single sum-free
subset of `{1,…,n}` is exactly `⌈n/2⌉ = (n+1)/2` — the rigorous "Schur
connection" that the structure section previously stated only as commentary.
All new theorems are axiom-free (`#print axioms` → only propext/Choice/Quot).

New theorems (Part III-B):
- `sumFree_card_le` : sum-free `A ⊆ Icc 1 n` ⇒ `A.card ≤ (n+1)/2`
- `upperHalf_card_eq` : `(Icc (n/2+1) n).card = (n+1)/2`
- `max_sumFree_card` : both directions packaged (max = ⌈n/2⌉)

Also filled the 3 trivial `native_decide` sorries in `Erdos748Aristotle.lean`
(they duplicate `f_1/f_2/f_3`, already proved in the main file).

## Known Facts

- Lean file: `proofs/Proofs/Erdos748Problem.lean` (0 sorries, 2 deep axioms)
- 15 theorems, 5 defs, lineCount 463

## Approaches Tried

- **Erdős reflection/difference argument** (WORKED, axiom-free) for the max
  sum-free set size. Key: with `m = max A`, the map `x ↦ m - x` is injective on
  `A` (all elements `≤ m`) and its image is disjoint from `A` (a common element
  forces `m = x + z` in `A`, violating sum-freeness). Both `A` and image lie in
  `Icc 0 n`, so `2|A| ≤ n+1`.
  - Lean gotchas: after `Finset.mem_image`, the membership equation
    `(fun x => m - x) x = z` is already beta-reduced by the elaborator, so a
    follow-up `simp only at h` errors "made no progress" — just feed it to
    `omega` directly. `Nat.card_Icc` gives `(Icc a b).card = b + 1 - a`;
    `omega` then discharges `n + 1 - (n/2 + 1) = (n+1)/2`.

## Still Open

- `green_upper_bound`, `precise_asymptotic`: deep (Green 2004, Sapozhenko 2003).
- Structure/classification of the sum-free sets attaining the max size ⌈n/2⌉.
