# S8 — Sharper popcount factor-count bound (researcher-2, 2026-06-12)

**Mode**: ACT
**Problem**: cayley-hamilton-minpoly-oq-03-oq-02 — Keller-Gehrig O(n^ω) (Layers 1+2+2.5, axiomatized Layer 3)
**Prior status**: ACT, iteration 7 (S7 STATE-SYNC). Layers 1+2+2.5 + axiomatized Layer 3 shipped and gallery-promoted; one tractable item deferred since S5.

## Outcome

Proved the asymptotically tight factor-count bound that had been deferred
since S5 as "blocked pending a missing Mathlib `Nat.bitIndices` length API":

```lean
theorem squareKrylovProd_factor_count_le_size (j : ℕ) :
    j.bitIndices.length ≤ Nat.size j
```

`Nat.size j = ⌈log₂ (j+1)⌉`, so the popcount of `j` (the number of
squared-Krylov factors the Keller-Gehrig assembly step multiplies to form
`M^j`) is bounded by the bit-length of `j` — the genuinely O(log j)
multiplication count, exponentially sharper than the prior `≤ j` bound.

**The deferral was wrong.** No new Mathlib API was required; the bound
follows in v4.26.0 from `Nat.twoPowSum_bitIndices`, `List.single_le_sum`,
`Nat.lt_size`, `Nat.bitIndices_sorted`, and a `toFinset ⊆ Finset.range`
embedding. The proof is reproduced in `knowledge.md` (S8 outcome section).

## Proof shape

1. `2^i` is a summand of `∑_{i∈bitIndices j} 2^i = j`, so `2^i ≤ j`, so
   `i < Nat.size j` (`Nat.lt_size`).
2. `j.bitIndices` is `Nodup` (`Nat.bitIndices_sorted` → `List.Pairwise.nodup`).
3. Nodup + all-entries-`< Nat.size j` ⇒ length `≤ Nat.size j` via
   `toFinset ⊆ Finset.range (Nat.size j)`, `List.toFinset_card_of_nodup`,
   `Finset.card_le_card`, `Finset.card_range`.

## Gotchas

- `List.Sorted.nodup` deprecated → `List.Pairwise.nodup` (a `Sorted` term
  is accepted directly; `Sorted` reduces to `Pairwise`).
- `Nat.bitIndices_sorted` takes `n` implicitly — passing `j` positionally
  is a type error.

## Files modified

- `proofs/Proofs/CayleyHamiltonMinpolyOQ03OQ02.lean` — `+import
  Mathlib.Data.Nat.Size`, new theorem `squareKrylovProd_factor_count_le_size`,
  updated trailing summary docstring. 333 → 383 LOC, 11 → 12 theorems,
  3 axioms unchanged, 0 sorries.
- `src/data/proofs/cayley-hamilton-minpoly-oq-03-oq-02/meta.json` —
  lineCount/theoremCount, Layer 2.5 + Layer 3 section ranges, import,
  `originalContributions` bullet; removed the now-answered sharper-popcount
  `openQuestion`.
- `src/data/research/problems/cayley-hamilton-minpoly-oq-03-oq-02.json` —
  leanFiles counts, currentState (iter 8), knowledge, blockers, lastUpdate.
- `research/problems/.../state.md`, `knowledge.md` — S8 sections.

## Build

`./proofs/scripts/docker-build.sh Proofs.CayleyHamiltonMinpolyOQ03OQ02` —
**Build succeeded**, 0 errors, 0 warnings (3063 jobs, mathlib v4.26.0 /
lean v4.26.0).

## Knowledge added

- Insights: 1 (the sharper bound is API-free; route is twoPowSum →
  single_le_sum → lt_size → Nodup-into-range)
- Built items: 1 (`squareKrylovProd_factor_count_le_size`)
- Next steps: nextSteps[2] marked RESOLVED

## Status

**Outcome**: progress (one verified theorem; resolves the last tractable
single-problem item). The problem is at a genuine completion-ready state —
the only remaining layer (full O(n^ω) operation count) needs an upstream
Mathlib complexity monad + fast-matmul oracle. Recommend marking the slug
`completed`.
