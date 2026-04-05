# Knowledge Base: erdos-1069 — Szemerédi-Trotter k-Rich Lines

Insights accumulated during research on this problem.

---

## Problem Understanding

**Goal**: Reduce axiom count from 2 → 1 by proving `kRich_bound` from `szemeredi_trotter`.

The current Lean file has exactly 2 axioms (lines 106 and 121):
- `szemeredi_trotter`: I(P,L) ≤ C·(n^{2/3}·m^{2/3} + n + m) [stays as axiom — deep result]
- `kRich_bound`: numKRichLines ≤ C·n²/k³ for k² ≤ n [derivable by counting + algebra]

The derivation is:
1. **mk ≤ I(P,L)**: each of m k-rich lines contributes ≥ k incidences
2. Apply Szemerédi-Trotter: I(P,L) ≤ C·szTrBound(n, |L|) ≤ C·szTrBound(n, m + ...)
3. Algebra: mk ≤ C(n^{2/3}m^{2/3} + n + m) + k² ≤ n → m ≤ C'n²/k³

---

## Insights

### Lean File Structure (from source inspection)

**Definitions** (lines 37–98):
- `pointsOnLine P l = P.filter (fun p => decide (l.a * p.1 + l.b * p.2 = l.c))`
- `incidenceCount P l = (pointsOnLine P l).card`
- `totalIncidences P L = L.sum (fun l => incidenceCount P l)`
- `kRichLines P L k = L.filter (fun l => decide (incidenceCount P l ≥ k))`
- `numKRichLines P L k = (kRichLines P L k).card`

### Key Sub-lemma for the Derivation

```
kRich_incidences_lower:
  numKRichLines P L k * k ≤ totalIncidences P L
```

Proof sketch:
- `kRichLines P L k ⊆ L` → `totalIncidences P (kRichLines P L k) ≤ totalIncidences P L`
- Each l ∈ kRichLines has incidenceCount ≥ k, so sum ≥ card * k
- Mathlib: `Finset.card_mul_le_sum_of_ge` or similar

### Algebraic Step (on paper, needs Lean)

Given mk ≤ C(n^{2/3}·m^{2/3} + n + m) and k² ≤ n, k ≥ 2:
- Case A: mk ≤ 2C·n^{2/3}·m^{2/3} → m^{1/3} ≤ 2Cn^{2/3}/k → m ≤ (2C)³·n²/k³
- Case B: mk ≤ 2C(n + m) → m(k-2C) ≤ 2Cn → m ≤ 2Cn/(k-2C) ≤ C''n²/k³

### Technical Notes

- `decide` on `ℝ` equality works via `Classical.decProp` (classical logic in Lean4)
- Need `Real.rpow` lemmas for the 2/3 power manipulation
- `Finset.sum_le_sum_of_subset` handles kRichLines ⊆ L
- Coercions: use `Nat.cast_le`, `push_cast` tactic

---

## Dead Ends

[None yet]
