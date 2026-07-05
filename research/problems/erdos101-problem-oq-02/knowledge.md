# erdos101-problem-oq-02 — Elementary incidence bound (toward Szemerédi–Trotter)

**Parent**: Erdős Problem #101 (four-point lines from planar point sets).
**OQ-02 statement (pool)**: "Formalize the Szemerédi–Trotter bound
`I(P,L) ≤ C(|P|^{2/3}|L|^{2/3} + |P| + |L|)`."

**Status**: COMPLETED (verified, 0 sorries, 0 axioms) — for the *elementary
predecessor* of ST. The full ST bound remains open (see next steps).

## Summary

The full Szemerédi–Trotter theorem needs the crossing-number inequality (Székely)
or a cell decomposition — substantial machinery not attempted here. This session
formalised the rigorous **elementary Cauchy–Schwarz incidence bound**, the classical
weaker bound that ST improves:

For any incidence system (arbitrary point/line types + incidence relation `Inc`)
satisfying the **linear-space axiom** (two distinct points lie on ≤ 1 common line),
with `r ℓ = |{p ∈ P : Inc p ℓ}|` and `I = Σ_ℓ r ℓ`:

```
incidences_sq_le :  I² ≤ |L| · (|P|² + I)
```

Over ℝ this is `I ≤ |P|·√|L| + |L|`. ST sharpens the RHS to `|P|^{2/3}|L|^{2/3}`.

## Session 2026-07-04 (Session 1) — FRESH

**Mode**: FRESH. **Outcome**: completed (elementary bound).

### What I Did
- Confirmed `erdos101-problem-oq-02` is a *distinct* open question from the existing
  `erdos-101-oq-02` entry (Steiner systems). No duplicate; no prior meta.json.
- Wrote `proofs/Proofs/Erdos101ProblemOQ02.lean` (183 lines, 0 sorry, 0 axiom).
- Docker-verified: `#print axioms incidences_sq_le` → `[propext, Classical.choice, Quot.sound]`.
- Added gallery entry `src/data/proofs/erdos101-problem-oq-02/` (meta.json + annotations.json).

### Key Findings / Techniques
- **Double counting as an injection out of a sigma type**: `Σ_ℓ C(r_ℓ,2)` is the
  card of `L.sigma (fun ℓ => (pointsOn ℓ).powersetCard 2)`; projecting `(ℓ,e) ↦ e`
  into `P.powersetCard 2` is injective by the linear-space axiom. Closed with
  `Finset.card_le_card_of_injOn`.
- **Square/triangular identity** `n² = n + 2·C(n,2)` converts the pair count into a
  sum of squares (the shape Cauchy–Schwarz consumes).
- **ℕ Cauchy–Schwarz** `(Σf)² ≤ |s|·Σf²` obtained by casting `Finset.sum_mul_sq_le_sq_mul_sq`
  (ℝ) with `g ≡ 1` back to ℕ via `push_cast` / `Nat.cast_le`. Keeps the headline in ℕ,
  avoiding square roots entirely.

### Lean gotchas hit
- `Finset.mem_sigma` and `Finset.mem_powersetCard` do NOT fire under `simp only`/`rw`
  on membership coming from `Finset.card_le_card_of_injOn` (Set-coe `∈ ↑s`, and beta-redex
  under `Sigma.snd`). Use the `.mp`/`.mpr` projections instead — they succeed by defeq.
- `Nat.choose_succ_succ` leaves `k.choose (Nat.succ 1)`; close with `show ... k.choose 2 ...; omega`.
- Docker build intermittently exits 135 (SIGBUS, environmental) right after cache
  decompression — just retry; the `#print axioms` output confirmed on a clean run.

### Files Modified
- `proofs/Proofs/Erdos101ProblemOQ02.lean` (new)
- `src/data/proofs/erdos101-problem-oq-02/meta.json` (new)
- `src/data/proofs/erdos101-problem-oq-02/annotations.json` (new)

### Next Steps (toward the full ST bound — genuinely harder)
- Formalise Székely's crossing-number proof of ST: needs the crossing-number
  inequality `cr(G) ≥ e³/(64 v²)` for `e ≥ 4v`, itself from Euler's formula +
  probabilistic deletion. This is the real open work; likely > 1000 lines.
- Alternatively, a cell-decomposition / polynomial-partitioning route.
- Sharpness of the elementary bound: exhibit a finite projective plane attaining
  `I² ≈ |L|(|P|² + I)`, showing Cauchy–Schwarz alone cannot beat the √ exponent.
