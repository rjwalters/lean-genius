# algebraic-numbers-countable-oq-05-oq-01 — Explicit height enumeration

**Question.** Can we make Cantor's height enumeration *explicit* — a computable bijection
`ℕ ↔ (real algebraic numbers)` driven by the height function
`H(p) = deg p + Σ|coeff|` on `ℤ[X]`?

## Session 1 (researcher-14, 2026-07-03) — phase NEW → ACT, verified quantitative step

### What already exists (parent `AlgebraicNumbersCountableOQ05`)
The parent proves each height stratum is **finite** (`finite_polys_of_height`) and
`algebraic_reals_countable_via_height`, but only *abstractly* (finiteness as the range of a
reconstruction map). It does **not** give a size bound — which an explicit, terminating
enumeration needs.

### Contribution (new file `Proofs/AlgebraicNumbersCountableOQ05OQ01.lean`, 0 sorry/0 axiom)
Supplied the first **quantitative** ingredient: an explicit closed-form bound on the
stratum size at the polynomial level.
- `encHeight` — explicit injection of `{p // cantorHeight p ≤ h}` into the finite grid
  `Fin (h+1) → Fin (2h+1)`, via `c ↦ (c + h).toNat` (well-defined since `|c| ≤ h`).
- `encHeight_injective` — a height-`≤h` polynomial is determined by its first `h+1`
  coefficients (higher ones vanish, degree `≤ h`) and the shift is injective on `{-h,…,h}`.
- `ncard_boundedHeight_le` — **`#{p : cantorHeight p ≤ h} ≤ (2h+1)^(h+1)`**. The stratum-`h`
  search terminates after inspecting at most `(2h+1)^(h+1)` candidate polynomials.

Reuses the parent's `cantorHeight_coeff_le` / `cantorHeight_degree_le` via `import`.

### Next steps (remaining open work)
1. Push the bound to *algebraic reals*: `#(algebraicRealsOfHeight ≤ h) ≤ h·(2h+1)^(h+1)`
   (each polynomial contributes `≤ deg ≤ h` real roots — combine with parent
   `finite_real_roots`). Gives an explicit per-height count.
2. Assemble the strata in height order and deduplicate the (shared) roots to get an explicit
   monotone `ℕ → algebraic reals`; injectivity/surjectivity via the union decomposition
   `algebraic_reals_eq_iUnion_height`.
3. Package as a `Denumerable`/computable `Equiv` — the full explicit bijection.

### Gotchas
- `encHeight` must be defined on the *subtype* `{p // cantorHeight p ≤ h}` (the `Fin (2h+1)`
  codomain proof needs `|coeff| ≤ h`); a total `Polynomial ℤ → …` version does not typecheck.
- In `encHeight_injective`, use `intro x y` + `simp only [encHeight]` (NOT `rintro ⟨p,hp⟩` +
  `dsimp`): destructuring leaves `(↑⟨p,hp⟩).coeff` as a distinct atom from `p.coeff`, so
  `omega` sees two unrelated variables and fails.
- `Set.Nat.card_coe_set_eq` is deprecated → use `Nat.card_coe_set_eq`.
