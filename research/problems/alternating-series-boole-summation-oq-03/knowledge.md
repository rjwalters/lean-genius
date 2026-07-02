# alternating-series-boole-summation-oq-03 — Alternating sum of a quadratic in closed form

**Parent:** `alternating-series-boole-summation` — verified, 0-axiom (finite Boole summation engine).

**Open question (degree-2 rung of the polynomial ladder):** The parent's `altSum_affine` gives the
alternating sum of an affine sequence `a_j = α + β·j` as a pure endpoint expression because
`Δ²(α+βj) ≡ 0` terminates the order-2 Boole formula. Does the degree-2 case — a quadratic
`a_j = α + β·j + γ·j²` — likewise close exactly, via `Δ³ ≡ 0` and the order-3 formula?

## Answer: YES

`proofs/Proofs/AlternatingSeriesBooleSummationOQ03.lean` proves the exact closed form

    ∑_{j=n}^{m-1} (-1)^j (α + βj + γj²)
        = ½·((-1)^n a_n − (-1)^m a_m)
          − ¼·((-1)^n (Δa)_n − (-1)^m (Δa)_m)
          + ¼·γ·((-1)^n − (-1)^m),

with Δa_j = (β+γ)+2γ·j, plus a worked corollary for ∑ (-1)^j j².

## Results (5 theorems, 0 sorry, 0 axiom)
- `fdiff_quadratic`                — Δ(α+βj+γj²) = (β+γ)+2γ·j  (affine first difference)
- `fdiff_two_quadratic`            — Δ²(quadratic) = 2γ (constant), via parent `fdiff_affine`
- `iterate_fdiff_three_quadratic`  — Δ³(quadratic) ≡ 0
- `altSum_quadratic`               — the exact endpoint closed form (order-3 Boole termination)
- `altSum_sq`                      — ∑ (-1)^j j² closed form (α=β=0, γ=1 specialization)

## Proof architecture
Pure reuse of the verified parent engine. The three finite-difference lemmas feed a vanishing
`Δ³a ≡ 0` into the parent's `boole_exact_of_iterate_fdiff_zero` at order K=3, which drops the
remainder alternating sum; the length-3 Boole sum is unfolded with `Finset.sum_range_succ`/`_one`,
the difference terms substituted via the `fdiff` lemmas, and `push_cast; ring` closes the endpoint
algebra. `fdiff_two_quadratic` applies the parent's `fdiff_affine` to the affine first difference
(no recomputation).

## Gotcha (worth remembering)
The RHS of `fdiff_quadratic` must annotate its binder as `fun (j : ℕ) => …`. Written as
`fun j => … (j : ℝ) …`, Lean reads the `(j : ℝ)` cast as a type *ascription* on the unconstrained
binder and infers `j : ℝ`, producing an `ℝ → ℝ` function that mismatches `fdiff`'s `ℕ → ℝ` domain.
The LHS lambda escapes this because `fdiff` constrains its argument to `ℕ → ℝ`. This one type
mismatch initially cascaded into `sorry` across every downstream theorem.

## Build & axiom verification (researcher-11, 2026-07-02)
- **Build VERIFIED**: `./proofs/scripts/docker-build.sh Proofs.AlternatingSeriesBooleSummationOQ03`
  → `=== Build succeeded ===`, exit 0, zero warnings (no `sorry`/unreachable-tactic).
- **`#print axioms` (all 5 theorems)**: `[propext, Classical.choice, Quot.sound]` only — no
  `sorryAx`, no `Lean.ofReduceBool`, no `native_decide`. Genuine **verified, 0-axiom**.
- Gallery entry created: `src/data/proofs/alternating-series-boole-summation-oq-03/{meta.json,annotations.json}`
  (status `verified`, badge `verified`, axiomCount 0, 5 theorems, 105 lines). listings.json /
  data-manifest.json are gitignored build artifacts (regenerated at deploy) — not committed.

Pool candidate → `completed`.

## Follow-on open questions (recorded in meta.conclusion)
1. Uniform `altSum_polynomial`: arbitrary degree-d polynomial alternating sum from a vanishing
   `Δ^{d+1}` hypothesis (generalize this ladder in one theorem).
2. Relate the collected endpoint coefficients (½, ¼, ⅛, …) to Euler polynomials / Euler numbers
   (ties back to parent OQ-02).
