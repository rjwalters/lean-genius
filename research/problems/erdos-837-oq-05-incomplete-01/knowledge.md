# erdos-837-oq-05-incomplete-01 — Complete proof of Hypergraph Density Jumps: Liminf Formulation

## Status: COMPLETED (sorry eliminated)

The task was to complete the proof in `Erdos837ProblemOQ05.lean`, which carried
1 `sorry` (`zero_is_jump`) and 1 axiom (`erdos_stone_simonovits`).

## What was done (session 2026-06-28, researcher-1)

1. **Eliminated the `sorry` in `zero_is_jump`** — `0 ∈ A_k` for `k ≥ 2` is now
   fully proved (counting model), no `sorry`. `#print axioms zero_is_jump`
   reports only `propext / Classical.choice / Quot.sound`. The result is
   independent of the `erdos_stone_simonovits` axiom.

2. **Construction (β = 1 witness).** Given a sequence `Gₙ` with `(Gₙ).uniformity = k`,
   diverging vertex count, and `0 < L = liminf (edgeDensity ∘ G)`:
   - `eventually_lt_of_lt_liminf` (with `IsBoundedUnder (·≥·)` from
     `edgeDensity ≥ 0`) gives eventually `c < edgeDensity (Gₙ)` for `c = L/2 > 0`.
   - On those `n`, `c · C(|Gₙ|,k) < e(Gₙ)` (unfold `edgeDensity`, kill the
     `if`-branch via positivity).
   - `choose_tendsto_atTop`: `C(m,k) → ∞` (proved via `Nat.pow_le_choose`
     lower bound `(m+1-k)^k/k! ≤ C(m,k)` squeezed by `tendsto_atTop_mono'`).
   - Hence `c · C(|Gₙ|,k) → ∞`, so by `tendsto_atTop_mono'`, `e(Gₙ) → ∞`.
   - Take `Hₙ = ⟨vₙ, C(vₙ,k), k⟩` with
     `vₙ = Nat.findGreatest (fun w => C(w,k) ≤ e(Gₙ)) |Gₙ|`. Then
     `C(vₙ,k) ≤ e(Gₙ)` (`findGreatest_spec` with witness `w=0`, since
     `C(0,k)=0` for `k≥1`), `vₙ ≤ |Gₙ|` (`findGreatest_le`), `vₙ → ∞`
     (`le_findGreatest`, needing both `|Gₙ| ≥ M` and `e(Gₙ) ≥ C(M,k)`), and
     `edgeDensity Hₙ = 1` once `vₙ ≥ k` (so `C(vₙ,k) ≠ 0`, `div_self`).
     `liminf_congr + liminf_const` finishes `1 ≤ liminf (edgeDensity ∘ H)`.

3. **Fixed a parse-error bug in the parent `Erdos837Problem.lean`.** Four
   floating `/-- … -/` doc comments (not attached to any declaration) were
   parse errors in Lean v4.26 — the parent (and therefore the whole entry)
   did NOT compile. Converted them to plain `/- … -/` block comments. This
   was identical on `origin/main`, so the "verified" parent was silently broken.

4. **Import fix.** `Mathlib.Topology.Instances.Real` is no longer a module
   olean in Mathlib v4.26 (it became a directory). Switched the child's import
   block to `import Mathlib` (+ `Proofs.Erdos837Problem`).

## Remaining
- 1 axiom: `erdos_stone_simonovits` (deep ESS A_2 characterization) — left as a
  legitimate axiomatized input; not provable from current Mathlib.
- The counting model (`KUniformHypergraph` = vertex/edge counts) is a toy model;
  `zero_is_jump` is real supersaturation only relative to it. A genuine
  formalization would use typed hypergraph structures.

## Key Mathlib API used
`Nat.findGreatest_spec`, `Nat.le_findGreatest`, `Nat.findGreatest_le`,
`Nat.pow_le_choose`, `tendsto_pow_atTop`, `Tendsto.atTop_div_const`,
`Tendsto.const_mul_atTop`, `tendsto_atTop_mono'`, `eventually_lt_of_lt_liminf`,
`isBoundedUnder_of`, `liminf_congr`, `liminf_const`, `tendsto_natCast_atTop_atTop`.
