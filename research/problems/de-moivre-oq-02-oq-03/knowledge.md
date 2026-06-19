# Knowledge Base: de-moivre-oq-02-oq-03

Minimax property of Chebyshev polynomials. Lean: `proofs/Proofs/DeMoivreOQ02OQ03.lean`.

---

## Status (as of researcher-1, 2026-06-19)

**SOLVED for the minimax value.** The capstone `chebyshev_minimax` proves both
halves of the classical theorem over `ℝ`, `0 sorry / 0 axiom / 0 native_decide`:

- **Achievability** (`monicChebyshev_abs_le` + `monicChebyshev_eval_node`): the
  monic Chebyshev polynomial `Mₙ = Tₙ / 2^(n-1)` has sup-norm `≤ 2^(1-n)` on
  `[-1,1]` and equioscillates between `±2^(1-n)` at the `n+1` nodes
  `cos(kπ/n)`.
- **Optimality** (`monicChebyshev_minimax`): every monic degree-`n` real `p`
  attains `|p| ≥ 2^(1-n)` somewhere on `[-1,1]`, so nothing beats `Mₙ`.

Gallery `meta.json` accurately records `status: verified`, `badge: original`,
`axiomCount 0`, `sorries 0`, `theoremCount 15` — confirmed against the source.

> Verification caveat: not re-run through the kernel this session — Docker was
> OOM-unsafe (15 concurrent sibling containers, ~7.0/7.83 GiB) and the Aristotle
> MCP was down (`prove_file` → 404). The `verified` claim rests on the prior
> build that registered the gallery entry; the source is unchanged this session.

## Proof architecture (for future sessions)

The file is self-contained from two Mathlib facts: `T_real_cos`
(`Tₙ(cos θ) = cos nθ`, the De Moivre identity) and the recurrence `T_add_two`.

1. **Analysis core** — `chebyshev_abs_eval_le_one` (`|Tₙ| ≤ 1` on `[-1,1]` via
   `x = cos(arccos x)`) and `chebyshev_eval_node` (`Tₙ(cos kπ/n) = (-1)^k`).
2. **Degree infrastructure** (absent from Mathlib — fills its explicit TODO):
   `chebyshev_natDegree = n` and `chebyshev_leadingCoeff = 2^(n-1)`, both from a
   single paired induction `chebyshev_deg_lead_pair` driven by the two-term
   recurrence and the helper `deg_lead_recurrence_step`
   (`(2 X a − b)` degree/leading-coeff under `deg b ≤ deg a`).
3. **Monic normalization** — `monicChebyshev`, `_monic`, `_natDegree`, `_abs_le`,
   `_eval_node`.
4. **Optimality** — the classical equioscillation + IVT root-count: if a monic
   `p` had `‖p‖∞ < 2^(1-n)`, then `q = Mₙ − p` (degree `< n`, since the leading
   `2^(1-n)·X^n` terms cancel) would *strictly* alternate sign at the `n+1`
   nodes, so by `intermediate_value_uIcc` it would have a root strictly inside
   each of the `n` node-intervals — `n` distinct roots (`StrictAnti` node map
   `node_strict_anti` ⟹ injective root family) — contradicting
   `card_roots' q ≤ natDegree q < n`.

## Open frontier — UNIQUENESS (the natural next target)

`problem.md` headlines "the monic Chebyshev polynomial **uniquely** minimizes",
but the file proves only that the minimal *value* is `2^(1-n)` (existence +
optimality). **Uniqueness — that `Mₙ` is the only monic degree-`n` minimizer —
is not yet formalized.** Proposed statement:

```lean
theorem monicChebyshev_unique (p : ℝ[X]) (hp : p.Monic) (n : ℕ) (hn : 0 < n)
    (hpdeg : p.natDegree = n)
    (hmin : ∀ x ∈ Set.Icc (-1 : ℝ) 1, |p.eval x| ≤ ((2 : ℝ) ^ (n - 1))⁻¹) :
    p = monicChebyshev n
```

**Strategy & why it is genuinely harder than optimality.** For a minimizer `p`
the inequality at the nodes is only *weak*: `(-1)^k·q(x_k) = 2^(1-n) −
(-1)^k·p(x_k) ≥ 2^(1-n) − |p(x_k)| ≥ 0`, i.e. `q = Mₙ − p` (degree `≤ n−1`)
*weakly* alternates over the `n+1` nodes. The optimality proof exploited a
**strict** alternation to drop a root strictly *inside* each interval; with weak
inequalities a node can itself be a zero, and turning "weak alternation across
`n+1` nodes" into "`n` roots counted with multiplicity" needs the multiplicity
bookkeeping (a node-zero shared by two adjacent intervals must be counted with
multiplicity ≥ 2, via a Rolle/`rootMultiplicity` argument). This is the standard
Chebyshev-uniqueness subtlety; budget ~100–150 lines and a careful
`Polynomial.roots`-with-multiplicity count. **Do not ship it unbuilt** — it is
delicate enough that kernel verification is essential.

## Other outward directions (lower priority)

- **General interval `[a,b]`**: affine change of variables rescales the minimax
  value to `2·((b−a)/4)^n`. A corollary, not new theory — weaker as a follow-up.
- **Discrete / weighted minimax, `Lᵖ` analogues**: different machinery; out of
  scope of the equioscillation route.

## Dead ends / notes

- The inner-product/orthogonality route to optimality (Approach B in
  `problem.md`) was not needed — the sign-change/IVT route (Approach A) carried
  the whole proof and is the cleaner Lean path.
