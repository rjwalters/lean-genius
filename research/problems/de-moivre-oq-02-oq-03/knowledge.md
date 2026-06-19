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

> **Kernel-verified 2026-06-19 (researcher-1).** Re-built clean through Docker:
> `Proofs.DeMoivreOQ02OQ03` → "Build completed successfully (7743 jobs)", exit 0,
> against the live Mathlib cache (`lake exe cache get`, 7727 oleans). The earlier
> "not re-run this session" caveat is now resolved — the `verified` /
> `axiomCount 0` / `sorries 0` gallery claim holds against current Mathlib.
> Static check on the source confirms 0 `sorry`, 0 `^axiom `, 0 `native_decide`
> (hence no `Lean.ofReduceBool`); the `verified` badge is honest.

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

### Isolated crux (ready for Aristotle the moment the MCP is back up)

The whole uniqueness theorem reduces — by the mechanical node setup mirroring
`monicChebyshev_minimax` (set `q = Mₙ − p`, evaluate `(-1)^k q(x_k) ≥ 0` at the
`n+1` nodes via `monicChebyshev_eval_node`, then `q = 0 ⟹ p = Mₙ` since
`degree_sub_lt` gives `deg q < n`) — to this **self-contained, Chebyshev-free**
lemma. State it in a `*Aristotle.lean` companion importing `Mathlib` and submit
via `mcp__aristotle__prove_file`:

```lean
/-- Weak Chebyshev alternation forces the zero polynomial: a real polynomial of
degree `< n` that weakly alternates in sign at `n+1` strictly decreasing reals
must be `0`. -/
theorem weak_cheb_alternation_zero
    (n : ℕ) (hn : 0 < n) (q : ℝ[X]) (hdeg : q.natDegree < n)
    (t : ℕ → ℝ)
    (hdec : ∀ i j, i < j → j ≤ n → t j < t i)
    (halt : ∀ k, k ≤ n → 0 ≤ (-1 : ℝ) ^ k * q.eval (t k)) :
    q = 0
```

Truth-checked by hand at `n = 1` (`q` const `c`: `0 ≤ c` and `0 ≤ -c ⟹ c = 0`)
and `n = 2,3`. The hard content is the multiplicity count: with strict
alternation IVT drops one interior root per interval (`n` distinct, as in
optimality), but the weak `≥ 0` lets a node be a zero shared by two adjacent
sign-intervals, which must then carry multiplicity `≥ 2`. Mathlib has no packaged
"root at a non-sign-changing point ⟹ even multiplicity" lemma, so a manual
proof needs `Polynomial.rootMultiplicity` / `le_rootMultiplicity_iff`
(`(X-a)^2 ∣ q`) bookkeeping plus `Polynomial.card_roots'`
(`Multiset.card q.roots ≤ q.natDegree`) — this is exactly the delicate step to
hand to Aristotle rather than write blind.

**Session status 2026-06-19 (researcher-1):** Aristotle MCP still down
(`prove_file` → `{"status":"error","message":"Resource not found."}` / 404), so
the crux was *not* submitted; staged here verbatim for the next backend-up
session. Docker, by contrast, is back (used it to kernel-verify the value half
above), so once Aristotle returns the crux proof, integrate into the gallery
file and re-build to confirm before flipping any status.

## Other outward directions (lower priority)

- **General interval `[a,b]`**: affine change of variables rescales the minimax
  value to `2·((b−a)/4)^n`. A corollary, not new theory — weaker as a follow-up.
- **Discrete / weighted minimax, `Lᵖ` analogues**: different machinery; out of
  scope of the equioscillation route.

## Dead ends / notes

- The inner-product/orthogonality route to optimality (Approach B in
  `problem.md`) was not needed — the sign-change/IVT route (Approach A) carried
  the whole proof and is the cleaner Lean path.
