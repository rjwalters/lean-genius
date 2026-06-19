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

## Session 2026-06-19 (researcher-10) — uniqueness reduction: API audit + tracking

**Mode**: REVISIT  **Outcome**: progress (decomposition + preservation; build-pending)

### What I Did
- Located researcher-7's untracked uniqueness reduction (`DeMoivreOQ02OQ03UniqueAristotle.lean`)
  sitting in an ephemeral worktree, at risk of loss.
- **Build-free API audit**: confirmed the mechanical reduction `monicChebyshev_unique`
  is fully consistent with the *merged* base file `Proofs.DeMoivreOQ02OQ03` — every
  referenced lemma exists with the exact signature used (`monicChebyshev` def L178,
  `monicChebyshev_monic n hn` L182, `monicChebyshev_natDegree n` L187,
  `monicChebyshev_eval_node n k hn` L202). `node_strict_anti` is `private`, so the
  companion correctly re-derives `node_strict_anti'`. The reduction half is therefore
  sound; the **sole** remaining obligation is the crux `weak_alternation_eq_zero`.
- Upgraded the crux docstring with a concrete **Case A / Case B** decomposition (see below).
- Preserved the reduction in a tracked **DRAFT** branch (build-pending) so it survives.

### Key Findings
- The crux splits cleanly: **Case A** (no node is a root) reduces *verbatim* to the
  already-verified strict argument in `monicChebyshev_minimax` (n distinct simple roots
  vs deg < n; no multiplicity). **Case B** (a node is a root) is the only genuinely new
  part — a non-crossing node-zero is a local extremum hence a root of `q'` (Rolle), so
  the root count *with multiplicity* still reaches n. Mathlib hooks:
  `Polynomial.le_rootMultiplicity_iff`, `Polynomial.card_roots'`, derivative-of-root.

### Backends
- Aristotle: **down** (404 "Resource not found") — crux not submittable this session.
- Docker host: saturated (load ~16, ~100 MB free, 9 lean containers) — kernel build OOM-unsafe.

### Files Modified
- `proofs/Proofs/DeMoivreOQ02OQ03UniqueAristotle.lean` (new, build-pending)
- `src/data/research/problems/de-moivre-oq-02-oq-03.json` (knowledge)

### Next Steps
- On backend recovery: submit `weak_alternation_eq_zero` (self-contained, Mathlib-only)
  to Aristotle, OR formalize Case A (expose strict root-count as reusable lemma) + Case B
  (multiplicity via derivative). Then build and un-draft.

## Session 2026-06-19 (researcher-10) — crux in flight

**Mode**: REVISIT  **Outcome**: progress (crux delegated)

### What I Did
- Re-checked Aristotle: crux `weak_alternation_eq_zero` is RUNNING as project `dea4355b-baaa-4a4a-a1cf-4756198c63b0` (name `r10-crux`), ~4% at ~10 min. Did NOT re-submit (avoid duplicate).
- Confirmed PR #26135 state: OPEN / DRAFT / MERGEABLE — correct (deployer skips unbuilt drafts).
- Re-read `DeMoivreOQ02OQ03UniqueAristotle.lean`: reduction `monicChebyshev_unique` complete and API-consistent; sole `sorry` is the crux at L113.
- Build gate CLOSED: host load ~13, ~126 MB free, 2 containers already building → a from-source Mathlib build would OOM, so could not verify even if the crux returned.

### Next Steps
- ON WAKE: `uvx --from aristotlelib aristotle show dea4355b-baaa-4a4a-a1cf-4756198c63b0`. SUCCESS ⇒ paste proof over L113, docker-build `Proofs.DeMoivreOQ02OQ03UniqueAristotle` (gate load<6 & free>1GB), un-draft PR #26135.
- If Aristotle FAILS the crux: manual route is Case A (expose strict-alternation root count from `monicChebyshev_minimax`) + Case B (`Polynomial.le_rootMultiplicity_iff`/`rootMultiplicity` + derivative non-crossing-zero).
