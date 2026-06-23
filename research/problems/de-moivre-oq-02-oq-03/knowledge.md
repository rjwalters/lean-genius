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

### Update (researcher-7, 2026-06-19, cycle 4) — Lagrange-route API CONFIRMED against Mathlib v4.26.0

Backends still down this cycle (Aristotle MCP `prove` → `Resource not found`/404; the worktree
docker build re-clones Mathlib from source → OOM at the 12 GB cap, so it is unsafe to raise the
limit — the from-source Mathlib build is exactly the trap CLAUDE.md forbids). No `.lean` shipped.
Instead, every API name in the Lagrange route above was checked directly against the local
Mathlib source (`proofs/.lake/packages/mathlib/Mathlib/...`). All five exist; **two refinements**:

- `Lagrange.eq_interpolate` — `Mathlib/LinearAlgebra/Lagrange.lean:362`:
  `{f : F[X]} (hvs : Set.InjOn v s) (degree_f_lt : f.degree < #s) : f = interpolate s v (fun i => f.eval (v i))`.
  Uses `f.degree` (`WithBot`) `< #s`, so feed `q.degree < n+1` (from `natDegree q < n`; handle `q=0` first).
- `Lagrange.interpolate` is `@[simps]` (`:299`), so `interpolate_apply` rewrites it to
  `∑ i ∈ s, C (r i) * Lagrange.basis s v i`.
- **REFINEMENT 1 — the divided-difference coefficient identity is NOT a named lemma; derive it inline.**
  Copy the recipe used inside Mathlib's own `leadingCoeff`-of-interpolant proof
  (`Lagrange.lean:481-486`): after `interpolate_apply`, apply `finset_sum_coeff`
  (`Mathlib/Algebra/Polynomial/Coeff.lean:89`), then per term `coeff_C_mul`, then rewrite
  `coeff n (basis ..) = leadingCoeff (basis ..)` using `← natDegree_basis hvs hi`
  (`Lagrange.lean:241`, gives `natDegree (basis) = #s − 1 = n`) and `← leadingCoeff`, then
  `leadingCoeff_basis hvs hi` (`Lagrange.lean:279`):
  `(Lagrange.basis s v i).leadingCoeff = (∏ j ∈ s.erase i, (v i − v j))⁻¹`. Net:
  `coeff n (interpolate s x (fun i => q.eval (x i))) = ∑ i ∈ s, q.eval (x i) · (∏ j ∈ s.erase i, (x i − x j))⁻¹`.
- `Finset.sum_eq_zero_iff_of_nonneg` — confirmed (used widely, e.g. `Analysis/Convex/Combination.lean:199`):
  `(∀ i ∈ s, 0 ≤ f i) → (∑ i ∈ s, f i = 0 ↔ ∀ i ∈ s, f i = 0)`.
- **REFINEMENT 2 — the finisher takes a `Finset ℝ` of distinct roots directly** (no `Fintype`/range plumbing):
  `Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero'` (`Mathlib/Algebra/Polynomial/Roots.lean:662`):
  `(p : R[X]) (s : Finset R) (heval : ∀ i ∈ s, p.eval i = 0) (hcard : natDegree p < #s) : p = 0`
  `[CommRing R] [IsDomain R]` — so pass `s := (Finset.range (n+1)).image x` (card `n+1` by injectivity
  from strict antitonicity), `heval` from the per-node `q.eval (x k) = 0`, and `natDegree q < n < n+1 = #s`.

Net effect: the crux is now a fully API-pinned ~30–50 line proof with no unverified lemma names.
This is the first-try recipe for the next Aristotle/build session (or a hand proof once a build host frees up).

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

---

## Session 2026-06-19 (researcher-7) — CRUX DISCHARGED, 0 sorry

**Mode**: REVISIT  **Outcome**: progress (crux proved; local v4.26 build pending)

### What I Did
- Aristotle project `3b070308` ("r7-demoivre-crux") returned **COMPLETE**: proved `node_divdiff_sign` by partitioning `(range (n+1)).erase i` into `range i` (factors `j<i`, negative) and `Ioc i n` (factors `j>i`, positive); the product has sign `(-1)^i` via `Finset.prod_pos`. Aristotle's whole Crux.lean builds with **no sorry**, axioms = `propext`/`Classical.choice`/`Quot.sound` only.
- Retrieved via `aristotle download 3b070308 --destination FILE.zip` (tar.gz) and integrated the **build-verified pair** — product-form `node_divdiff_sign` + `weak_alternation_eq_zero` (Lagrange `eq_interpolate` + `leadingCoeff_basis` + `eq_zero_of_natDegree_lt_card_of_eval_eq_zero'`) — into `DeMoivreOQ02OQ03UniqueAristotle.lean`. Kept `monicChebyshev_unique` + `node_strict_anti'` (the `weak_alternation_eq_zero` signature is identical, so the wrapper still type-checks).
- File now **0 sorry**. Committed `845e7b667c3`, pushed to update PR #26135 (kept DRAFT pending local build).

### Key Findings
- Toolchain artifact: Aristotle verified under `v4.28.0`; repo pins `v4.26.0`. Only flagged delta was `hni : n = s.card - 1` (`rw [hcard]; omega` is v4.28-only — under v4.26 `rw` auto-closes and `omega` would error). Closed with `by omega` (uses `hcard` in context; robust under both). Did not touch repo lean-toolchain.
- Nesting Aristotle's standalone lemma would change its `simp_all` context — kept `node_divdiff_sign` a separate namespace-level lemma with Aristotle's exact clean signature.

### Files Modified
- `proofs/Proofs/DeMoivreOQ02OQ03UniqueAristotle.lean` (0 sorry)
- `src/data/research/problems/de-moivre-oq-02-oq-03.json` (knowledge)

### Next Steps
- ON WAKE: check background build waiter `b33u7fbco` (log `/tmp/r7-demoivre-build.log`). `BUILD EXIT rc=0` ⇒ `gh pr ready 26135`, mark status verified, graduate pool (FORCE_COMPLETE=1; graduation reads MAIN problem json so needs the merge first). rc≠0 ⇒ fix the v4.26 error (likely `open Real`/`Polynomial.Chebyshev` name clash or `simp_all +decide` drift in the integrated lemmas) and rebuild.
