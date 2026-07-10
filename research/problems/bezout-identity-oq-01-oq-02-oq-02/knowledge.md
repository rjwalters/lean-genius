# Knowledge Base: bezout-identity-oq-01-oq-02-oq-02

Insights accumulated during research on this problem.

---

## Problem Understanding

[Initial observations about the problem will be recorded here]

---

## Insights

[Insights from research attempts will be accumulated here]

---

## Dead Ends

[Approaches known not to work will be documented here]

---

## Module map (two complementary formalizations on `main`)

- `BezoutIdentityOQ01OQ02OQ02.lean` (namespace `BezoutPrimitive`, landed by a competing PR):
  the **necessity half** — `IsPrimitive` via `w ⬝ᵥ v = 1`, transvection generators
  (`transvectionSL`), primitivity preserved under `SLₙ`, and `orbit_e_isPrimitive` (every orbit
  element of a basis vector is primitive). Explicitly leaves the converse (sufficiency) open as
  "the remaining Euclidean-descent construction".
- `BezoutIdentityOQ01OQ02OQ02Descent.lean` (namespace `BezoutDescent`, this work): the
  **constructive sufficiency descent** the companion leaves open — a block-embedding reduction
  engine + verified base cases.

## Session 2026-07-09 — constructive descent engine (`BezoutDescent`)

**Outcome**: engine + verified n=2,3 + general head block; audit-clean, docker-verification BLOCKED.

### Decls (0 sorry / 0 axiom)
- `embedOne` : `SLₙ ↪ SL₍ₙ₊₁₎`, `M ↦ diag(1,M)` (tail reducer) with `det_embedOne`,
  `embedOne_mulVec` (`diag(1,M) ·ᵥ (a ::ᵥ w) = a ::ᵥ (M ·ᵥ w)`), `embedOneSL`.
- `sl2_transitive` (base, from grandparent `bezoutSL`); `headBlock3` + `sl3_transitive`
  (first genuinely-new case: primitive `(a,b,c) → (1,0,0)` by `embedOne T` then head Bézout block).
- **General head block** (this session's addition): `headBlockN {m} N := (fromBlocks N 0 0 1).submatrix
  finSumFinEquiv.symm finSumFinEquiv.symm` = `diag(N, Iₘ) ∈ M_{2+m}`, generalizing `headBlock3`
  (= m=1); `det_headBlockN`; `headBlockN_mulVec` (`diag(N,Iₘ) ·ᵥ (u ++ w) = (N·ᵥu) ++ w`, Fin.append
  split); `headBlockNSL`. Paired with `embedOne` this supplies BOTH reduction steps of the general
  induction.

### Gotchas
- `det_headBlockN`: DON'T `rw [headBlockN, det_submatrix_equiv_self, …]` (fails → cascades
  "unknown identifier `det_headBlockN`" downstream since the failed decl never registers). DO apply
  `Matrix.det_submatrix_equiv_self finSumFinEquiv.symm _` as a term in a `have` (typechecks up to
  defeq), then `det_fromBlocks_zero₂₁ → det_one → mul_one`.
- `headBlockN_mulVec` recipe: `rw [headBlockN, submatrix_mulVec_equiv]`; rewrite
  `Fin.append u w ∘ ⇑finSumFinEquiv = Sum.elim u w` via `Equiv.symm_symm` + `Fin.append_comp_sumElim`;
  `fromBlocks_mulVec`; `simp only [Sum.elim_comp_inl/inr, Matrix.zero_mulVec, Matrix.one_mulVec,
  add_zero, zero_add]`; `funext i; Fin.addCases` (`finSumFinEquiv_symm_apply_castAdd/natAdd` +
  `Fin.append_left/right`).
- SIGBUS-135/139 masks real Lean errors (prints misleading `[7744/7744]` then exits on olean-write);
  rebuild several times before trusting.
- **DOCKER INFRA CORRUPT (07-09 eve)**: containerd content store blob I/O error — the image config
  blob `sha256:0e944ca881ad…` is physically unreadable, so `docker image inspect`/fresh `docker run`
  fail; only pre-existing `lean-build-*` containers survive. NOT self-healing. Session additions are
  elaboration-audited vs confirmed Mathlib signatures but NOT docker-verified; re-verify after an
  image re-pull.

## Session 2026-07-09 (later) — content-reduction atoms in literal dimensions (`BezoutDescent`)

**Outcome**: two reusable atoms added (0 sorry / 0 axiom), staying entirely in *literal* `Fin 2`/`Fin 3`
dimensions so the `2 + m` vs `m + 2` cast obstruction never arises. Docker infra STILL DOWN
(containerd `meta.db` write `input/output error` — image build fails before any elaboration); additions
are elaboration-audited by line-for-line mirroring of the audited `sl3_transitive`, NOT docker-verified.

### Decls
- `gcdReduceSL2 (x y) : ∃ N : SL₂, N ·ᵥ ![x,y] = ![gcd x y, 0]` — the general (non-coprime) `SL₂`
  content-reduction atom. `by_cases Int.gcd x y = 0`: zero branch identity (`gcd=0 ⇒ x=y=0`,
  `Int.gcd_eq_zero_iff`), else grandparent `bezoutMatrix`/`bezoutMatrix_det`/`bezoutMatrix_mulVec`.
  Extracts the exact inline tail-reducer `T` that `sl3_transitive` built ad hoc, making it reusable.
- `sl3_content_reduce (a b c) : ∃ M : SL₃, M ·ᵥ ![a,b,c] = ![gcd a (gcd b c), 0, 0]` — CONTENT form of
  `sl3_transitive` (drops `IsCoprime`). Both steps now instances of `gcdReduceSL2`. Proof mirrors
  `sl3_transitive` verbatim (`embedOne`/`headBlock3`, `← mulVec_mulVec`, `hcons`/`hcons2` rfl, `funext;
  fin_cases` + `simpa [mulVec, dotProduct, Fin.sum_univ_two]`). `sl3_transitive` = the `g=1` corollary.

### Why the content form matters
The `n=4` step (and every step) reduces the *tail* of a primitive vector, but that tail is generally
NOT primitive — so the tail reducer must be the CONTENT form (`→ (gcd,0,…,0)`), which the primitive
`slk_transitive` lemmas do not provide. `gcdReduceSL2` + `sl3_content_reduce` are the first two rungs of
that content ladder. General obstruction below unchanged.

### Next step (single remaining ingredient for full induction)
`Fin.cons`/`Fin.append` content bridge: package `(v₀, g, 0,…,0)` as `Fin.append ![v₀,g] 0`, prove
`Fin.cons v₀ (Fin.cons g 0) = Fin.append ![v₀,g] 0`, thread `Int.gcd` bookkeeping through an
induction on `n` (base n=2 = grandparent) alternating `embedOne` and `headBlockN`. Right inductive
statement = **content reduction** (`∃ M ∈ SLₙ, M ·ᵥ v = (gcd v, 0,…,0)`); primitive-vector
transitivity (`→ e₀`) is the `gcd = 1` corollary for `n ≥ 2`.
