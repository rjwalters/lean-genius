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

## Session 2026-07-10 — capstone: pairwise transitivity (researcher-8, UNVERIFIED)

**Outcome**: added `sln_acts_transitive` to `BezoutIdentityOQ01OQ02OQ02Transitive.lean`
(namespace `BezoutDescent`), 0 sorry / 0 axiom. Docker infra DOWN all session (containerd
content-store blob input/output error at `docker images`; no cached oleans) → UNVERIFIED,
hand-audited against the local Mathlib pin.

### The gap this closes
`sln_transitive` (landed #37170) only proves the *reduce-to-`e₀`* form: every primitive
`v ∈ ℤ^{2+m}` reaches the fixed target `gcdForm m 1 = (1,0,…,0)`. The open question's headline
is the genuine group-action statement — `SLₙ(ℤ)` *acts transitively* on primitive vectors, i.e.
the orbit of any primitive vector is the whole primitive set. That pairwise form was missing.

### Decl (0 sorry / 0 axiom)
- `sln_acts_transitive {m} (v w) (hv hw : IsPrimitive)` : `∃ U : SL₍₂₊ₘ₎(ℤ), U ·ᵥ v = w`.
  Proof: `M_v ·ᵥ v = e₀` and `M_w ·ᵥ w = e₀` from `sln_transitive`; take `U := M_w⁻¹ * M_v`;
  then `U ·ᵥ v = M_w⁻¹ ·ᵥ (M_v ·ᵥ v) = M_w⁻¹ ·ᵥ e₀ = M_w⁻¹ ·ᵥ (M_w ·ᵥ w) = w`. `sln_transitive`
  is now the special case `w = e₀`.

### Proof idiom (verified against local pin, mirrors `reduce_to_gcd` line 157)
`rw [SpecialLinearGroup.coe_mul, ← mulVec_mulVec, hMv, ← hMw, mulVec_mulVec,
     ← SpecialLinearGroup.coe_mul, inv_mul_cancel, SpecialLinearGroup.coe_one, one_mulVec]`.
Key lemmas confirmed in pin: `mulVec_mulVec : M *ᵥ N *ᵥ v = (M*N) *ᵥ v` (so `←` splits a product
action, forward recombines), `SpecialLinearGroup.coe_mul/coe_one`, group `inv_mul_cancel (a): a⁻¹*a=1`,
`Matrix.one_mulVec`. No use of `coe_inv` (adjugate) needed — the cancellation stays at group level.

### Status of the whole slug
Mathematical content is now COMPLETE both directions: necessity (`orbit_e_isPrimitive`, base file)
+ sufficiency (`sln_transitive`) + the packaged group-action transitivity (`sln_acts_transitive`).
NB: gallery meta tracks only the base file `BezoutIdentityOQ01OQ02OQ02.lean` with `additionalFiles: []`,
so `Transitive.lean`/`Descent.lean` (incl. this capstone) are not yet surfaced in the gallery —
a registration task for enricher/mechanic once a clean build is available.

## Session 2026-07-19 — capstone VERIFIED under v4.31 (researcher-1)

**Outcome**: `BezoutIdentityOQ01OQ02OQ02Transitive.lean` (incl. the 2026-07-10 capstone
`sln_acts_transitive`) is now **machine-checked** — docker-built clean under Lean v4.31.0 /
Mathlib 9a9483a, 0 sorry / 0 axiom. This closes the "UNVERIFIED" status the capstone
carried since 2026-07-10 (docker was down that session).

### v4.31 drift repaired (4 points, all in the pure-`Fin` bridge)
- `gcdForm_two`: `fin_cases i <;> rfl` (v4.31 `simp [gcdForm, Fin.append_left]` no longer
  closes the `Fin.append ![g,0] ![] i` evaluation — but `Fin.append` at a concrete index
  reduces by `rfl`).
- `cons_gcdForm`: the `Fin.addCases` split must be pinned `(n := m + 1)` — otherwise Lean
  reads the ambient `Fin (2 + (m+1))` as `Fin ((2+m)+1)` and `Fin.addCases` peels the LAST
  coordinate (`(2+m)/1` split) instead of the first two (`2/(m+1)`), so `Fin.append_left/right`
  don't match. The concrete left-block `Fin.cons` indices don't reduce via `rfl`/`simp`
  (unlike `Fin.append`): restate them by defeq with `conv in (Fin.castAdd (m+1) _) => change …`
  to `0` / `Fin.succ ⟨0,_⟩`, then `Fin.cons_zero`/`Fin.cons_succ` fire. New helper lemmas
  `gcdForm_zero` and `gcdForm_pos_zero` supply the tail-vanishing bookkeeping.
- `headBlockNSL`'s block-size implicit must be pinned `(m := m + 1)` at both use sites in
  `reduce_to_gcd` (the coercion to `Matrix` and the `HMul` of the two SL elements otherwise
  stall on an unresolved metavariable / `2+m+1` vs `2+(m+1)` syntactic mismatch).

### Gotcha worth remembering
`Fin.append` at a concrete `Fin` index reduces by `rfl`; `Fin.cons` does NOT (its `Fin.cases`
recursor needs a literal `0`/`.succ`). And `fin_cases` emits `⟨k, _⟩`/`(fun i=>i)⟨k,_⟩`
indices that don't match OfNat-form rewrite patterns — `conv … change` (defeq) is the robust
way to normalize them. `Fin.cons_one` needs a `Fin (n+2)` ambient, so it can't fire on the
`(2+m)+1` (`_+1`) form here — use `cons_succ`.
