# Knowledge Base: cauchy-interlacing-theorem

Insights accumulated during research on this problem.

---

## Problem Understanding

Cauchy interlacing: if `B` is the principal `(n-1)×(n-1)` submatrix of a Hermitian
`A ∈ ℂ^{n×n}` (delete one matching row/column), the sorted eigenvalues interlace:
`λ_k ≤ μ_k ≤ λ_{k+1}` (ascending convention). The proof of record is the
Courant–Fischer min-max variational characterisation restricted to the
codimension-one coordinate subspace.

---

## Insights

### Session 2026-06-16 (s08, REVISIT → ACT, **KEYSTONE PROVEN**) — Courant–Fischer max–min, 0-sorry/0-axiom, build-green

**Mode**: REVISIT → ACT. Aristotle MCP `prove` still 404 (re-probed `a+b=b+a`).
But Docker builds **WORK** — the `proofs/.lake` self-symlink does NOT block builds
(the s05/s07 "blackout" diagnosis was wrong): `docker-build.sh` clones the source
tree fresh inside the container and pulls 7727 oleans from the Azure mathlib cache
through the symlink. Always check by actually building, not by `ls -ld proofs/.lake`.

**Result**: new file `proofs/Proofs/CauchyInterlacingKeystone.lean` —
`✔ [7743/7743] Built … (31s)`, **0 sorry / 0 axiom** (verified: build emitted no
`declaration uses sorry`). This **closes the single documented Mathlib gap** that
blocked the problem for s03–s07. The dishonest `courant_fischer_placeholder : True`
in `CauchyInterlacing.lean` is now superseded by the real, proven content.

**Key idea — state the max–min in BOUND FORM, not `iSup`/`iInf`.** The
conditionally-complete-lattice junk-value pain of an `⨆/⨅` formulation is entirely
avoided by splitting Courant–Fischer into two bound statements that carry the same
information and reduce *directly* to the two verified sublemmas:

* LOWER (`eigenvalue_maxmin_lower`): for antitone `μ`, the `(k+1)`-dim eigenspan
  `span {b 0,…,b k}` (= `span (b '' Iic k)`) has *every* nonzero Rayleigh quotient
  `≥ μ k`. ⇒ an optimal subspace witnessing `max min R ≥ μ k` exists. Proof =
  `rayleigh_bounds_on_eigenspan.1` (Sublemma A) + `Finset.le_inf'` (antitone ⇒
  `μ k ≤ μ i` for `i ≤ k`).
* UPPER (`eigenvalue_maxmin_upper`): for antitone `μ`, *every* `(k+1)`-dim subspace
  `S` contains a nonzero `x` with Rayleigh `≤ μ k`. ⇒ no subspace beats `μ k`.
  Proof = intersect `S` with `W := span (b '' Ici k)` (dim `n-k`); dimension count
  `(k+1)+(n-k)=n+1 > n` ⇒ `inf_ne_bot_of_finrank_add_lt` (Sublemma B) gives nonzero
  `x ∈ S ⊓ W`; `rayleigh_bounds_on_eigenspan.2` + `Finset.sup'_le` bound it by `μ k`.

**New reusable lemmas (all 0-sorry):**
- `finrank_span_image_eq_card b I : finrank (span (b '' ↑I)) = I.card`. Recipe:
  `(b.orthonormal.linearIndependent).comp _ Subtype.val_injective` →
  `Set.range_comp` + `Subtype.range_coe` → `finrank_span_eq_card` → `simp`.
- `rayleigh_ge_on_eigenspan_of_lb` / `exists_rayleigh_le_in_subspace` — the
  index-set-parametrised halves (the genuinely reusable content; the Fin-interval
  versions are thin corollaries).

**Mathlib API that worked first-try (v4.26.0):** `Fin.card_Iic` (`= ↑k+1`),
`Fin.card_Ici` (`= n - ↑k`), `Module.finrank_eq_card_basis b.toBasis` +
`Fintype.card_fin` (⇒ `finrank E = n`), `Finset.le_inf'`/`Finset.sup'_le`,
`Submodule.mem_inf`. All in the abstract `LinearMap`/`OrthonormalBasis` framework
(eigenvalues as `μ : Fin n → ℝ`, `T (b i) = μ i • b i`), matching the sublemmas.

**Still open (next session):** (1) bridge the abstract keystone to
`Matrix.IsHermitian.eigenvalues₀` / `CauchyInterlacing.sortedEigs` (matrix ↔
linear-map + sorting permutation); (2) assemble the final `cauchy_interlacing`
inequality `λ(i+1) ≤ μ i ≤ λ i` for `principalDrop` from the two halves via the
coordinate-subspace inclusion. The hard variational core is now DONE; what remains
is the (still nontrivial) impedance-matching bookkeeping.

### Session 2026-06-16 (s07, REVISIT → stand-down, dual blackout) — Sublemma A glue transcribed turnkey

**Mode**: REVISIT under dual backend blackout, **new blackout flavor**. Aristotle
MCP `prove` → `Resource not found` (404, re-confirmed this session with a trivial
`a+b=b+a` probe). Docker *daemon* is UP (`docker run --rm alpine echo` → rc 0) but
**builds are blocked**: `proofs/.lake` is a **circular self-symlink**
(`proofs/.lake -> /Users/.../proofs/.lake`, in BOTH the worktree and main repo), so
`docker-build.sh` cannot reach the Mathlib oleans / its git-clone of the tree fails.
This is distinct from s05/s06's "Docker saturated/hung" — the daemon answers, the
build tree is corrupt. Don't conclude "Docker down" from `docker run` succeeding;
check `ls -ld proofs/.lake`.

**No new PR** — the problem already has 3 open PRs (#24977 mergeable doc-plan,
#24796 + #24924 both CONFLICTING) and adding a 4th unverifiable orphan would be
churn. This entry instead **transcribes** the exact code for the s06-documented
turnkey step so the next backend-up session can paste-and-build with zero
re-derivation.

**Turnkey #1 — discharge Sublemma A's `sorry` in `lean/CauchyInterlacingMinMax.lean`.**
The merged `lean/CauchyInterlacingSublemmas.lean` (#24939, VERIFIED 0-sorry/0-axiom)
already proves the general bound `Sublemmas.rayleigh_bounds_on_eigenspan`. Sublemma A
(`rayleigh_mem_Icc_of_mem_eigenspan`) is its instantiation. Replace the `sorry` with:

```lean
  -- `rayleigh T x` is defeq to `RCLike.re ⟪T x, x⟫ / ‖x‖ ^ 2`.
  unfold rayleigh
  exact Sublemmas.rayleigh_bounds_on_eigenspan T
    (hT.eigenvectorBasis hn) (hT.eigenvalues hn)
    (fun i => hT.apply_eigenvectorBasis hn i) I hI x hmem hx
```

To make this compile in one shot, the two files must be co-located (inline the
`CauchyInterlacing.Sublemmas` namespace into the same file, or build them as one
Lake target — the staging `lean/` dir is NOT a package). Confidence: HIGH on the
math/instantiation; UNVERIFIED on exact API spellings — watch (a)
`hT.apply_eigenvectorBasis hn i : T (eigenvectorBasis hn i) = (eigenvalues hn i:𝕜) • …`
(need the `∀ i` form, hence the `fun i =>`), and (b) the `'' (I : Set (Fin n))`
vs `(b : Fin n → E) '' ↑I` coercion match — if `unfold rayleigh` doesn't fire, try
`show RCLike.re _ / _ ≤ _ ∧ _` / `simp only [rayleigh]`.

**Turnkey #2 — fix the mis-stated keystone (still open, the real gap).** As flagged
in s06 (#24977), `eigenvalue_eq_iSup_iInf_rayleigh` equates the **unsorted**
`hT.eigenvalues hn k` to a max–min that returns the (k+1)-th *largest* eigenvalue.
`LinearMap.IsSymmetric.eigenvalues` is indexed by the eigenbasis, NOT sorted, so the
identity is false as written. Restate over a descending-sorted enumeration
(`CauchyInterlacing.sortedEigs`, antitone — lives in
`lean/CauchyInterlacing.lean` on branch `research/cauchy-interlacing-statement`,
not yet co-located) before attempting the proof. Do NOT submit the current statement
to Aristotle — it would chase a false goal.



**Mode**: REVISIT (Aristotle MCP down → `Resource not found`; Docker had room:
1 active build + 1 idle 8h zombie, ~300 MB of 7.65 GiB used, so the
"Docker target" path was open even though the Aristotle path was not).

**Outcome**: `CauchyInterlacingSublemmas.lean` is now `sorry`-free / 0-axiom and
**machine-checked green** (`docker-build.sh`, Lean v4.26.0, full file 131 s). The
two remaining `sorry`s (the Parseval leaf identities from s03) were discharged by
hand, and the previously *unverified* candidate proofs (Sublemma B dimension
count, `weighted_mean_mem_inf_sup`) were confirmed to compile.

- **Shared support lemma** `repr_eq_zero_of_not_mem`: for `x ∈ span (b '' I)` and
  `i ∉ I`, `b.repr x i = 0`. Proof: `b.repr_apply_apply` → `⟪b i, x⟫ = 0`, then
  `Submodule.span_induction` — `mem` generator case is orthonormality
  `orthonormal_iff_ite` with `i ≠ j` (from `i ∉ I`, `j ∈ I`), closed under
  `+`/`•` by `inner_add_right` / `inner_smul_right`. Discharges both leaves (the
  exact prediction from s03).
- **Leaf A** `norm_sq_eq_sum_repr_sq`: `← b.repr.norm_map x`,
  `EuclideanSpace.norm_eq`, `Real.sq_sqrt (sum_nonneg …)`; then
  `(Finset.sum_subset (subset_univ I) …).symm` restricts to `I`.
- **Leaf B** `re_inner_apply_eq_sum_repr_mul`: helper `repr_apply_of_diag` proves
  `b.repr (T x) i = b.repr x i * μ i` (expand `T x` via `← b.sum_repr x`,
  `map_sum`/`map_smul`/`hb`, then `inner_sum` + `Finset.sum_eq_single i`). Then
  `← b.repr.inner_map_map (T x) x`, `PiLp.inner_apply`, `RCLike.inner_apply`,
  `RCLike.conj_ofReal`, `RCLike.mul_conj` give `⟪T x, x⟫ = ∑_i μ i · ‖b.repr x i‖²`;
  restrict, then `RCLike.re_ofReal_mul`.

**Mathlib API notes (v4.26.0)**: coords print as `(b.repr x).ofLp i`;
`RCLike.mul_conj` matches `z * conj z` (reassociate with `← mul_assoc`, not
`conj_mul`); `push_cast; ring` cleans `↑(‖·‖²)` casts. `Submodule.span_induction`
uses cases `mem | zero | add | smul`.

**Still open**: the Courant–Fischer max–min keystone (`CauchyInterlacing.lean:95`)
— the actual Mathlib gap. All sublemmas it reduces to are now proven; next step is
assembling the keystone from `rayleigh_bounds_on_eigenspan` +
`inf_ne_bot_of_finrank_add_lt`.

### Session 2026-06-16 (s05, REVISIT → stand-down, dual blackout)

**Mode**: REVISIT under dual backend blackout. Aristotle MCP `prove` →
`Resource not found` (404); Docker daemon hung (`docker info` times out, no
`docker ps`). No verifiable Lean possible this session.

**State confirmed**: `CauchyInterlacingSublemmas.lean` is `sorry`-free / 0-axiom
on `origin/main` (the 5 `sorry` greps are all in comments). The lone open
obligation is the keystone `cauchy_interlacing` (`CauchyInterlacing.lean:95`),
which still reduces to `courant_fischer_placeholder : True` — i.e. the
Courant–Fischer max–min identity is genuinely not yet started in Lean.

**Pointer fix (the reason for this note)**: the s04 note and `Sublemmas.lean`
header both cite `approaches/keystone-minmax-proof-design.md` for the full
keystone proof design + per-step Mathlib lemma map. **That file is NOT on
`main`** — it lives only in the still-OPEN PR #24796
(branch `research/cauchy-interlacing-orient`, commit `0dab61880d7`). A future
session that greps `main` for it will come up empty; read it via
`git show 0dab61880d7:research/problems/cauchy-interlacing-theorem/approaches/keystone-minmax-proof-design.md`
or from PR #24796.

**Why no Lean shipped**: the next step (boundedness `have`s §3 → max–min identity
§2 → matrix↔operator eigenvalue bridge → assembly) is all API-heavy closed
mathematics (`ciSup`/`ciInf` plumbing, `eigenvalues_antitone`,
`apply_eigenvectorBasis`, `finrank_span_eq_card`, the
`Matrix.IsHermitian.eigenvalues₀` ↔ operator-`eigenvalues` correspondence). None
of these names can be confirmed without a compiler; blind-writing them would be
unverifiable scaffolding. ACT (submit the max–min identity as an Aristotle
`prove_file` companion, or build it under Docker) when either backend returns.

### Session 2026-06-15 (s01, FRESH → ORIENT)

- **Mathlib API correction (vs. older notes).** Mathlib now ships
  `Matrix.IsHermitian.eigenvalues₀ : Fin (Fintype.card n) → ℝ`, the eigenvalues
  in **descending** order, with `Matrix.IsHermitian.eigenvalues₀_antitone`. This
  is the sorted enumeration earlier sessions thought was absent. It makes a clean
  statement of "the k-th eigenvalue" possible — the plain
  `Matrix.IsHermitian.eigenvalues : n → ℝ` is reindexed by the matrix index type
  and is **not** sorted, so it cannot express interlacing directly.
- **Statement of record written** using `eigenvalues₀`. With the descending
  convention the theorem reads `λ i ≥ μ i ≥ λ (i+1)` for `i : Fin n` (the
  ascending textbook convention flips the inequalities under `i ↦ n - i`).
- **Reusable helper `sortedEigs`**: composes `eigenvalues₀` with the canonical
  `Fin N ≃ Fin (Fintype.card (Fin N))` so eigenvalues are indexed naturally by
  `Fin N`; `sortedEigs_antitone` carries the descending order across.
- **Principal submatrix** modelled as `A.submatrix Fin.castSucc Fin.castSucc`
  (delete the last index); Hermitian-ness is inherited via
  `Matrix.IsHermitian.submatrix`.

### Session 2026-06-15 (s02, REVISIT → ORIENT refine)

Backends both gated this session (Aristotle MCP connected but backend returns
`Resource not found` / 404 on a trivial probe; Docker at 3 `lean-build` peers,
over the 2-container safety threshold on the 7.65 GiB VM — building would OOM
peers). No verification possible; this session is a grounded design refinement.

- **Gap confirmed against *current* Mathlib docs (2026-06), not just prior memory.**
  - `Mathlib.Analysis.Matrix.Spectrum`: `eigenvalues₀`, `eigenvalues₀_antitone`,
    `spectral_theorem` (`A = conjStarAlgAut … eigenvectorUnitary (diagonal (ofReal ∘ eigenvalues))`),
    plus `eigenvectorBasis` / `eigenvectorUnitary`. **No** Rayleigh / min-max here.
  - `Mathlib.Analysis.InnerProductSpace.Rayleigh`: only the **extreme** cases —
    `IsSelfAdjoint.hasEigenvector_of_isMaxOn` (sup of `T.rayleighQuotient` is the
    *largest* eigenvalue) and `…hasEigenvector_of_isMinOn` (inf → smallest). No
    k-th eigenvalue / Courant–Fischer / subspace min-max anywhere. Gap is real.
- **Corrected interlacing reduction (s01 note had the directions muddled).**
  Set `N = n+1`, `H = span{e₀,…,e_{n-1}}` (codim 1); for `x` supported on `H`,
  `R_B(x) = R_A(x)` because `⟨x, A x⟩ = ⟨x, B x⟩`. The admissible test subspaces
  for `B` are **exactly** the `A`-test subspaces contained in `H` — a *subfamily*.
  Both bounds then follow from one fact, restricting an extremum to a subfamily:
  - `μ i ≤ λ i` from the **max–min** form: `μ i = max_{S⊆H, dim=i+1} min_S R`;
    the family `{S ⊆ H}` ⊆ `{S ⊆ V}`, and a max over a *subfamily* is *smaller*,
    so `μ i ≤ max_{S⊆V, dim=i+1} min_S R = λ i`.
  - `λ (i+1) ≤ μ i` from the **min–max** (codim) form: `μ i = min_{T⊆H, dim=N-1-i} max_T R`;
    the family `{T ⊆ H, dim = N-1-i}` ⊆ `{T ⊆ V, dim = N-1-i}` (= A-family for
    index `i+1`, since `N-(i+1) = N-1-i`), and a min over a *subfamily* is
    *larger*, so `μ i ≥ min_{T⊆V} max_T R = λ (i+1)`.
- **Explicit constructive proof of the keystone min–max** (to build), with the
  named Mathlib pigeonhole lemma:
  - Lower (`λ k ≥ value`): test `S = span{v₀,…,v_k}` (top `k+1` eigenvectors);
    for `x = Σ_{j≤k} c_j v_j`, `R(x) = Σ|c_j|²λ_j / Σ|c_j|² ≥ λ_k` since each
    `λ_j ≥ λ_k`. So `min_S R ≥ λ_k`, hence the max–min `≥ λ_k`.
  - Upper (`λ k ≤ value`): for ANY `S` with `dim S = k+1`, intersect with
    `W = span{v_k,…,v_{N-1}}` (`dim W = N-k`). Via
    **`Submodule.finrank_sup_add_finrank_inf_eq`**:
    `finrank (S ⊓ W) = finrank S + finrank W − finrank (S ⊔ W) ≥ (k+1)+(N-k) − N = 1 > 0`,
    so `S ⊓ W ≠ ⊥`. Any `0 ≠ x ∈ S ⊓ W` is a combination of `v_k,…,v_{N-1}`, so
    `R(x) ≤ λ_k`; thus `min_S R ≤ λ_k`, hence the max–min `≤ λ_k`. (Dual argument
    with `span{v_k}` / `span{v₀,…,v_k}` gives the min–max form.)
  This is the actual crux s01 hand-waved as "orthogonal-complement dimension
  counting" — the dimension pigeonhole is one named lemma, not new infrastructure.

### Session 2026-06-15 (s03, ACT — Sublemma A assembly discharged)

Dual blackout persisted (Aristotle `prove` → `Resource not found`/404 live-probed;
Docker `ps` hangs / pool unsafe). Build-free ACT step on the **merged**
`CauchyInterlacingSublemmas.lean`:

- **Sublemma A assembly is now `sorry`-free.** `rayleigh_bounds_on_eigenspan`
  previously held one opaque `sorry`. It is now reduced — with a verified glue —
  to exactly **two** named Parseval leaf lemmas:
  * `norm_sq_eq_sum_repr_sq` : `‖x‖² = ∑_{i∈I} ‖b.repr x i‖²`, and
  * `re_inner_apply_eq_sum_repr_mul` : `re ⟪T x, x⟫ = ∑_{i∈I} ‖b.repr x i‖² · μ i`.
  The positive-mass hypothesis `0 < ∑_{i∈I} ‖b.repr x i‖²` is **derived** from the
  first identity and `‖x‖>0` (`pow_pos (norm_pos_iff.mpr hx0) 2`), so it is *not*
  an independent obligation — the net leaf count for Sublemma A is two, not three.
- **Glue recipe** (verified modulo build): `hwnonneg := fun i _ => sq_nonneg _`;
  rewrite the Rayleigh quotient by the two identities (`rw [h1, h2]`); close with
  `weighted_mean_mem_inf_sup μ I hI (fun i => ‖b.repr x i‖²) hwnonneg h3`. Avoided
  `set` (its opacity blocks `sq_nonneg`/`positivity` on `w i`) by passing the
  explicit weight lambda.
- **Both leaves share one crux**: `b.repr x i = ⟪b i, x⟫ = 0` for `i ∉ I` (the
  off-support vanishing from `x ∈ span (b '' I)` + orthonormality). Proving that
  support lemma once discharges both — the ideal first Aristotle submission when
  the backend returns. Candidate Mathlib map recorded in each lemma's docstring
  (`b.repr.norm_map` + `EuclideanSpace.norm_eq` + `Finset.sum_subset` for the
  norm leaf; `OrthonormalBasis.sum_repr` + `hb` + Parseval for the form leaf).
- **Not** verified (build-pending under blackout); not registered in `Proofs.lean`.

---

## Dead Ends

(none yet)

---

## Mathlib Gap (keystone)

The single missing ingredient is the **Courant–Fischer max–min characterisation**
of the descending k-th eigenvalue:

  `λ_k = max_{dim S = k+1} min_{0 ≠ x ∈ S} ⟨x, A x⟩ / ⟨x, x⟩`
       `= min_{dim S = n-k} max_{0 ≠ x ∈ S} ⟨x, A x⟩ / ⟨x, x⟩`.

Mathlib has only the **extreme cases** (top/bottom eigenvalue as a Rayleigh
quotient sup/inf via the inner-product Rayleigh API). The general k-th min-max is
absent. Estimated effort: a self-contained min-max over
`Submodule ℂ (EuclideanSpace ℂ (Fin N))` with the Rayleigh quotient — a few
hundred lines, the natural next build target (or a Mathlib contribution).

Once the min-max lemma exists, interlacing is a short subspace-inclusion argument:
the `(k+1)`-dimensional test subspaces available to `B` are exactly those
contained in the codimension-one coordinate subspace `span{e₀,…,e_{n-1}}`, a
subset of those available to `A`. The inclusion sandwiches `μ_k` between `λ_k`
(more subspaces can only raise the max) and `λ_{k+1}` (the deleted dimension
contributes at most one to the min-max index).

---

## Next Steps

1. **Build the keystone min–max** over `Submodule ℂ (EuclideanSpace ℂ (Fin N))`
   with `T.rayleighQuotient` (`T := Matrix.toEuclideanLin A` as a self-adjoint CLM;
   needs the `eigenvalues₀ = sorted operator eigenvalues` bridge via
   `spectral_theorem` / `eigenvectorBasis`). Prove both forms using the explicit
   constructive recipe in s02: top-`k+1` eigenvector span for the lower bound, and
   `Submodule.finrank_sup_add_finrank_inf_eq` for the upper-bound pigeonhole. This
   is the single isolated obligation and the **ideal Aristotle target** once the
   backend is reachable (404 this session) — submit the min–max lemma alone.
2. Discharge `cauchy_interlacing` from the min–max lemma via the corrected
   subfamily-monotonicity reduction in s02 (`{S ⊆ H}` ⊆ `{S ⊆ V}`; max–min over a
   subfamily ↓ gives `μ i ≤ λ i`, min–max over a subfamily ↑ gives `λ(i+1) ≤ μ i`).
3. As an interim verifiable win when a Docker window opens (≤ 2 peers): build the
   *existing* skeleton (`sortedEigs_antitone`, `principalDrop_isHermitian`, the
   `cauchy_interlacing` statement with its one `sorry`) by copying it to
   `proofs/Proofs/CauchyInterlacing.lean` and running
   `docker-build.sh Proofs.CauchyInterlacing` — locks in the foundation without
   registering in `Proofs.lean`.
4. Register & flip meta to verified only after the min–max keystone is proved and
   the full file builds green.
