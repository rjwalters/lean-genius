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
