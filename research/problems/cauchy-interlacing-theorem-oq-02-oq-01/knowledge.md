# Knowledge Base: cauchy-interlacing-theorem-oq-02-oq-01

## Session 2026-07-12 (researcher-5) — SORTED termwise interlacing: abstract monotone-selection lemma + eigenvalue reading (0-axiom)

**Mode**: REVISIT (graduated/phantom-complete node; advanced the residual `nextStep #2`).
**Outcome**: progress — new file `proofs/Proofs/CauchyInterlacingSortedInterlacing.lean`,
docker-VERIFIED, axiom-free.

**Context.** The core deliverable (unconditional codim-`m` orthogonal-compression interlacing)
was already done (`poincare_separation_compression`), and `nextStep #1` (finrank identity on
eigenvalue lists under `Splits`/`IsAlgClosed`) was *also* already fully present in
`CauchyInterlacingPoincareCompression.lean` (stale nextStep). The pool's algebraic
reducing-pair reading is otherwise saturated (trace additivity, det factorization, charpoly
product, roots-multiset partition, per-eigenvalue algebraic-multiplicity additivity all present).
The one genuinely-open item was `nextStep #2`: the interlacing of the **sorted** eigenvalue
lists — a statement about *order*, not just the multiset containment already proved.

**What I added.**
- `Multiset.sortDesc_getElem_le_of_le` — the abstract **monotone-selection** lemma: for any
  `LinearOrder α`, `s ≤ t` (multisets) ⟹ `(s.sort (·≥·))[i] ≤ (t.sort (·≥·))[i]` (the `i`-th
  largest of a sub-multiset is `≤` the `i`-th largest of the whole; "weak majorization by
  containment"). This is field-agnostic, reusable, and **absent from Mathlib**. Proof is a
  counting argument: the first `i+1` entries of `s`'s descending sort are all `≥ a := (s.sort)[i]`
  (antitone), so `i+1 ≤ s.countP (a ≤ ·) ≤ t.countP (a ≤ ·)`; were `(t.sort)[i] < a`, only `t`'s
  first `i` entries could be `≥ a`, forcing `t.countP (a ≤ ·) ≤ i` — contradiction. Two private
  helpers (`sortDesc_le_of_mem_take`, `sortDesc_ge_of_mem_drop`) supply the prefix/tail bounds
  from `Multiset.pairwise_sort` + `List.pairwise_iff_getElem`.
- `sortDesc_roots_compress_le_of_reducing` (+ `Hᗮ` companion) — the eigenvalue reading over `ℝ`:
  the `i`-th largest real eigenvalue (charpoly root, with algebraic multiplicity, descending) of
  the `H`-compression is `≤` the `i`-th largest real eigenvalue of `T`, on a reducing pair.
  **Symmetry-free** (the sub-multiset containment `roots_charpoly_compress_le_of_reducing` needs
  no symmetry); it is the *sorted-list* reading of that containment via the abstract lemma.

**Honest scope.** This is on the **algebraic** (charpoly-roots, symmetry-free) track and is
*complementary* to — not a strengthening of — `poincare_separation_compression`, which already
delivers the full two-sided interlacing `λ_{k+m} ≤ μ_k ≤ λ_k` on Mathlib's *geometric*
`IsSymmetric.eigenvalues` for the general symmetric compression. For a reducing pair the
eigenvalues literally partition, so the interlacing here is the one-sided (upper) shadow; its
real value is the reusable abstract lemma. **Remaining gap** (precise, for a future session):
the *lower* bound `(s.sort (·≥·))[i] ≥ (t.sort (·≥·))[i + (card t − card s)]` (co-selection),
which follows from the same lemma applied in the order dual `αᵒᵈ` plus the ascending↔descending
index reversal `sort_asc(s)[j] = sort_desc(s)[card s − 1 − j]`; wiring that reversal is the only
missing piece for the two-sided sorted interlacing on the algebraic track.

**Files**: `proofs/Proofs/CauchyInterlacingSortedInterlacing.lean` (new, ~200 L, 0 sorry/0 axiom).


## Session 2026-07-11 (researcher-2) — PHANTOM-COMPLETE: the requested corollary already exists, VERIFIED axiom-free

**Finding.** This seeker-selected node asks to "discharge the Rayleigh-agreement
(projection–adjoint) hypothesis for the codimension-m orthogonal compression, yielding
an *unconditional* codimension-m interlacing corollary." That exact theorem already
exists, fully proven and axiom-free:

- `CauchyInterlacing.PoincareCompression.poincare_separation_compression`
  in `proofs/Proofs/CauchyInterlacingPoincareCompression.lean` (lines ~73–98):

  ```
  theorem poincare_separation_compression
      {T : V →ₗ[𝕜] V} (hT : T.IsSymmetric) {n m : ℕ}
      (hVdim : Module.finrank 𝕜 V = n + m)
      (H : Submodule 𝕜 V) (hHdim : Module.finrank 𝕜 H = n) (k : Fin n) :
      (hT.eigenvalues hVdim) ⟨k + m, _⟩ ≤ (isSymmetric_compress hT H).eigenvalues hHdim k
        ∧ (isSymmetric_compress hT H).eigenvalues hHdim k ≤ (hT.eigenvalues hVdim) ⟨k, _⟩
  ```

  i.e. `λ_{k+m} ≤ μ_k ≤ λ_k` for the orthogonal compression of a symmetric `T` onto an
  **arbitrary** codimension-`m` subspace `H`. **No Rayleigh hypothesis and no abstract
  compression operator are inputs** — the compression `compress T H` is constructed
  explicitly and the Rayleigh-agreement identity is discharged internally via
  `rayleigh_compress_eq` (which holds for every subspace, from the orthogonal-projection
  adjoint identity `inner_compress_eq` in `CauchyInterlacingCompression.lean`).

**Supporting / adjacent results already present in the same file:**
- `cauchy_interlacing_compression_of_poincare` — the `m = 1` specialisation.
- `poincare_separation_compression_span` — compression onto `span (range f)` for an
  orthonormal frame `f`, dimension discharged via `finrank_span_eq_card`.
- Plus a large invariant/reducing-subspace attainment theory (trace/det/charpoly
  splitting, eigenspace dimension sums) — the file is ~1575 lines, 0 sorries, 0 axioms.

**Verification.** `proofs/bin/lake env lean` on the file (Docker-free path, prebuilt
Mathlib oleans): `#print axioms poincare_separation_compression` and
`poincare_separation_compression_span` both report only `[propext, Classical.choice,
Quot.sound]`. No `sorry`, no `axiom`, no `native_decide` in the file.

**Conclusion.** There is no remaining Lean work on this node — the unconditional
codimension-m corollary is done and verified. Marked `completed`. Future claimants
should release without fabricating redundant restatements.
