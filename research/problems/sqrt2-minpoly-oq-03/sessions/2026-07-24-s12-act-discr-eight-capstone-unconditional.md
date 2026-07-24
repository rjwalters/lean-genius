# S12 ACT (2026-07-24, researcher-3) — discr = 8 proved; capstone UNCONDITIONAL; problem COMPLETED

## Outcome

The file's sole strategic sorry `Q_sqrt2_discr_eq_eight` is closed and the
formal target is delivered unconditionally:

- `Q_sqrt2_classNumber_eq_one : NumberField.classNumber Q_sqrt2 = 1`
- 0 sorries, 0 axioms; `#print axioms` = `[propext, Classical.choice, Quot.sound]`
  for `Q_sqrt2_discr_eq_eight`, `Q_sqrt2_classNumber_eq_one`,
  `isIntegral_elt_iff`, `intBasis`.
- Verification: host `bin/lake env lean` exit 0 (zero warnings) AND Docker
  `docker-build.sh Proofs.Sqrt2MinpolyOQ03` green `[8577/8577]`.

## What was built (S12 section of `Sqrt2MinpolyOQ03.lean`)

1. `exists_elt_eq` — coordinate surjectivity from
   `(AdjoinRoot.powerBasis X_sq_sub_two_ne_zero).basis.reindex (finCongr hdim)`;
   basis vectors identified with `PowerBasis.basis_eq_pow` (`gen⁰ = 1`,
   `gen¹ = root`), assembled with `Fin.sum_univ_two` + `Algebra.smul_def`.
2. `elt_eq_zero` — coordinate uniqueness at 0: `b ≠ 0` contradicts
   `elt_not_mem_range` (irrationality), `b = 0` reduces to injectivity of
   `algebraMap ℚ` (`map_eq_zero_iff`).
3. `sqrt2Int : 𝓞 Q_sqrt2 := ⟨root, root_isIntegral⟩`;
   `sqrt2Int_mul_self : sqrt2Int * sqrt2Int = 2` by transporting `root_sq`
   through `NumberField.RingOfIntegers.ext`.
4. `intBasis : Basis (Fin 2) ℤ (𝓞 Q_sqrt2) := Basis.mk` on `![1, sqrt2Int]`:
   - independence: `Fintype.linearIndependent_iff`; coerce the vanishing
     ℤ-combination through `algebraMap (𝓞 K) K` (`map_zsmul`), rewrite as
     `elt (g 0) (g 1) = 0` (`map_intCast`, `zsmul_eq_mul`), apply `elt_eq_zero`;
   - spanning: `exists_elt_eq` on `↑x`, `x.isIntegral_coe`, S11
     `coords_int_of_isIntegral`, then `x = a0 • 1 + b0 • sqrt2Int` via
     `RingOfIntegers.coe_injective`.
5. Traces over ℤ: `trace_intCast (n) : trace ℤ 𝓞 (algebraMap n) = 2n`
   (`Algebra.trace_algebraMap` + `RingOfIntegers.rank` + `Q_sqrt2_finrank`);
   `trace_sqrt2Int = 0` via `Algebra.trace_eq_matrix_trace intBasis` +
   `Algebra.leftMulMatrix_eq_repr_mul` (left-mul matrix `[[0,2],[1,0]]`:
   diagonal entries are `repr (b 1) 0` and `repr ((2:ℤ)•b 0) 1`, both 0 by
   `Basis.repr_self` + `Finsupp.single_eq_of_ne`).
6. `Q_sqrt2_discr_eq_eight` — `← NumberField.discr_eq_discr Q_sqrt2 intBasis`,
   `Algebra.discr_def`, `Matrix.det_fin_two`; trace matrix `[[2,0],[0,4]]`,
   `det = 8`.
7. `Q_sqrt2_classNumber_eq_one := Q_sqrt2_classNumber_eq_one_of_discr
   Q_sqrt2_discr_eq_eight` — the S9 conditional reduction, now fed.

The former sorry block (mid-file) was removed; the discriminant theorem and
capstone now live at the END of the file (they consume the S11 section).
Downstream anchors referencing old line ranges may need re-anchoring by the
enricher.

## Lean gotchas (v4.31 / Mathlib pin)

- **`Basis` is `Module.Basis`** at this pin: bare `Basis` in source needs
  `open Module` (S3–S11 code never spelled it at top level, so this only bit
  now).
- `rw [← hsum]` where `hsum : … = x` and the goal's OTHER side contains
  `b'.repr x` rewrites the `x` inside `repr` too — use a forward `calc` from
  `Basis.sum_repr` instead.
- `rw`'s terminal rfl does NOT close `(0 : ℤ) + 0 = 0` (literal `OfNat`
  atoms); follow with `norm_num`.
- `Matrix.cons_val_one` alone strands `![y] 0` (the vecHead of the tail);
  plain `simp` closes basis-vector evaluations.
- `map_ofNat` converts `algebraMap ℤ (𝓞 K) 2 = 2` and
  `algebraMap (𝓞 K) K 2 = 2` cleanly; `RingOfIntegers.map_mk`/`sqrt2Int_coe`
  are `rfl`.

## Trackers

- `src/data/research/problems/sqrt2-minpoly-oq-03.json` deliberately NOT
  touched: on main it is 3 concatenated JSON objects (mechanic issue #43405;
  open fix PR #43409). Reconcile the knowledge JSON after that merges.
- Pool status → completed on release.

## Follow-up directions (quality-filtered)

1. **Euclidean strengthening** (`EuclideanDomain (𝓞 Q_sqrt2)` via the norm
   form `|a² − 2b²|`): strictly stronger than PID; genuinely new content
   (Minkowski gives PID, not Euclidean). Session-sized IF `Zsqrtd 2 ≃+*
   𝓞 Q_sqrt2` is built first (the S12 `intBasis` machinery is exactly that
   bridge's ingredients).
2. **Same recipe for the next real quadratic field** (e.g. ℚ(√3), d_K = 12,
   M_K = √3 < 2 — same one-session shape; ℚ(√5) needs the d ≡ 1 (mod 4)
   half-integer ring, a materially different integral-basis argument — that
   variant is the more informative one).

No follow-up merely re-asks this problem; both open new mechanisms.
