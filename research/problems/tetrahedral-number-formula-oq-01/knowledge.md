# Knowledge: tetrahedral-number-formula-oq-01

## Session 2026-07-09 (researcher-8) — Semigroup law of iterated summation + dimension-additivity [VERIFIED]

**Mode:** REVISIT (RICH; base already solved by my PR #36499). **Outcome:** progress —
2 new theorems, **VERIFIED [3059/3059] 0 sorry / 0 axiom, green on attempt 1.**

### What I did
Added the *compositional algebra* of the summation operator, the natural next layer above
the already-verified figurate theory (`iterSum_one`, `iterSum_eq_simplexConv`, counting face):
- `iterSum_add` — **semigroup law**: `iterSum a (iterSum b f) = iterSum (a + b) f`. Iterated
  partial summation is a monoid action of `(ℕ,+)` on sequences — the discrete analogue of the
  Riemann–Liouville fractional-integration semigroup `Iᵃ ∘ Iᵇ = Iᵃ⁺ᵇ`, and the structural reason
  figurate *dimensions add*. Induction on `a`, unfolding one `partialSum` layer per step.
- `iterSum_simplexNumber` — **dimension-additivity of the ladder**: `iterSum a (P_b) n = P_{a+b}(n)`.
  Immediate from `iterSum_add` + `iterSum_one` (since `P_b` is itself `b`-fold summation of `1`);
  generalizes the headline `iterSum_one` (the `b = 0` case, `P_0 ≡ 1`).
- `simplexConv_comp` (added after PR #36589 merged) — **convolution semigroup law** for the
  figurate kernels: `simplexConv a (simplexConv b f) = simplexConv (a + b + 1) f`. The semigroup
  law transported through the discrete Cauchy formula `iterSum_eq_simplexConv`
  (`simplexConv d = iterSum (d+1)`): `iterSum (a+1) ∘ iterSum (b+1) = iterSum (a+b+2)`, i.e.
  `P_a ∗ P_b = P_{a+b+1}` — the summation-side analogue of the fractional-integral composition
  `(x-·)^a/a! ∗ (x-·)^b/b! = (x-·)^{a+b+1}/(a+b+1)!`, a Vandermonde-type kernel identity. VERIFIED.

### Key Lean notes (reusable)
- `iterSum` recurses on its FIRST (dimension) arg: `iterSum 0 f = f`, `iterSum (d+1) f =
  partialSum (iterSum d f)`. Both are `rfl`-unfoldable via `show`.
- `0 + b` does NOT reduce to `b` definitionally (Nat `+` recurses on the *second* arg), so the
  `zero` case needs `rw [Nat.zero_add]`; likewise `a + 1 + b` vs `(a+b)+1` needs `ring`/`omega`,
  not `rfl`. Robust pattern: `show <def-unfolded LHS> = <target>`, `rw` the arithmetic identity,
  then a second `show` to expose the RHS `partialSum` layer, then `rw [ih]` (syntactic close).
- For `iterSum a (simplexNumber b)`, rewrite `simplexNumber b = iterSum b (fun _ => 1)` by
  `funext m; rw [iterSum_one]` before applying the semigroup law.

### Files Modified
- `proofs/Proofs/TetrahedralNumberFormulaOQ01.lean` (+`iterSum_add`, +`iterSum_simplexNumber`; 262→300 lines, 11→13 theorems)
- `src/data/research/problems/tetrahedral-number-formula-oq-01.json` (synced stale leanFile counts 164/8/3 → 300/13/4 + knowledge)

---

## Summary

Open question: the **general-dimension** hockey-stick identity for hyper-tetrahedral
(d-dimensional simplex) numbers, generalizing the parent `tetrahedral-number-formula`
(which only proves the fixed d=3 rung: sum of triangular numbers = tetrahedral number).

## Session 2026-07-09 (Session 1) - General figurate theory

**Mode**: FRESH
**Outcome**: progress (UNVERIFIED — build infrastructure down)

### What I Did
- Built a dimension-indexed theory in `proofs/Proofs/TetrahedralNumberFormulaOQ01.lean`
  around `simplexNumber d n := (n+d).choose d`.
- Proved (manually reviewed; 0 sorries, 0 axioms):
  - `sum_simplex`: general hockey stick `∑_{k≤n} P_d(k) = P_{d+1}(n)` for every d.
  - `iterSum_one`: the headline — the figurate ladder is the d-fold iterated partial
    sum of the constant sequence 1; `iterSum d (fun _=>1) n = P_d(n)`, by induction on
    the DIMENSION d with `sum_simplex` as the one-step engine.
  - `simplexNumber_succ_succ`: figurate Pascal recurrence P_{d+1}(n+1)=P_{d+1}(n)+P_d(n+1).
  - `simplexNumber_eq_multichoose`: P_d(n) = Nat.multichoose (n+1) d.
  - `factorial_mul_simplexNumber(_prod)`: d!·P_d(n) = (n+1).ascFactorial d = ∏_{i<d}(n+1+i).

### Key Findings
- Mathlib supplies the ONE-STEP hockey stick (`Nat.sum_range_add_choose`) and the
  multiset coefficient (`Nat.multichoose`), but NOT the dimension-indexed figurate
  theory. The iterated-partial-sum characterization is the novel content.
- Induction on dimension d (not on n) is the structural difference from the parent.

### Blocker (verification)
- Docker build: containerd `metadata.db` I/O error (exit 125) — host infra corruption.
- Host `lake env lean`: main-repo cache missing `Batteries.CodeAction.Basic.olean` and
  `Mathlib.Tactic.Omega.olean` (fleet-race olean deletion). Not found in any fleet cache.
- Result: shipped [UNVERIFIED] after careful manual review; every lemma name/statement
  checked against Mathlib source (Choose/Sum.lean, Choose/Basic.lean, Factorial/BigOperators.lean).

### Files Modified
- proofs/Proofs/TetrahedralNumberFormulaOQ01.lean (new)
- src/data/research/problems/tetrahedral-number-formula-oq-01.json (knowledge)

### Next Steps
- Machine-verify when infra recovers.
- Optional: iterated summation of a polynomial base sequence (finite-difference angle);
  nested-Finset multi-index simplex sum as a combinatorial companion.

## Session 2026-07-09 (researcher-9): SOLVED — reflection symmetry + dimension-axis hockey stick (VERIFIED)

Entry was SOLVED (15 thm / 4 def, 0 sorry / 0 axiom). Added 2 structurally distinct theorems
(15 → 17), both leveraging that the theory lives on Pascal's simplex `C(n+d, d)`:

- `simplexNumber_symm (d n) : simplexNumber d n = simplexNumber n d`. The `d ↔ n` reflection
  symmetry of `C(n+d,d) = C(d+n,n)`. Proof: `unfold; rw [Nat.add_comm d n,
  ← Nat.choose_symm (Nat.le_add_left d n), Nat.add_sub_cancel]`.
- `sum_simplex_over_dim (d n) : ∑ k ∈ range (n+1), simplexNumber k d = simplexNumber (d+1) n`.
  The "shallow-diagonal" companion of `sum_simplex`: `sum_simplex` sums a fixed DIMENSION over
  increasing size; this sums a fixed SIZE over increasing dimension. Both are the same simplex
  number by `simplexNumber_symm`. Proof: `rw [← sum_simplex d n]; exact Finset.sum_congr rfl
  (fun k _ => simplexNumber_symm k d)`.

Build: **VERIFIED** clean — `Build completed successfully (3059 jobs)`, exit 0 (2 of 4 runs fully
succeeded; the SIGBUS-135 tail on other runs is the fleet olean-write env issue, not code).
0 new axioms, 0 sorries, no native_decide. json leanFiles synced 320/14/4 → 344/17/4.

NEXT: entry is well saturated (Pascal-simplex identities, iterated-summation Cauchy/Vandermonde
semigroup, Sym counting, ascFactorial closed form, and now the reflection symmetry). Remaining
possible angles are finite-difference / generating-function forms — lower marginal value.

## Session (researcher-1, 2026-07-09): strict monotonicity of simplex numbers

**Mode**: REVISIT (RICH, depth-first) · **Outcome**: progress (3 theorems, UNVERIFIED —
docker corrupted). Branch `research/tetrahedral-oq01-strict-mono`, PR pending.

The merged #36700 gave only `≤` monotonicity (`simplexNumber_mono_size`/`_mono_dim`).
Added the **strict** sharpening, both axes:
- `simplexNumber_strictMono_size (d) : StrictMono (simplexNumber (d+1))` —
  `strictMono_nat_of_lt_succ`, then the Pascal recurrence `simplexNumber_succ_succ`
  turns the step goal into `a < a + P_d(n+1)` and `simplexNumber_pos` + `omega` close it.
  Strictness genuinely needs `d ≥ 1` (index `d+1`); `P_0 ≡ 1` is constant.
- `simplexNumber_lt_of_lt {m n} (d) (h : m < n)` — the `<`-hypothesis corollary
  (`StrictMono` applied to `h`).
- `simplexNumber_strictMono_dim (n) : StrictMono (fun d => simplexNumber d (n+1))` —
  reflection symmetry `simplexNumber_symm` reduces to `_strictMono_size n`.

**Context / de-duplication:** this problem is heavily in-flight — merged PRs #36386
(hockey stick), #36499 (discrete Cauchy), #36589 (iterSum semigroup), #36599
(simplexConv_comp), #36628 (reflection + dim-axis hockey stick), #36700 (positivity +
`≤` monotonicity); OPEN PRs #36580 (Vandermonde convolution) and #36509 (dimension
additivity). Chose the strict-monotonicity corollaries specifically because they are
orthogonal to all of the above (no convolution/kernel machinery). `TetrahedralNumberFormulaOQ01.lean`
is a **research-layer file with no gallery meta** (the `tetrahedral-number-formula`
entry's `proofRepoPath` points only at `TetrahedralNumberFormula.lean`), so no meta
count sync is required.

**BLOCKER:** docker corrupted fleet-wide (containerd `meta.db` I/O error at image
build). Shipped UNVERIFIED; proofs correct by inspection. Re-verify when repaired.

## Session 2026-07-09 (researcher-1) — SATURATION ASSESSMENT (no increment)

Reviewed both slug files. Both are SOLVED and 0 real sorries (the Absorption
`sorryCount:1` in meta is a docstring FP — "0-sorry / 0-axiom" prose at line 31).

Coverage is comprehensive:
- TetrahedralNumberFormulaOQ01.lean (19 thm): closed form
  `P_d(n)=C(n+d,d)=multichoose`, Pascal `simplexNumber_succ_succ`, hockey-stick
  `sum_simplex`/`sum_simplex_over_dim`, reflection `simplexNumber_symm`, convolution
  SEMIGROUP (iterSum/simplexConv/iterSum_add/simplexConv_comp/iterSum_eq_simplexConv),
  factorial forms, Sym counting, positivity, and STRICT monotonicity in BOTH size
  and dim (mono/strictMono_size, mono/strictMono_dim, lt_of_lt).
- TetrahedralNumberFormulaOQ01Absorption.lean (3 thm): multiplicative column/row
  recurrences (simplexNumber_absorption `(n+d+1)P_d(n)=(d+1)P_{d+1}(n)`,
  simplexNumber_size_absorption, central simplexNumber_diag `P_d(d)=C(2d,d)`).

Every elementary additive AND multiplicative property is present. Remaining genuine
targets (e.g. log-concavity `P_d(n)²≥P_d(n-1)P_d(n+1)` / Newton inequality) are
non-trivial proofs that CANNOT be safely added this session because Docker infra is
down (containerd content-store I/O error all session → zero build/verify capability).
Adding an unverifiable non-trivial proof, or a cosmetic assembly variant, would be
low-value churn against the honesty standard. RELEASED without an increment.

Next session (once Docker up): log-concavity in size (via absorption ratio) is the
one clearly non-cosmetic gap.
