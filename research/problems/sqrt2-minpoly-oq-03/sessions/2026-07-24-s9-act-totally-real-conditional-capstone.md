# 2026-07-24 — S9 ACT (researcher-2): totally-real + conditional capstone [BUILD-VERIFIED]

## TL;DR

Re-opened from BLOCKED (Docker up again; the 2026-06-13 blackout condition no
longer holds). Shipped the **largest single Lean delta in this problem's
history** (+115/−23 LOC in `Sqrt2MinpolyOQ03.lean`) and build-verified it:
`./proofs/scripts/docker-build.sh Proofs.Sqrt2MinpolyOQ03` green at
**[8577/8577]**, sole warning the expected strategic sorry (L189).

Three of S8's four remaining capstone sub-targets are now **DONE**:

| S8 sub-target | Status after S9 |
|---|---|
| (1) `discr Q_sqrt2 = 8` | **OPEN** — the single remaining strategic sorry (`Q_sqrt2_discr_eq_eight`) |
| (2) `nrComplexPlaces = 0` | **DONE** — `Q_sqrt2_nrComplexPlaces`, via new `IsTotallyReal` instance |
| (3) Minkowski-bound arithmetic | **DONE** — absorbed into `Q_sqrt2_classNumber_eq_one_of_discr` (`norm_num`) |
| (4) capstone PID assembly | **DONE** — `Q_sqrt2_classNumber_eq_one` assembled; conditional on (1) only |

## Headline discovery: the v4.31 pin resurrects the short route

S8 (v4.26 pin) established that `isPrincipalIdealRing_of_abs_discr_lt` did
**not** exist and prescribed the long route through
`isPrincipalIdealRing_of_isPrincipal_of_pow_le_of_mem_primesOver_of_mem_Icc`
(4 sub-targets incl. a `⌊M K⌋₊ = 1` arithmetic reduction). The repo has since
moved to the **v4.31** Mathlib pin, where
`RingOfIntegers.isPrincipalIdealRing_of_abs_discr_lt` **EXISTS**. This
collapses sub-targets (3)+(4) into a 4-line proof:

```lean
theorem Q_sqrt2_classNumber_eq_one_of_discr
    (hd : NumberField.discr Q_sqrt2 = 8) :
    NumberField.classNumber Q_sqrt2 = 1 := by
  rw [NumberField.classNumber_eq_one_iff]
  apply RingOfIntegers.isPrincipalIdealRing_of_abs_discr_lt
  rw [hd, Q_sqrt2_nrComplexPlaces, Q_sqrt2_finrank]
  norm_num [Nat.factorial]
```

The bound is `|discr| < (2 · (π/4)^r₂ · (nⁿ/n!))²` = `(2·1·2)² = 16` with
`r₂ = 0`, `n = 2`; `|8| = 8 < 16` closes by `norm_num`.

## New build-verified content (bottom-up)

1. `embedding_root_sq (φ : Q_sqrt2 →+* ℂ) : φ root ^ 2 = 2` — ring homs
   preserve `root² = 2` (from `AdjoinRoot.eval₂_root` + `map_ofNat`).
2. `conj_eq_self_of_sq_eq_two : z ^ 2 = 2 → conj z = z` — from `(z²).im = 0`
   get `re·im = 0`; the `re = 0` branch forces `−im² = 2`, killed by
   `nlinarith [sq_nonneg z.im]`.
3. `complexEmbedding_isReal (φ) : ComplexEmbedding.IsReal φ` — the technical
   heart. **Instance-safe route**: instead of `AdjoinRoot.algHom_ext` (which
   hit ℚ-algebra-instance unification friction on `ℂ`), precompose both
   `conjugate φ` and `φ` with the surjection `AdjoinRoot.mk` and apply
   `Polynomial.ringHom_ext`:
   - on `C`-constants: `Subsingleton (ℚ →+* ℂ)` (any two ring homs from ℚ
     agree) — no algebra instances needed;
   - on `X`: reduces to `conj (φ root) = φ root`, closed by (1)+(2).
   Surjectivity (`AdjoinRoot.mk_surjective`) then extends agreement to all of
   `Q_sqrt2`. This was the fix in commit `0a3426732a` after the first draft's
   `algHom_ext` route failed to elaborate.
4. `instance : NumberField.IsTotallyReal Q_sqrt2` — from (3) via
   `InfinitePlace.isReal_iff`.
5. `Q_sqrt2_nrComplexPlaces : nrComplexPlaces Q_sqrt2 = 0` — bearer
   `IsTotallyReal.nrComplexPlaces_eq_zero`.
6. `Q_sqrt2_classNumber_eq_one_of_discr` — conditional capstone (above).
7. `Q_sqrt2_classNumber_eq_one` — main theorem, assembled as
   `..._of_discr Q_sqrt2_discr_eq_eight`.

## Remaining work (S10+): `Q_sqrt2_discr_eq_eight`

The single open input. Sketched route (docstring L178–188):

- Prove `𝓞 K = ℤ[√2]`: `a + b·root` integral ⟺ `a, b ∈ ℤ` (trace `2a ∈ ℤ`,
  norm `a² − 2b² ∈ ℤ`, mod-4 case analysis).
- Exhibit `{1, root}` as a `Basis (Fin 2) ℤ (𝓞 K)`.
- `discr K = det [[tr 1, tr √2], [tr √2, tr 2]] = det [[2, 0], [0, 4]] = 8`
  via `NumberField.discr_eq_discr`.
- Checked at the pin: **no** `Zsqrtd ↔ RingOfIntegers` bridge exists, so the
  integral-basis argument must be done by hand. Estimate: 1–2 full sessions.

## Ledger

- Sorries: **1** (unchanged in count, massively narrowed in content: was "the
  entire discr/Minkowski/PID chain", is now "one discriminant computation").
- Axioms: **0**.
- Build: `[8577/8577]` green, Docker, Mathlib v4.31 pin.
- Iteration 16 → **17**. Status: BLOCKED → **active** (blackout premise gone;
  this session is a real Docker-verified ACT, not PREP churn).

## Honest assessment

The mathematical content of S9 (total-reality of Q(√2)) is elementary, but it
is genuinely formalized, not assumed — the `z² = 2 → z real` argument and the
`ringHom_ext` extension are complete proofs. The capstone remains conditional:
the slug is **not** verified (1 sorry). The honest headline is the route
collapse from the v4.31 pin upgrade plus 3-of-4 sub-targets discharged.
