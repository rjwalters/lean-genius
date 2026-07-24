# Knowledge Base: erdos-116-wip-01

Insights accumulated during research on this problem.

## Session 2026-07-21 (researcher-1) — strict positivity of the lemniscate area

The prior "elementary layer saturated" note (open/measurable/bounded/finite) missed one
genuinely-elementary gap: **strict positivity** of the measure. Prior work proved
`μ ≥ 0` and `μ < ⊤`; a *nonempty open* set in the plane has *positive* Lebesgue measure,
pinning the volume in `(0, ⊤)` so the parent `sublevelMeasure` (`.toReal`) is genuinely
nonzero, not the `⊤ ↦ 0` truncation nor a degenerate `0`. Added 3 axiom-free theorems to
`Erdos116WIP01.lean` (host-verified v4.31.0; `#print axioms` = propext/Classical.choice/
Quot.sound on all three):

- `volume_sublevelSet_pos` (`ℂ`-side, `0<n`) — `0 < volume Sₚ` from
  `(isOpen_sublevelSet P).measure_pos volume (sublevelSet_nonempty P hn)`
  (ℂ `volume` is an `IsOpenPosMeasure`, so the instance resolves with no extra hypotheses).
- `volume_realProd_sublevelSet_pos` (parent `ℝ×ℝ`-side) — transported across the
  volume-preserving `ℂ ≃ᵐ ℝ×ℝ`, exact mirror of `volume_realProd_sublevelSet_lt_top`
  (`realProd_sublevelSet_eq_preimage` + `MeasurePreserving.measure_preimage` on the
  `nullMeasurableSet`).
- `sublevelMeasure_pos` (`0<n`) — `0 < sublevelMeasure P` via `ENNReal.toReal_pos`
  fed the positivity (`.ne'`) and finiteness (`.ne`) facts. Sharpens `sublevelMeasure_nonneg`.

### Remaining open (unchanged)
- The DEEP quantitative bounds — KLR `c/log n` lower, Pólya `π` upper, the
  `1/log n` vs `1/log log n` gap — need logarithmic-potential / area-of-lemniscate
  machinery absent from Mathlib v4.31. Positivity/finiteness give `0 < μ < ⊤` but no
  quantitative control. Elementary well-definedness layer is now truly complete.

---

## Session 2026-07-20 (researcher-1, iter 1 ACT) — sublevel set open / measurable / bounded

**Mode**: first real ACT on a fresh wip-01 node (parent `Erdos116Problem.lean`
had 5 axiom-free structural lemmas; no `Erdos116WIP01.lean` existed).
**Outcome**: progress — new file `proofs/Proofs/Erdos116WIP01.lean` with 6
declarations (5 public results + `sublevelSet_eq_preimage`), 0 sorry / 0 axiom /
no native_decide, VERIFIED axiom-free (`[propext, Classical.choice, Quot.sound]`).
Host-verified without Docker (parent imports `Mathlib` only): fresh-built
`Erdos116Problem.olean` via `lake env lean`, compiled the child clean (exit 0, no
warnings), `#print axioms` on all five public results.

This discharges **Key lemma 1** of `problem.md`: the lemniscate
`Sₚ = {z : |p(z)| < 1}` is open (hence measurable) and bounded.

### What I added (namespace `UnitDiskPoly`)
- `continuous_eval : Continuous P.eval` — `z ↦ ∏ᵢ (z - zᵢ)` is a finite product of
  continuous factors (`continuous_finsetProd`, each factor `continuous_id.sub
  continuous_const`).
- `sublevelSet_eq_preimage` — `Sₚ = (fun z => ‖p(z)‖) ⁻¹' Set.Iio 1` (`rfl` after
  unfolding, since `Complex.abs = ‖·‖`).
- `isOpen_sublevelSet` — continuous preimage of the open ray `[0,1)`
  (`isOpen_Iio.preimage (continuous_norm.comp continuous_eval)`).
- `measurableSet_sublevelSet` — `IsOpen.measurableSet`.
- `sublevelSet_subset_closedBall : Sₚ ⊆ closedBall 0 2` — if `‖z‖ > 2` then each
  factor `‖z - zᵢ‖ ≥ ‖z‖ - ‖zᵢ‖ ≥ ‖z‖ - 1 > 1`, so `‖p(z)‖ = ∏‖z-zᵢ‖ ≥ 1`.
- `isBounded_sublevelSet` — `Bornology.IsBounded` via subset of `closedBall`.

### Key findings / reusable Lean recipe
- **`Finset.one_le_prod'` does NOT apply to ℝ** — it needs `MulLeftMono ℝ`, which
  fails because ℝ's multiplication is not `≤`-monotone (negatives flip it). For
  "product of nonneg reals each `≥ 1` is `≥ 1`", use `Finset.prod_le_prod`
  against the constant-`1` product: `(1 : ℝ) = ∏ _i, 1 ≤ ∏ i, f i` via
  `Finset.prod_const_one` + `Finset.prod_le_prod (0 ≤ 1) (1 ≤ f i)`.
- **`norm_prod`** rewrites `‖∏ i, f i‖ = ∏ i, ‖f i‖` for ℂ (normed field).
- **`norm_sub_norm_le z w : ‖z‖ - ‖w‖ ≤ ‖z - w‖`** is the reverse-triangle form
  needed for the per-factor lower bound.
- `Complex.abs` here is the parent's local compat def `= ‖·‖`, so
  `P.roots_in_disk i : Complex.abs (roots i) ≤ 1` is defeq to `‖roots i‖ ≤ 1` and
  `hz : z ∈ sublevelSet` is defeq to `‖p(z)‖ < 1` (no rewrite needed).

### Next steps
- **Finiteness of `sublevelMeasure`**: `Sₚ` is a bounded measurable set, so its 2D
  Lebesgue measure is finite. The parent's `sublevelMeasure` is defined on the
  `ℝ×ℝ` copy `{p | Complex.abs (P.eval ⟨p.1,p.2⟩) < 1}`; connect it to `Sₚ ⊆ ℂ`
  via the `Complex.equivRealProdCLM`/`measurableEquivRealProd` measure iso, then
  `measure_lt_top` from boundedness. (Session-sized but fiddly — the ℂ≅ℝ² measure
  bridge is the main friction.)
- **Pólya's `π` upper bound** and the deep KLR `c/log n` lower bound remain out of
  scope (potential theory, not in Mathlib) — isolate KLR as a single named
  assumption when the gallery entry is upgraded.

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

## Session 2026-07-20 (researcher-1) — bare stub → axiom-free foundational core

**Mode**: FRESH (knowledge score 0). **Outcome**: progress (6 theorems, axiom-free), host-verified v4.31.

**Finding**: `Erdos116Problem.lean` had real definitions but **zero theorems**, yet the gallery
meta (`proofStrategy`, `conclusion`) described "four bounds stated as axioms" and a main theorem
`ErdosProblem116` — none of which existed in the source (an overclaim). Fixed both the Lean file and
the prose.

**Added (proofs/Proofs/Erdos116Problem.lean, all 0-axiom, `#print axioms` = propext/Classical.choice/Quot.sound):**
- `UnitDiskPoly.eval_root_eq_zero` — `p(zᵢ)=0` (a factor vanishes); proof `Finset.prod_eq_zero (mem_univ i) (by simp)`.
- `UnitDiskPoly.root_mem_sublevelSet` — every root ∈ `{|p|<1}` (|0|=0<1).
- `UnitDiskPoly.sublevelSet_nonempty` (n>0) — witness `roots ⟨0,hn⟩`.
- `UnitDiskPoly.eval_of_degree_zero` — `n=0 ⟹ p ≡ 1` (empty product).
- `UnitDiskPoly.sublevelSet_of_degree_zero` — `n=0 ⟹ {|p|<1} = ∅` (|1|=1 ≮ 1). The boundary case
  making the `n>0` hypothesis essential.
- `UnitDiskPoly.sublevelMeasure_nonneg` — `0 ≤ μ` (`ENNReal.toReal_nonneg`).

**Gotcha**: file has no namespace (`namespace: null`); shim `noncomputable def Complex.abs (z) := ‖z‖`
for v4.31 (`Complex.abs` removed). `simp [Complex.abs]` unfolds the shim; `Complex.abs 0` → `‖0‖` → `0`.

**Meta synced**: theoremCount 0→6 (both `.meta` and `.leanFile`), lineCount 74→124, imports→`["Mathlib"]`,
`assumptions`/`proofStrategy`/`conclusion` rewritten to stop referencing non-existent axioms/`ErdosProblem116`.

**Still open (Mathlib infra gap)**: the four deep bounds (Pommerenke `c/n⁴`, KLR `c/log n` & `C/loglog n`,
Pólya `π`) need logarithmic-potential / planar-measure-of-lemniscate machinery absent from Mathlib v4.31.
Next foundational step: prove `sublevelSet` is open/measurable (`p` continuous).

## Session 2026-07-20 (researcher-1) — finiteness / well-definedness of sublevelMeasure

**Mode**: build on Key lemma 1 (open/measurable/bounded). **Outcome**: progress — 3
axiom-free theorems, **host-verified v4.31** (`lake env lean` exit 0; `#print axioms` =
`[propext, Classical.choice, Quot.sound]` on all three; no sorry/native_decide).

The parent (`Erdos116Problem.lean`) defines
`sublevelMeasure P := (volume {p:ℝ×ℝ | Complex.abs (P.eval ⟨p.1,p.2⟩) < 1}).toReal`.
This `.toReal` is only faithful when the underlying `volume` is finite (otherwise `⊤`
truncates to `0`). This session discharges that finiteness:

- `volume_sublevelSet_lt_top` — `volume Sₚ < ⊤` on the ℂ side: `Sₚ ⊆ closedBall 0 2`
  (previous session), the closed ball is compact in the proper space `ℂ`, and `volume`
  is finite on compacts (`isCompact_closedBall` + `IsCompact.measure_lt_top`, then
  `measure_lt_top_of_subset`).
- `realProd_sublevelSet_eq_preimage` — the parent's `ℝ×ℝ` set equals
  `Complex.measurableEquivRealProd.symm ⁻¹' Sₚ` (the inverse equiv sends `(a,b) ↦ {re:=a,im:=b}`).
- `volume_realProd_sublevelSet_lt_top` — the parent's planar measure is finite, obtained by
  transporting via `Complex.volume_preserving_equiv_real_prod.symm` +
  `MeasurePreserving.measure_preimage` (needs `NullMeasurableSet`, from
  `measurableSet_sublevelSet.nullMeasurableSet`) down to the ℂ-side bound.

**Now saturated**: the elementary topology + measure-theoretic well-definedness layer
(open, measurable, bounded, finite planar measure). Remaining targets are the deep
quantitative bounds — Pólya `π` upper bound and KLR `c/log n` lower bound — which rest on
logarithmic-potential / area-of-lemniscate machinery absent from Mathlib.

## Session 2026-07-22 (researcher-1): exact areas at the extremal configuration

- `p(z) = zⁿ` (all roots 0) has lemniscate exactly the open unit disk: `‖zⁿ‖ = ‖z‖ⁿ < 1
  ↔ ‖z‖ < 1` (`pow_lt_one_iff_of_nonneg`, needs `n ≠ 0`). Area = π on the nose via
  `Complex.volume_ball` (`= .ofReal r ^ 2 * NNReal.pi`, simp closes at r = 1), then the
  usual `ℂ ≃ᵐ ℝ × ℝ` volume-preserving transport to the parent's `sublevelMeasure`.
- Degree 1: `{z : ‖z - z₀‖ < 1} = ball z₀ 1` (just `dist_eq_norm`), so the area
  functional is constant π over the whole root disk at n = 1.
- `exists_sublevelMeasure_eq_pi (hn : n ≠ 0) : ∃ P, sublevelMeasure P = Real.pi` —
  formalizes that the conjectured maximizer attains π at every degree.
- Lean idiom: membership in `sublevelSet` is defeq to `‖P.eval z‖ < 1` (the parent's
  `Complex.abs` compat def unfolds by `rfl`); `show ‖_‖ < 1` converts cleanly.

## Session 2026-07-24 (researcher-3): the extremal quantity minLemniscateArea

**Outcome**: the EHP extremal function `A(n) = ⨅ P, sublevelMeasure P` formalized
(`minLemniscateArea`), with `Nonempty (UnitDiskPoly n)` instance (`allRootsZero`),
two-sided pinning `π/(4·9^{n−1}) ≤ A(n) ≤ π` (n ≥ 1), `0 < A(n)`, and exact values
`A(0) = 0`, `A(1) = π` (degree-1 constancy proved for ARBITRARY `P : UnitDiskPoly 1`
via `Fin.prod_univ_one`-style `eval_degree_one`, avoiding structure-eta equality with
`singleRoot`). Deep bounds stated as axiom-free named Props (`PommerenkeLowerBound`,
`KLRLowerBound`, `KLRUpperBound`) + machine-checked `KLR ⟹ Pommerenke` implication.

Lean idioms: `ciInf_le`/`le_ciInf` with `BddBelow (Set.range ...)` = `⟨0, by rintro x
⟨P, rfl⟩; exact sublevelMeasure_nonneg P⟩` (parent already has `sublevelMeasure_nonneg`
— do NOT redeclare, name clash). `gcongr` handles `min c π / n⁴ ≤ c / log n` in one
step given `hc0 : 0 ≤ c`, `hlogpos : 0 < log n`, `hlog_le : log n ≤ n⁴` in context
(leaves only `min c π ≤ c`). `Complex.abs 1`: `map_one` does NOT fire (abs is a compat
def, not bundled) — coerce membership defeq to `‖·‖` and use `norm_one`.
