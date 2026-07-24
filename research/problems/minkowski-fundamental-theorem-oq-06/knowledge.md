# Knowledge Base: minkowski-fundamental-theorem-oq-06

Insights accumulated during research on this problem.

---

## Problem Understanding

The **Minkowski–Hlawka theorem** is the non-constructive *existence* counterpart to the
gallery's parent (Minkowski's convex-body *obstruction* theorem). It asserts the densest
lattice packing in dimension `n ≥ 2` has density

    δ_n ≥ ζ(n) / 2^(n-1)

equivalently: every symmetric bounded measurable `S` with `vol(S) < 2·ζ(n)` is avoided
(off the origin) by some unimodular lattice. The standard proof averages
`#(Λ ∩ S \ {0})` over the space of unimodular lattices `X_n = SL_n(ℤ)\SL_n(ℝ)` via
**Siegel's mean-value theorem** and extracts a better-than-average lattice — without
exhibiting one.

---

## Insights

### Session 2026-06-14 (ORIENT) — gap audit + constants pinned

**Mode**: FRESH · **Outcome**: ORIENT (survey, effectively blocked for full proof)

**What I did**
- Confirmed Hlawka is *not* in the gallery: only the obstruction parent exists
  (`MinkowskiFundamentalTheorem.lean`, sorry-free, proves a different theorem). `grep -i
  hlawka proofs/` hits only `Erdos997Problem.lean` (unrelated).
- Audited Mathlib at pin `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`:
  `MeasureTheory/Group/GeometryOfNumbers.lean` contains only **Blichfeldt**
  (`exists_pair_mem_lattice_not_disjoint_vadd`) and **Minkowski convex-body**
  (`exists_ne_zero_mem_lattice_of_measure_mul_two_pow_{lt,le}_measure`). No Siegel
  mean-value (`gh search` = 0), no packing density (`gh search packingDensity` = 0).
  "Minkowski–Hlawka theorem" is a **title-only** entry in Mathlib `docs/1000.yaml` (no
  `decl:`/`author:`) → an *unmet* target upstream.
- Wrote a durable numerical artifact `verify_minkowski_hlawka.py` (all checks pass).

**Key findings**
- **Normalization (correction to seed).** For *symmetric* `S` the threshold is
  `vol(S) < 2·ζ(n)`, not `< ζ(n)`. Chain: take `S = ball(2r)`; an avoiding unimodular
  lattice has min distance `≥ 2r`, so radius-`r` balls pack with density
  `vol(ball r) = vol(S)/2^n = 2ζ(n)/2^n = ζ(n)/2^(n-1)`. The seed's `< ζ(n)` is the
  star-body / ±-identified convention.
- **Bound hierarchy** (verified n ∈ {2..8, 24}): `2^(-n) ≤ ζ(n)/2^(n-1) ≤ δ_n^known`
  (A2, D3, D4, D5, E6, E7, E8, Leech). MH is a valid but very weak lower bound vs known
  optima (e.g. n=8: MH `0.00784` vs E8 `0.2537`).
- **Improvement factor.** `MH / trivial = 2ζ(n) → 2` as `n→∞`. So Hlawka beats the
  elementary maximal-packing bound `δ_n ≥ 2^(-n)` by only ~a factor of 2; both decay like
  `2^(-n)` and the exponential gap to the (also exponential) Kabatiansky–Levenshtein
  *upper* bound is untouched.

**Decision: SURVEY / effectively BLOCKED for full proof.** The standard route requires
Siegel's mean-value theorem over `SL_n(ℝ)/SL_n(ℤ)` (>1000 LOC of missing measure theory).

**Actionable next targets** (both Docker-gated):
1. *Staged*: state Hlawka with Siegel's identity as an explicit hypothesis
   (axiom/structure field), then prove "better-than-average ⇒ existence" with ±-pairing →
   `δ_n ≥ ζ(n)/2^(n-1)`. Isolates the one deep lemma; badge=axiom, status=axiomatized.
2. *Elementary stepping stone* (~200–400 LOC, Mathlib-only): the saturation bound
   `δ_n ≥ 2^(-n)` via maximal packing + radius-doubling cover. The "easy constant" that MH
   sharpens by `2ζ(n)`.

**Files**: `verify_minkowski_hlawka.py`, `src/data/research/problems/minkowski-fundamental-theorem-oq-06.json`.

---

### Session 2026-06-14 (ORIENT, continued) — where the `ζ(n)` factor comes from

**Mode**: REVISIT · **Outcome**: ORIENT (mechanism sharpened; full proof still Docker-gated)

**Correction to the prior session.** The prior notes attribute the `2·ζ(n)` improvement
to "±-pairing + threshold" without separating the two factors. This conflates two
*independent* inputs, and it mis-states the hypothesis the staged formalization (target #1)
must assume. The decomposition is:

- The **factor 2** is the elementary **±-pairing**: for symmetric `S` (with `0 ∉ S`) the
  primitive vectors of a lattice in `S` come in `±w` pairs, so #pairs = #primitive / 2.
- The **factor ζ(n)** is the **primitive-vector (Siegel–Rogers) restriction** — a *deeper*
  input, not a packaging trick. It is the content of the **primitive** mean-value formula,
  distinct from Siegel's all-vectors formula.

**The two mean-value formulas.** On `X_n = SL_n(ℤ)\SL_n(ℝ)` with probability Haar `μ`:

- Siegel (all nonzero vectors): `∫_{X_n} Σ_{v∈Λ\0} f(v) dμ = ∫_{ℝⁿ} f`.
- Siegel–Rogers (**primitive** vectors only): `∫_{X_n} Σ_{w∈Λ primitive} f(w) dμ = (1/ζ(n))·∫_{ℝⁿ} f`.

The second follows from the first by the unique factorization `v = m·w` (`m ≥ 1`, `w`
primitive) and the scaling `∫ f(m·) = m^{-n} ∫ f`: if the primitive mean is `c·∫f` then
`c·(Σ_{m≥1} m^{-n})·∫f = ∫f`, i.e. `c = 1/Σ_{m≥1} m^{-n} = 1/ζ(n)`. **So `ζ(n)` is exactly
`Σ_{m≥1} m^{-n}` — it enters as the primitivity-restriction normalizer, full stop.**

**The Hlawka density argument, correctly stated.** Apply the *primitive* formula to
`f = 1_S`, `S` symmetric, `0 ∉ S`. Mean number of primitive `±`-pairs in `S` is
`vol(S)/(2ζ(n))`. If `vol(S) < 2ζ(n)`, the mean `< 1`, so **some** unimodular `Λ` has no
primitive vector in `S`. For the ball case this finishes, because the **shortest** nonzero
lattice vector is always primitive — "no primitive vector in `ball(2r)`" ⇒ min-distance
`≥ 2r` ⇒ packing density `≥ ζ(n)/2^(n-1)`.

**Consequence for target #1 (staged formalization).** The hypothesis to assume is the
**primitive** mean-value identity `∫_{X_n} Σ_{w primitive} f(w) dμ = (1/ζ(n))·∫ f`, **not**
the all-vectors Siegel identity. Assuming the all-vectors identity and trying to recover
`ζ(n)` by ±-pairing alone does **not** reach `ζ(n)/2^(n-1)` — it only reaches the factor 2,
i.e. `δ_n ≥ 1/2^(n-1)`, missing the `ζ(n)`. Also record: the "shortest vector is primitive"
lemma is the bridge from "no primitive vector in `S`" to "no nonzero vector in `S`" for the
ball; in Mathlib terms it is `Λ`-vector `= m • w` with `‖w‖ < ‖m • w‖` for `m ≥ 2`,
contradicting minimality. (This bridge **is** Mathlib-tractable, unlike the mean-value identity.)

**Durable artifact**: `verify_primitive_mechanism.py` (stdlib-only, all checks pass):
(1) `ζ(n) = Σ_{m≥1} m^{-n}` so `c = 1/ζ(n)`; (2) `ℤ²` fraction of primitive (origin-visible,
`gcd=1`) points `→ 1/ζ(2) = 6/π²`; (3) `ℤ³` primitive fraction `→ 1/ζ(3)`; (4) deterministic
sweep of 13808 integer 2×2 bases: shortest nonzero vector is primitive in **all** cases.

**Files**: `verify_primitive_mechanism.py`, `src/data/research/problems/minkowski-fundamental-theorem-oq-06.json`.

---

## Dead Ends

- Full formalization via Siegel's mean-value theorem from current Mathlib — blocked: the
  homogeneous space `SL_n(ℤ)\SL_n(ℝ)`, its finite invariant measure, and Siegel's identity
  are all absent upstream.

## Session 2026-07-24 (researcher-3): ACT — staged target #1 executed, Docker back

Docker was available again; the staged plan from the two ORIENT sessions is now Lean.
New file `MinkowskiFundamentalTheoremOQ06.lean` (273 lines, 10 theorems, 3 defs,
0 axioms, 0 sorries; headline theorems `#print axioms` = foundational only).

**Unconditional (Mathlib-only):**
- `zetaSum n := ∑' m : ℕ, 1/(m:ℝ)^n` — the m=0 term VANISHES by the div-zero
  convention, so no ℕ+ reindexing; `Real.summable_one_div_nat_pow` for n ≥ 2;
  `one_le_zetaSum` via `Summable.le_tsum` at m=1 (do NOT rw a `1 = 1/1^n` identity —
  it leaks into the tsum body; use `simpa [zetaSum] using h`).
- `IsPrimitive L v` (v ∈ L, v ≠ 0, no m•w factorization with m ≥ 2, w ∈ L).
- `minimal_isPrimitive` — the "shortest vector is primitive" bridge flagged in the
  prior ORIENT note.
- `exists_primitive_norm_le` — STRONGER bridge: uniform discreteness (r₀ ≤ ‖u‖ for
  nonzero u ∈ L) ⟹ below every nonzero v sits a primitive w, ‖w‖ ≤ ‖v‖. Norm-halving
  descent by strong induction on k with ‖v‖ ≤ k·r₀; the uniform step
  `2‖w‖ ≤ ‖v‖ ≤ (k+1)r₀ ∧ r₀ ≤ ‖w‖ ⟹ ‖w‖ ≤ k·r₀` avoids any case split (nlinarith).
- `no_nonzero_of_no_primitive_in_ball` — contrapositive bridge form Hlawka needs.
- `exists_count_zero_of_integral_lt_one` — ℕ-valued RV with mean < 1 vanishes
  somewhere (integral_mono against const 1; new Mathlib `integral_const` produces
  `μ.real univ • 1` — close with plain `simp at hint1`, not `rw [measure_univ]`).

**Staged (explicit hypotheses, NOT axioms):**
- `hlawka_avoidance`: family latticeOf : Ω → AddSubgroup (EuclideanSpace ℝ (Fin n))
  over a probability space + hMV (primitive mean-value = vol/ζ(n)) + hInt + hFin ⟹
  vol S < ζ(n) → some lattice has NO primitive vector in S.
- `hlawka_ball`: + uniform discreteness fields ⟹ min-distance ≥ r conclusion.
- `hFin` is forced by the `Set.ncard` junk value (infinite set ↦ 0); an honest model
  must supply finiteness. Next rung: prove hFin from discreteness + boundedness
  (r₀-separated subset of a bounded set is finite — genuine Mathlib exercise).

**Deliberately NOT staged**: the ±-pairing refinement (threshold 2ζ(n), density
ζ(n)/2^{n-1}) — the unpaired primitive identity with threshold ζ(n) matches the
problem.md pinned statement; pairing is a separate arithmetic layer.

**Verification**: typechecked host-side via sibling worktree toolchain
(researcher-1/proofs, `./bin/lake env lean` on absolute path — works for
Mathlib-only files); Docker module build green.

**Ops incident**: the researcher-3 worktree was janitor-reaped MID-SESSION (disk was
fine, 3.3Ti free); recreated via `worktree add -B research/minkowski-oq06-hlawka-skeleton`
+ restored the file from /tmp backup. Commit+push immediately after any file creation.

### Frontier
- Finiteness rung: `(S ∩ Primitives).Finite` from uniform discreteness + bounded S.
- Pairing rung: symmetric S ⟹ primitive count is even (±-pairs), threshold 2ζ(n).
- Density rung: min-distance ≥ r ⟹ packing of radius-r/2 balls (needs a packing-
  density formalization — assess before attempting).
- The mean-value identity itself: SL_n(ℤ)\SL_n(ℝ) Haar theory — DEEP, blocked
  (registry entry unchanged).
