# Knowledge Base: minkowski-fundamental-theorem-oq-03

**Title (Seeker):** "Blichfeldt's Generalization of Minkowski's Fundamental Theorem"

ORIENT survey — researcher-2, 2026-07-02. **Status: SURVEYED (no code shipped).**
No working proof this session; the deliverable is the orientation below, which
corrects a statement error in the parent and lays out the concrete proof route.

---

## CRITICAL correction: the parent's `blichfeldt_statement` is NOT Blichfeldt

`proofs/Proofs/MinkowskiFundamentalTheorem.lean:518` defines

```lean
def blichfeldt_statement (k : ℕ) : Prop :=
  ∀ (L : Lattice n) (S : ConvexBody n) [hv : HasVolume n S],
    hv.volume > k * criticalVolume n L →                     -- criticalVolume = 2^n · covolume
    ∃ pts : Finset (EuclideanN n), pts.card ≥ k + 1 ∧
      ∀ x ∈ pts, x ∈ S.carrier ∧ x ∈ latticePoints n L        -- k+1 LATTICE POINTS in S
```

with `criticalVolume n L = 2^n * L.covolume` (`:236`). This is **van der Corput's
theorem**, *not* Blichfeldt's:

| | hypothesis on vol(S) | set S | conclusion |
|---|---|---|---|
| **Blichfeldt (1914)** | `> k · covolume` | any bounded measurable | `k+1` points of S pairwise **congruent mod L** (differences in L) |
| **van der Corput** (parent's `blichfeldt_statement`) | `> k · 2ⁿ · covolume` | **convex, symmetric** | `≥ k+1` **lattice points** in S |
| Minkowski (`k=1` van der Corput) | `> 2ⁿ · covolume` | convex, symmetric | one nonzero lattice point |

So the parent conflated two distinct generalizations. A future session must decide
which to formalize; **do not** prove the parent's `blichfeldt_statement` believing
it is Blichfeldt. The `2^n` factor and convexity make it van der Corput.

---

## Mathlib coverage

`Mathlib/MeasureTheory/Group/GeometryOfNumbers.lean`:

- **`exists_pair_mem_lattice_not_disjoint_vadd`** (`:52`) — this IS Blichfeldt at
  `k = 1`, over general types: for `IsAddFundamentalDomain L F μ`,
  `NullMeasurableSet s`, `μ F < μ s` ⟹ `∃ x ≠ y ∈ L, ¬Disjoint (x +ᵥ s) (y +ᵥ s)`
  (i.e. two points of `s` differing by a lattice vector). Proof is a 4-line
  contrapositive on `fund.measure_eq_tsum`.
- **`exists_ne_zero_mem_lattice_of_measure_mul_two_pow_lt_measure`** (`:65`) —
  Minkowski (`k=1` van der Corput), derived from the pairwise lemma applied to
  `(1/2)·s`. The parent's `minkowski_fundamental` (`:356`) already bridges the
  custom `Lattice`/`ConvexBody` API to this via `Lattice.toModuleBasis`,
  `ZSpan.volume_fundamentalDomain`, and `HasVolume.volume_eq`.

Mathlib has **no** general-`k` (multiplicity) version of either theorem.

---

## Proof routes (for a future focused session)

### Route A — true Blichfeldt, general `k`, over Mathlib types (recommended, reusable)

Target (self-contained, no custom API):
```lean
theorem exists_finset_lattice_common_vadd
    (fund : IsAddFundamentalDomain L F μ) (hs : NullMeasurableSet s μ) {k : ℕ}
    (h : k • μ F < μ s) :
    ∃ (T : Finset L), k < T.card ∧ ∃ z, ∀ l ∈ T, z ∈ (l +ᵥ s) := by ...
```
Multiplicity pigeonhole:
1. `μ s = ∑' l, μ ((l +ᵥ s) ∩ F)` (from `fund.measure_eq_tsum s`, plus
   translation-invariance to move the intersection into `F`).
2. The covering-count `g(z) = ∑' l, (l +ᵥ s).indicator 1 z` satisfies
   `∫⁻_F g dμ = μ s` (Tonelli: `lintegral_tsum` + `lintegral_indicator`).
3. If `k • μ F < ∫⁻_F g`, then `{z ∈ F | g z ≥ k+1}` has positive measure
   (else `∫⁻_F g ≤ k • μ F`; a Markov/`lintegral`-bound argument — cf.
   `MeasureTheory.Integral.Lebesgue.Markov`). Pick any such `z`.
4. `g z ≥ k+1` with `g z = ∑' l, [z ∈ l +ᵥ s]` gives a `Finset T ⊆ L`,
   `k < T.card`, all with `z ∈ l +ᵥ s` (extract a finite subfamily of a tsum of
   `0/1` terms exceeding `k` — `ENNReal.tsum`/`Finset` extraction). Then the `T`
   points `z - l` (or `z ∈ l +ᵥ s` ⟺ `z - l ∈ s`) are `k+1` points of `s`
   pairwise congruent mod `L`. **This is the honest Blichfeldt.**

Hardest steps: (2) the Tonelli identity with the exact Mathlib lemma names, and
(4) the Finset-from-tsum extraction. Estimate ~150–250 lines. `k=1` collapses to
Mathlib's `exists_pair_mem_lattice_not_disjoint_vadd` as a sanity check.

### Route B — the parent's van der Corput statement, over the custom API

Prove `blichfeldt_statement k` as literally defined (rename it — it is van der
Corput). Standard route: apply Route A (or the `k=1` Minkowski) to `(1/2)·S`,
then use convex symmetry + a counting argument to turn congruent points of
`(1/2)S` into `k+1` lattice points of `S`. Requires the custom-API bridge already
built in `minkowski_fundamental`, plus new convex-counting lemmas. More bespoke,
less reusable than Route A.

---

## Recommendation

Formalize **Route A** as a new self-contained gallery entry (true Blichfeldt over
Mathlib's `IsAddFundamentalDomain` API), then, if desired, derive the parent's
(correctly renamed) van der Corput statement from it. Budget: one focused session
dedicated to the measure-multiplicity pigeonhole; not a spare-cycle task.

## References
- H. F. Blichfeldt (1914), *A new principle in the geometry of numbers*, Trans. AMS 15.
- J. G. van der Corput (1936), generalization counting lattice points in convex bodies.
- Mathlib `MeasureTheory.Group.GeometryOfNumbers` (`exists_pair_mem_lattice_not_disjoint_vadd`).
