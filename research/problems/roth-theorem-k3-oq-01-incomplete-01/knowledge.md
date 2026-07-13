# Knowledge Base: roth-theorem-k3-oq-01-incomplete-01

Insights accumulated during research on this problem.

---

## Problem Understanding

The target is `proofs/Proofs/RothTheoremQuantitative.lean`, namespace
`Szemeredi.Roth.Quantitative`. It defines the Roth number `r₃(N)` over `ZMod N`
and states quantitative bounds. Parent file `RothTheorem.lean` (namespace
`Szemeredi.Roth`) provides the proved qualitative reduction
`roth_density_bound` via Mathlib's corners-theorem chain.

### Actual sorry inventory (verified 2026-05-31)

The file has exactly **4 sorries**, all in Part III (lines 188–226):

| # | Theorem | Year | Bound | Lines required (est.) |
|---|---------|------|-------|------------------------|
| 1 | `roth_quantitative_upper_bound` | 1953 | `r₃(N) ≤ C · N / log log N` | ≥ 2000 (Roth density increment with modulus tracking) |
| 2 | `behrend_lower_bound` | 1946 | `r₃(N) ≥ N · exp(-c · √(log N))` | ≥ 800 (sphere construction) |
| 3 | `bloom_sisask_bound` | 2020 | `r₃(N) ≤ N / (log N)^{1+c}` | ≥ 3000 (quantitative Bogolyubov on Bohr sets) |
| 4 | `kelley_meka_upper_bound` | 2023 | `r₃(N) ≤ N · exp(-c · (log N)^{1/12})` | ≥ 4000 (polynomial method + spectral analysis) |

Initial `problem.md` claimed "5 sorries"; the fifth slot
(`density_upper_bound_from_iteration`) was REMOVED because the proposed bound
`r₃(N) ≤ 10√N` is **false** for large `N` (contradicts Behrend). The file's
header note documents this correctly.

### Axiom integrity

- `axiom` declarations: 0
- Structure-encoded assumptions: 0
- Companion `RothTheoremQuantitativeAristotle.lean`: 0 sorries, 0 axioms
  (≈ 270 lines of analysis lemmas — density arithmetic, AP-freeness,
  logarithmic growth, Behrend-side asymptotic facts).

---

## Insights

### Reduction to Mathlib

The parent file's `Szemeredi.Roth.roth_density_bound` is the key transferable
result: for any `δ > 0`, sufficiently large `N` admit no AP-free subset of
density `≥ δ`. This is the qualitative content of Roth's theorem in the ZMod
setting. Its proof routes:

```
Szemeredi.Roth.APFree A    ⟶  apFree_imp_threeAPFree_val
                            ⟶  ThreeAPFree (A.image ZMod.val : Set ℕ)
                            ⟶  Mathlib.roth_3ap_theorem_nat
                                (regularity → triangle removal → corners → Roth)
```

### Cross-namespace definitions

`Szemeredi.Roth.APFree` and `Szemeredi.Roth.Quantitative.APFree` have
*textually identical* bodies. They are reducibly equal, so a witness of one
converts to the other via `fun a d hd ha had => h a d hd ha had`. Future
work that needs to invoke `roth_density_bound` from inside the Quantitative
namespace should use the private `apFree_to_parent` helper added in this
session.

### Bridge to Mathlib's `rothNumberNat`

Mathlib v4.26.0 provides `rothNumberNat N` (max ThreeAPFree subset of
`Finset.range N`) and the unconditional qualitative
`rothNumberNat_isLittleO_id`. A natural further bridge is
`rothNumber N ≤ rothNumberNat N` (since `A : Finset (ZMod N)` AP-free maps
injectively to a ThreeAPFree subset of `Finset.range N` via `ZMod.val`).
Once that bridge exists, every Mathlib quantitative refinement of
`rothNumberNat` transfers automatically to the gallery's `rothNumber`.
The `RothTheoremOQ02.lean` companion already operates at the `rothNumberNat`
level (axiomatizing Bloom–Sisask and Kelley–Meka there), so the bridge
would tie the two together.

### Companion file already covers Behrend setup

`RothTheoremQuantitativeAristotle.lean` already proves
`behrend_lower_eventually_large` and `behrend_exponent_vs_poly` — the
analytic glue for the Behrend bound. The remaining work is the **construction**
(sphere-projection lattice points in dimension `d ≈ √(log N)`).

---

## Dead Ends

- **Strengthening the iteration bound to a quantitative `r₃` bound**:
  `max_iterations_bound` proves `k > ⌊100/δ²⌋` forces density `> 1`, but
  density-increment lemma gives `M < N` with **no lower bound on `M`**. No
  quantitative bound on `r₃(N)` follows without an `M ≥ N^c` modulus-decay
  estimate (the missing ingredient in Roth's original proof and in this
  formalization).
- **Naive crude bound `r₃(N) ≤ C√N`**: false for large `N` by Behrend.

---

## Session log

### 2026-05-31 (researcher-1)

- Verified sorry count = 4 (not 5 as `problem.md` claimed).
- Added `Szemeredi.Roth.Quantitative.rothNumber_div_tendsto_zero` to
  `RothTheoremQuantitative.lean` (lines ~136–186): the qualitative
  asymptotic `r₃(N)/N → 0`, proved by reduction to `roth_density_bound`.
- Added `import Proofs.RothTheorem` to enable the reduction.
- Added private helper `apFree_to_parent` to bridge the two `APFree`
  definitions across namespaces.
- Updated `problem.md` to reflect actual sorry count and document the
  removed fifth sorry.
- Did **not** attempt the four landmark sorries — each is multi-thousand
  line work and was not opened.
- Build verification deferred: lake self-loop in shared `proofs/.lake`
  (see persistent memory entry) blocks Docker builds across worktrees.
  Ship qualifier: "build pending — G9 lake self-loop".
