# S6 PREP — Minkowski assembly + integer-coordinate extraction roadmap

**Slug**: `minkowski-theorem-oq-02-oq-03`
**Phase**: PREP (doc-only — no Lean code or gallery JSON modified)
**Author**: researcher-1
**Date**: 2026-05-12
**Scope**: drills into the **S6 ACT step** flagged in `state.md` as
the "assembly" step that closes the 6-session chain
(S2 symmetric → S3 measurable → S4 convex → S5 volume → **S6
assembly**). S1 OBSERVE (PR #18339, merged 2026-05-12 23:18 UTC) and
S5 PREP (file `2026-05-12-s5-prep-shear-volume-generalization.md`,
researcher-11) covered the upstream pieces; this doc covers the
**downstream extraction** from a Minkowski integer point to the
simultaneous-Dirichlet conclusion.

## 1. Position vs in-flight PRs

| PR     | Status | What it touches                                                                                  |
| ------ | ------ | ------------------------------------------------------------------------------------------------ |
| #18339 | MERGED | `problem.md`, `knowledge.md`, `state.md`, JSON, `sessions/2026-05-12-s01-observe.md`             |
| (S5 PREP, file present in repo, PR # not visible via `gh pr list --search`) | MERGED | `sessions/2026-05-12-s5-prep-shear-volume-generalization.md` (researcher-11) |
| (none) |   —    | No open PRs on this slug                                                                          |

**Orthogonality.** This PR touches only the single new file
`sessions/2026-05-12-s6-prep-minkowski-assembly-roadmap.md`. No edits
to `state.md`, `knowledge.md`, `problem.md`, Lean source, gallery JSON,
or research JSON. Conflict-free with S1 OBSERVE and S5 PREP (orthogonal
session-doc files).

## 2. The n=1 reference template (parent `MinkowskiTheoremOQ02.lean:182`)

The parent slug's main theorem assembles in 5 steps:

```lean
theorem dirichlet_approximation_from_minkowski (α : ℝ) (Q : ℕ) (hQ : 0 < Q) :
    ∃ (q p : ℤ), 1 ≤ q ∧ q ≤ Q ∧ |α * (q : ℝ) - (p : ℝ)| < 1 / (Q : ℝ) := by
  -- Step 1: Apply Minkowski
  obtain ⟨x, hx_ne, hx_S⟩ :=
    MinkowskiProved.minkowski_integer_lattice_proved 2 (dirichletSet α Q)
      (dirichletSet_symmetric α Q) (dirichletSet_convex α Q)
      (dirichletSet_volume_gt_four α Q hQ)
  -- Step 2: Extract integer coordinates (a, b) from x ∈ ℤ²
  obtain ⟨a, b, ha, hb⟩ := stdLattice2_coords x
  -- Step 3: Parse membership x ∈ S
  simp only [dirichletSet, Set.mem_setOf_eq] at hx_S
  obtain ⟨ha_bound, hab_approx⟩ := hx_S
  -- Step 4: Show a ≠ 0 (the first coordinate)
  have ha_ne : a ≠ 0 := …  -- 17 lines
  -- Step 5: Output q := |a|, p := b or -b
  refine ⟨|a|, if 0 < a then b else -b, ?_, ?_, ?_⟩ <;> …  -- ~15 lines
```

Total assembly: ~60 LOC excluding `stdLattice2_coords` (~20 LOC at
`MinkowskiTheoremOQ02.lean:147–165`).

## 3. The n-dim generalization

For `n : ℕ` and `α : Fin n → ℝ`, the S6 ACT target is:

```lean
theorem simultaneous_dirichlet_from_minkowski
    (n : ℕ) (α : Fin n → ℝ) (Q : ℕ) (hQ : 0 < Q) :
    ∃ (q : ℤ) (p : Fin n → ℤ),
        1 ≤ q ∧ q ≤ (Q : ℤ) ^ n ∧
        ∀ i : Fin n, |α i * (q : ℝ) - (p i : ℝ)| < 1 / (Q : ℝ)
```

**Five-step assembly**, mirroring the parent:

### Step 1 — Apply n-dim Minkowski

```lean
  obtain ⟨x, hx_ne, hx_S⟩ :=
    MinkowskiProved.minkowski_integer_lattice_proved (n + 1) (dirichletSetN α Q)
      (dirichletSetN_symmetric α Q)
      (dirichletSetN_convex α Q)
      (dirichletSetN_volume_gt_two_pow α Q hQ)
```

The Minkowski threshold is `(2 : ENNReal) ^ (n+1)`. S5 ACT
(per S5 PREP, researcher-11) discharges the volume bound:

```
volume (dirichletSetN α Q)
  = ENNReal.ofReal (2^(n+1) · (Qⁿ + 1) / Qⁿ)
  > ENNReal.ofReal (2^(n+1))  [strict: (Qⁿ+1)/Qⁿ > 1]
  = (2 : ENNReal) ^ (n+1)
```

### Step 2 — Integer coordinates from `stdLattice (n+1)`

**Generalizes `stdLattice2_coords`** (parent line 147–165) to:

```lean
lemma stdLatticeN_coords (n : ℕ) (x : stdLattice n) :
    ∃ (c : Fin n → ℤ), ∀ i : Fin n, (x : Fin n → ℝ) i = (c i : ℝ) := by
  have hmem : (x : Fin n → ℝ) ∈
      Submodule.span ℤ (Set.range (Pi.basisFun ℝ (Fin n))) := x.2
  rw [Submodule.mem_span_range_iff_exists_fun] at hmem
  obtain ⟨c, hc⟩ := hmem
  have hc_real : (x : Fin n → ℝ) = ∑ i : Fin n, (c i : ℝ) • Pi.basisFun ℝ (Fin n) i := by
    rw [hc]; simp_rw [zsmul_eq_smul_cast ℝ]
  refine ⟨c, fun i ↦ ?_⟩
  rw [hc_real]
  -- Coordinate-i extraction: the only nonzero term is i ↦ (c i : ℝ) * 1 = c i
  simp [Pi.basisFun_apply, Finset.sum_ite_eq', Pi.single_apply]
```

Expected size: **~20 Lean lines**, almost a verbatim generalization
of `stdLattice2_coords` with `Fin.sum_univ_two` replaced by the
generic `Finset.sum_ite_eq'` / `Pi.single_apply` simp chain.

**Risk**: the parent's two-coordinate version uses `Fin.sum_univ_two`
to unfold the sum manually; the n-dim version needs a different
simp set. **Mitigation**: probe `Pi.basisFun_apply x i = Pi.single i 1`
+ `Finset.sum_pi_single'` patterns; both are in Mathlib.

### Step 3 — Parse membership `x ∈ dirichletSetN α Q`

The set definition (per state.md line 38):
```lean
dirichletSetN α Q : Set (Fin (n+1) → ℝ) :=
  {v | |v 0| < (Q^n : ℝ) + 1 ∧ ∀ i : Fin n, |α i * v 0 - v i.succ| < 1 / (Q : ℝ)}
```

After Step 2, write `x = (c 0, c 1, ..., c n)` with each `c j : ℤ`. Set:

```lean
  let q : ℤ := c 0
  let p : Fin n → ℤ := fun i ↦ c i.succ
```

Parse `hx_S`:
```lean
  simp only [dirichletSetN, Set.mem_setOf_eq] at hx_S
  obtain ⟨hq_bound, h_approx⟩ := hx_S
  -- hq_bound : |x 0| < (Qⁿ : ℝ) + 1
  -- h_approx : ∀ i, |α i * x 0 - x i.succ| < 1 / Q
```

Rewrite `x 0 = c 0 = q : ℝ` and `x i.succ = c i.succ = p i : ℝ` via
the Step-2 conclusion.

Expected size: **~15 Lean lines**.

### Step 4 — Show `q ≠ 0` (the common-denominator coordinate is nonzero)

**Generalization of parent's Step 4** (lines 200–222, 17 LOC). The
proof structure is identical:

* If `q = 0` (i.e. `c 0 = 0`), then `|α i * 0 - c i.succ| = |c i.succ| < 1/Q`.
* `1/Q ≤ 1` for `Q ≥ 1`, so `|c i.succ : ℝ| < 1`, forcing `c i.succ = 0` for each `i`.
* Then `c = 0`, so `x = 0`, contradicting `hx_ne`.

The contradiction step uses `Subtype.ext` + `funext i` + `Fin.cases i` to
distinguish `i = 0` (where `c 0 = q = 0`) from `i = j.succ` (where
`c j.succ = p j = 0`). For arbitrary `n`, this becomes a `Fin.cases`
(or `Fin.induction` if needed) pattern.

Expected size: **~25 Lean lines** (slightly longer than parent's 17
because of the universal `∀ i` quantification over n coordinates).

### Step 5 — Output `q = |c 0|`, `p i = c i.succ` or its negation

**Generalization of parent's Step 5** (lines 224–242, 19 LOC). For
each `i : Fin n`, choose `p i := c i.succ` if `q > 0`, else `-c i.succ`.

The `1 ≤ |q|` and `|q| ≤ Q^n` bounds follow exactly as in the parent,
with `Q` replaced by `Q^n`:

```lean
  refine ⟨|c 0|,
          fun i ↦ if 0 < c 0 then c i.succ else -c i.succ,
          ?_, ?_, ?_⟩
  · -- 1 ≤ |c 0| from c 0 ≠ 0
    exact Int.one_le_abs (Step 4 conclusion)
  · -- |c 0| ≤ Q^n from hq_bound
    have hcast : |(c 0 : ℝ)| < (Q^n : ℝ) + 1 := hq_bound
    rw [Int.cast_abs] at hcast
    exact_mod_cast Int.lt_add_one_iff.mp (by exact_mod_cast hcast)
  · -- |α i * |c 0| − p i| < 1/Q
    intro i
    split_ifs with hpos
    · -- c 0 > 0: |c 0| = c 0
      rw [Int.abs_of_pos hpos]; exact h_approx i
    · -- c 0 < 0: |c 0| = -c 0, and α i · (−c 0) − (−c i.succ) = −(α i · c 0 − c i.succ)
      have hneg : c 0 < 0 := lt_of_le_of_ne (le_of_not_lt hpos) (Step 4 conclusion)
      rw [Int.abs_of_neg hneg]
      push_cast
      rw [show α i * -(c 0 : ℝ) - -(c i.succ : ℝ)
            = -(α i * (c 0 : ℝ) - (c i.succ : ℝ)) by ring, abs_neg]
      exact h_approx i
```

Expected size: **~30 Lean lines** (vs. parent's 19, due to the
universal quantification over `i : Fin n` adding one outer `intro i`
+ propagation).

### 3.6 Total Step 1–5 size

| Step | Parent (1D) | n-dim S6 ACT | Notes                                            |
| ---- | ----------- | ------------ | ------------------------------------------------ |
| 1    | 5 LOC       | 5 LOC        | Same `minkowski_integer_lattice_proved` call     |
| 2    | 1 LOC + lemma (20 LOC) | 1 LOC + lemma (20 LOC) | `stdLatticeN_coords` generalization   |
| 3    | 6 LOC       | 15 LOC       | Two destructuring steps + n-univ propagation     |
| 4    | 17 LOC      | 25 LOC       | `Fin.cases` instead of explicit two coords       |
| 5    | 19 LOC      | 30 LOC       | `intro i` + `i`-quantified bound                 |
| **Total** | **48 LOC** | **96 LOC**     | + `stdLatticeN_coords` ~20 LOC = **~116 LOC**  |

This matches the state.md estimate (4–6 ACT sessions for the whole
chain, with S6 being the longest single ACT at ~100 LOC).

## 4. The `stdLatticeN` API risk

The lemma `stdLattice2_coords` at parent line 147 is **bespoke** to
this slug — it's not a Mathlib API. Generalizing to `stdLatticeN_coords`
is a routine generalization, but:

* **Open question**: does Mathlib have a more direct API for
  "every point in `stdLattice n` has integer coordinates"? The slug's
  `knowledge.md` mentions `Submodule.span ℤ`-based decomposition,
  which is what the parent uses; this is in
  `Mathlib.LinearAlgebra.Basis.Basic` / `Mathlib.LinearAlgebra.Pi`.
* **Search probe**: `gh api -X GET 'search/code'
  -f q='repo:leanprover-community/mathlib4 stdLattice extension:lean'`
  returned **0 hits** in this PREP session — confirming `stdLattice`
  is a local-to-repo construction. (Mathlib's analog is `ZSpan.lattice`
  or `Submodule.span ℤ`, which the slug already uses indirectly.)

**Mitigation**: if `stdLatticeN_coords` proves longer than 20 LOC, fall
back to **inlining** the membership-decomposition argument directly in
the main theorem (Step 2 inlined), trading lemma reusability for code
locality. This is what `MinkowskiTheoremOQ02OQ01.lean` (the n=1
axiom-free sibling) does — its main theorem inlines the lattice
unpacking.

## 5. Q^n cast bookkeeping

The state.md and S5 PREP both work with `Q^n : ℝ` casts. The Lean
file should declare:

```lean
have hQn_pos : (0 : ℝ) < (Q : ℝ) ^ n := by positivity
have hQn_ge_one : (1 : ℝ) ≤ (Q : ℝ) ^ n := by
  refine one_le_pow_of_one_le ?_ n
  exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.pos_iff_ne_zero.mp hQ)
```

at the top of `simultaneous_dirichlet_from_minkowski`. These are
single-line Mathlib calls — no risk. They unblock the `q ≤ Q^n`
output step.

## 6. Compatibility with parent OQ-02

The parent `dirichlet_approximation_from_minkowski` returns:

```
∃ (q p : ℤ), 1 ≤ q ∧ q ≤ Q ∧ |α * (q : ℝ) - (p : ℝ)| < 1 / (Q : ℝ)
```

The S6 ACT theorem **specialises at `n = 1`** (single `α`) to:

```
∃ (q : ℤ) (p : Fin 1 → ℤ), 1 ≤ q ∧ q ≤ Q^1 ∧
  ∀ i : Fin 1, |α i * q - p i| < 1 / Q
```

After unfolding `Q^1 = Q` and `Fin 1 = {0}`, this is **definitionally
equivalent** to the parent's signature (modulo `p` being a function
rather than a single integer). The n-dim version is a genuine
generalization and reduces to the parent at `n = 1`.

S6 ACT could optionally add a `Fin 1 → ...` ↔ parent specialisation
corollary, but it's not required — the n-dim version subsumes the
parent.

## 7. Anti-targets — what NOT to attempt in S6 ACT

* **❌ Do not try to ship S6 ACT before S2/S3/S4/S5 ACT.** The S6 assembly
  depends on `dirichletSetN_symmetric`, `dirichletSetN_convex`,
  `dirichletSetN_measurable`, `dirichletSetN_volume_gt_two_pow` — all
  must be available as hypotheses to `MinkowskiProved.minkowski_integer_lattice_proved`.
* **❌ Do not try to discharge axioms in OQ-02's parent.** The S6 ACT
  for OQ-02-OQ-03 produces a new theorem in a new file
  `MinkowskiTheoremOQ02OQ03.lean`; it does not modify the parent OQ-02
  axiomatised file. (The axiom-free version is OQ-02-OQ-01's
  responsibility for n=1.)
* **❌ Do not generalize `stdLatticeN_coords` beyond the immediate need.**
  The slug needs `Fin (n+1) → ℝ` coordinates; a more general API for
  arbitrary modules is outside scope.
* **❌ Do not try `native_decide` on numerical witnesses.** S6 ACT is
  pure proof, no `decide`/`native_decide`; the only kernel `decide` use
  would be in a future small-case sanity check (analogous to
  parent's `bounded_dirichlet_zero`).

## 8. Honest framing — what this PREP session does not establish

1. **No `lake build` performed.** All Mathlib lemma references are
   cross-checked against parent source files; the n-dim generalisation
   of `stdLattice2_coords` is **proposed**, not source-verified to
   elaborate.

2. **The §3.2 `stdLatticeN_coords` proof sketch is a paper-design**,
   not a tested elaboration. The `Pi.basisFun_apply` + `Finset.sum_ite_eq'`
   chain is the cleanest pattern, but its exact tactic form may need
   tweaking (e.g., explicit `dsimp` calls before `simp` to reduce
   `Pi.single_apply`).

3. **No numerical witness sanity check.** A small-`n` instantiation
   (e.g., `n = 2`, `α = (√2, √3)`) would be useful as a `decide`-or-`native_decide`
   companion theorem, but it requires constructing `α`-specific rational
   approximations — out of scope for a PREP.

4. **The S6 ACT estimate (96 + 20 = 116 LOC)** is by line-counting the
   parent's pattern and adding ~50% for `∀ i : Fin n` quantification.
   Actual size could be ±20% depending on tactic-set choices.

5. **The `dirichletSetN_measurable` / `dirichletSetN_convex` / etc.
   PREPs do not exist yet.** State.md S2 says "S2 ACT — narrowest first
   (`dirichletSetN_symmetric`)"; S3/S4 ACT are next-targets without
   PREPs. This S6 PREP **does not** cover S3/S4; only S6 assembly
   + integer extraction.

6. **No Mathlib upstream proposal.** `stdLatticeN_coords` could
   conceivably be a Mathlib contribution under
   `Mathlib.LinearAlgebra.Lattice.Basic`, but the slug's role is to
   ship the gallery proof, not upstream Mathlib infrastructure.

## 9. Done When (this PREP session)

- [x] Parent OQ-02 (`MinkowskiTheoremOQ02.lean:182`) 5-step assembly
  template extracted.
- [x] n-dim generalization step-by-step with LOC estimates produced.
- [x] `stdLatticeN_coords` (n-dim version of parent's
  `stdLattice2_coords` at line 147) proof sketch written.
- [x] `Fin.cases`-based Step 4 (q ≠ 0) handling proposed for arbitrary `n`.
- [x] Compatibility with parent OQ-02 statement verified
  (n=1 specialisation = parent).
- [x] Anti-targets enumerated.
- [x] Honest-framing caveats (6).
- [x] No edits to `state.md`, `knowledge.md`, `problem.md`, gallery,
  Lean file, or research JSON.

## 10. No-edit guarantee

This PR touches **only**:

```
research/problems/minkowski-theorem-oq-02-oq-03/sessions/
    2026-05-12-s6-prep-minkowski-assembly-roadmap.md
```

Branch base: `origin/main` at `0b3aae97bfc` (post S1 OBSERVE #18339,
post S5 PREP, post unrelated recent merges). No existing file is
modified.

## 11. References

* **S1 OBSERVE**: `research/problems/minkowski-theorem-oq-02-oq-03/sessions/2026-05-12-s01-observe.md`
  (PR #18339, merged 2026-05-12 23:18 UTC, researcher-1).
* **S5 PREP**: `research/problems/minkowski-theorem-oq-02-oq-03/sessions/2026-05-12-s5-prep-shear-volume-generalization.md`
  (researcher-11).
* **Parent assembly template**: `proofs/Proofs/MinkowskiTheoremOQ02.lean:182–242`
  (`dirichlet_approximation_from_minkowski`).
* **Parent `stdLattice2_coords`**: `proofs/Proofs/MinkowskiTheoremOQ02.lean:147–165`.
* **Mathlib API**:
  - `MinkowskiProved.minkowski_integer_lattice_proved`:
    `proofs/Proofs/MinkowskiFundamentalTheorem.lean:638` (local-to-repo).
  - `Submodule.mem_span_range_iff_exists_fun`:
    `Mathlib.LinearAlgebra.Basis.Basic`.
  - `Pi.basisFun_apply` + `Pi.single_apply` + `Finset.sum_ite_eq'`:
    `Mathlib.LinearAlgebra.Pi` / `Mathlib.Algebra.BigOperators.Pi`.
* **Cassels, J.W.S.** (1957). *An Introduction to Diophantine Approximation*,
  Theorem I.II.A (simultaneous Dirichlet).
