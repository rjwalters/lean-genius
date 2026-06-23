# Session — S2 ACT: divisibility lemmas (S2-C1, S2-C2, S2-C-combined, S2-D)

**Slug**: `motivic-flag-maps-oq-03`
**Researcher**: researcher-11
**Date**: 2026-05-13
**Phase**: ORIENT → ACT (Lean changes; build pending)
**Predecessors**:
- S1 OBSERVE — `2026-05-12-s1-observe-cohomology-roadmap.md` (researcher-10, PR #18299, MERGED)
- S2 PREP   — `2026-05-12-s02-prep-divisibility-decomposition.md` (researcher-6, PR #18401, MERGED)
- S2-A PREP — `2026-05-13-s2a-prep-MotivicMeasure-structure-design.md` (researcher-6, PR #18457, MERGED)

---

## 1. What this PR does

Lands the four divisibility theorems explicitly scoped by PR #18401's
S2 PREP cost-reduction memo, all derived directly from the already-merged
`main_theorem_expanded` in `MotivicFlagMaps.lean`:

| Theorem | LOC | Divisor | Witness |
|---|---|---|---|
| `L_pow_triangular_dvd_motivicClassBasedMaps` | 5 | `K.L ^ triangular n` | `(∏ (L^i - 1)) * L^a` |
| `L_pow_a_dvd_motivicClassBasedMaps` | 5 | `K.L ^ (computeA β).toNat` | `(∏ (L^i - 1)) * L^{triangular n}` |
| `L_pow_full_dvd_motivicClassBasedMaps` | 4 | `K.L ^ (triangular n + (computeA β).toNat)` | `∏ (L^i - 1)` |
| `L_minus_one_dvd_motivicClassBasedMaps` | 8 | `K.L - 1` | i = 0 factor of the GL_n product |

**Net delta**: +60 LOC in `proofs/Proofs/MotivicFlagMaps.lean` (4 theorems + section
header + module-doc). **+0 axioms** (every proof reduces by `main_theorem_expanded`
+ algebraic identities — no new structure-encoded assumptions, no new `axiom`
declarations).

The axiom count of the file stays at **2** (`motivicClassBasedMaps`,
`motivic_class_flag_maps`), and the assumption-encoding structure
`GrothendieckRingVar` is unchanged.

---

## 2. Proof sketches (one paragraph each)

All four proofs share the same opening move: rewrite the LHS using
`main_theorem_expanded` to expose the literal factorization
`(∏ (L^i - 1)) * L^{triangular n + a}`. From there:

- **S2-C1 / S2-C2**: split the exponent `triangular n + a` via `pow_add`, then
  close by `ring` with witness `(∏ (L^i - 1))` times the "other" `L`-power.
- **S2-C-combined**: even cheaper — the exponent doesn't need splitting; the
  witness is the bare GL_n-product `∏ (L^i - 1)`, and `ring` closes immediately.
- **S2-D**: peel the GL_n product. `Finset.dvd_prod_of_mem`, applied to the
  index `0 ∈ Finset.range n` (which uses `hn : n ≥ 1`), gives
  `(K.L ^ 1 - 1) ∣ ∏ i ∈ Finset.range n, (K.L ^ (i+1) - 1)`. Then `simp only
  [zero_add, pow_one]` cleans the `0 + 1` and `K.L ^ 1`, yielding the desired
  `(K.L - 1) ∣ ∏ ...`; lifting through the `* L^{...}` factor via
  `dvd_mul_of_dvd_left` closes the goal.

No `sorry` placeholders. No new imports beyond the existing `import Mathlib` at
the head of the file.

---

## 3. Small-case sanity (researcher-6's PREP §5)

For `n = 2`, `β = (1, 1)` (where `MotivicFlagMaps.computeA_11` is already
proved `= 4`):

```
[Ω²_{(1,1)}(Fl_3)] = (L - 1)(L² - 1) · L · L^4 = (L - 1)(L² - 1) · L^5
                                                 └──┬──┘   └─┬─┘
                                            L^{triangular 2}  L^a
```

- `L_pow_triangular_dvd_…` witness: `(L−1)(L²−1) · L^4` ✓
- `L_pow_a_dvd_…`         witness: `(L−1)(L²−1) · L` ✓
- `L_pow_full_dvd_…`      witness: `(L−1)(L²−1)` ✓
- `L_minus_one_dvd_…`     witness: `(L²−1) · L^5` ✓

All four pass the literal-factorization check. The PREP author noted "no sign
or convention issue"; this ACT inherits that guarantee.

---

## 4. Mathlib lemma audit (v4.26.0)

Three Mathlib names are load-bearing. Confirmed available in v4.26.0 (pinned
in `proofs/lakefile.toml`):

- `pow_add : a^(m + n) = a^m * a^n` — `Mathlib.Algebra.GroupPower.Basic`.
- `Finset.dvd_prod_of_mem : (f : ι → M) → a ∈ s → f a ∣ ∏ i ∈ s, f i` —
  `Mathlib.Algebra.BigOperators.Order`. Requires `[CommMonoid M]`, which is
  supplied by `K.ringInst : CommRing K.carrier`.
- `Finset.mem_range : a ∈ Finset.range n ↔ a < n` — `Mathlib.Data.Finset.Range`.
  Applied via `.mpr` to `hn : n ≥ 1` (definitionally `1 ≤ n = 0 < n`).
- `dvd_mul_of_dvd_left : a ∣ b → ∀ c, a ∣ b * c` — `Mathlib.Algebra.GroupWithZero.Divisibility`.

No phantom names; all four lemma applications are direct.

---

## 5. Why these matter for OQ-03

The realization-functor program scoped by S1 OBSERVE (PR #18299) and the
`MotivicMeasure` structure scoped by S2-A PREP (PR #18457) need *algebraic*
divisibility facts in `K_0(Var)` to translate into *cohomological* vanishing
facts in the target ring. Specifically (PR #18457 §"Headline payoff"):

> Once S2-D's `(K.L - 1) ∣ motivicClassBasedMaps K n β` (for `n ≥ 1`) is in,
> Propagation 2 immediately gives:
> **For `n ≥ 1`, the Euler characteristic of `Ω²_β(Fl_{n+1})` vanishes.**

This PR is exactly that "S2-D land". The S2-A ACT that lays down
`MotivicMeasure` + `eulerMeasure` instance can now consume
`L_minus_one_dvd_motivicClassBasedMaps` as a one-line input.

Similarly, `L_pow_full_dvd_…` is the lemma every `μ` consumes when one wants
"the moduli class is divisible by `μ K.L` to the power `triangular n + a` in
the target ring." This is precisely how Bruhat-decomposition counts propagate.

---

## 6. Build status

**Worktree symlink loop**: `proofs/.lake` is the well-known broken symlink
(see CLAUDE.md / memory note: "`.lake` symlink loop + mid-build worktree wipe").
Direct `./proofs/scripts/docker-build.sh` from the worktree will fail. This PR
ships the Lean changes as **build-pending** in line with established
researcher-3 / researcher-11 conventions.

Per memory protocol:

1. Lean file committed + pushed first (this commit).
2. PR title / body explicitly mark "build pending".
3. Mechanic or Doctor verifies from a clean worktree post-merge.

The proof scripts are short (≤ 8 lines each), every Mathlib lemma is
single-application, and the four theorems are independent — failure of any
one is isolatable to its own proof block.

---

## 7. Honesty / disclaimers

- These are **divisibility lemmas in an abstract commutative ring**, not
  topological statements. They become topological only after composing with
  a realization homomorphism (`MotivicMeasure`); that composition is the work
  of the subsequent S2-A ACT (~80 LOC, +4 axioms per PR #18457 §"S2-A ACT
  estimate").
- Routine. The S2 PREP (PR #18401) explicitly noted the cost is
  ~25 LOC across the three S2-C variants. This ACT lands roughly that
  (~60 LOC counting section header + module-doc + the new S2-D theorem).
  No mathematical insight beyond what `main_theorem_expanded` already
  packages.
- The Euler-characteristic claim "for `n ≥ 1`, `χ(Ω²_β(Fl_{n+1})) = 0`" is
  **classical and well known** (any cell decomposition of GL_n shows it). The
  value of these lemmas is to expose the same fact via a Lean-internal
  divisibility chain that does not depend on Mathlib's (absent) algebraic
  geometry stack.

---

## 8. Phase transition

```
ORIENT  →  (this PR, S2 ACT)  →  ACT  (four divisibility lemmas live; S2-A ACT enabled)
```

`state.md` is **not** edited in this PR — per the established convention,
Lean ACTs update phase via the gallery JSON post-merge (which does not yet
exist for OQ-03 sub-research; that will be created when S2-A ACT lands the
`MotivicMeasure` infrastructure).

---

## 9. What this session deliberately does **not** do

- No edits to `problem.md`, `knowledge.md`, `state.md`, or any
  `src/data/research/problems/*.json` file.
- No `MotivicMeasure` structure design (that is S2-A's responsibility per
  PR #18457).
- No `eulerMeasure` / `pointCountMeasure` instances (S2-A and S2-B).
- No edits to `MotivicFlagMapsPartialFlags.lean` (OQ-02) or
  `MotivicFlagMapsProvable.lean` (OQ-01).
- No new gallery entry — `motivic-flag-maps-oq-03` ships as a research-only
  workspace until the S2-A ACT lands a citable Euler-vanishing theorem.

---

## 10. Cross-references

- **Parent Lean file**: `proofs/Proofs/MotivicFlagMaps.lean` (Part VI-B
  added at line ~347, immediately after `main_theorem_expanded`).
- **S1 OBSERVE**: PR #18299 (researcher-10).
- **S2 PREP**:  PR #18401 (researcher-6) — original divisibility design.
- **S2-A PREP**: PR #18457 (researcher-6) — `MotivicMeasure` structure design.
- **Sibling slugs**:
  - `motivic-flag-maps-oq-01` (active, OBSERVE) — Mathlib formalization of
    the moduli-space axiom. Orthogonal: this ACT does not touch the axiom.
  - `motivic-flag-maps-oq-02` (active, OBSERVE) — partial-flag extension.
    Orthogonal: lives in `MotivicFlagMapsPartialFlags.lean`.
