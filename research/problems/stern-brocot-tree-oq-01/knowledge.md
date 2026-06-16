# Knowledge Base: stern-brocot-tree-oq-01

## Problem Summary

The Stern–Brocot tree enumerates **every positive rational exactly once, in
lowest terms**. Mathlib (v4.26) has no Stern–Brocot tree, mediant, or Farey
development, so `proofs/Proofs/SternBrocotTreeOQ01.lean` builds the structure
from scratch over `List Bool` paths and `ℤ` boundary pairs.

Target = the full bijection `{paths} ≃ {reduced positive rationals}`, which
factors as: (a) every label is a reduced positive rational [kernel, done];
(b) surjectivity; (c) injectivity.

---

## Status

- **(a) Structural kernel — DONE** (build-pending orphan, prior session):
  `sb_det` (unimodular invariant `aL·bR − aR·bL = −1`), `sb_pos`, `sbNum_pos`,
  `sbDen_pos`, `sb_isCoprime` (lowest terms via explicit Bézout), `sb_root`.
- **(b) Surjectivity — DONE this session** (`sb_surjective`).
- **(c) Injectivity — foundation done** (`sb_left_lt_mediant`,
  `sb_mediant_lt_right`); full injectivity still open.

All work is in the **unregistered orphan** `SternBrocotTreeOQ01.lean` (not in
`Proofs.lean`, no `src/data/proofs/` gallery dir) → zero gallery/build risk
while build-pending under the Docker blackout.

---

## Session 2026-06-16 (s2, researcher-9) — ACT, surjectivity + mediant separation

**Mode**: REVISIT (own prior in-progress work). **Backend**: dual blackout —
Aristotle `prove` → 404; `docker info` → rc=124 with 14 stuck sibling build
wrappers (a 15th build would OOM peers), so **no Lean compiled**. All names
verified against the offline Mathlib v4.26 checkout at `/Users/rwalters/GitHub/mathlib4`.

### What I proved (new, sorry-free by construction)

1. **Mediant separation** (injectivity foundation), division-free integer form:
   - `sb_left_lt_mediant : (sb p).aL * sbDen p < sbNum p * (sb p).bL`
   - `sb_mediant_lt_right : sbNum p * (sb p).bR < (sb p).aR * sbDen p`
   Both reduce to `aL·bR − aR·bL = −1 < 0` (= `sb_det`); closed by `nlinarith [sb_det p]`.

2. **Prefix-transfer lemmas** via conjugation homomorphisms `T`, `T'`:
   - `T s = ⟨aL, aL+bL, aR, aR+bR⟩` (left-mult by `[[1,0],[1,1]]`),
     `T' s = ⟨aL+bL, bL, aR+bR, bR⟩` (left-mult by `[[1,1],[0,1]]`).
   - Key fact: `T`/`T'` **commute with `SB.step`** (`T_step`, `T'_step`), hence
     with the whole fold (`T_sbFrom`, `T'_sbFrom`). Since
     `start.step false = T start` and `start.step true = T' start`, prepending a
     move conjugates the state: `sb (false::q) = T (sb q)`, `sb (true::q) = T' (sb q)`.
   - Consequence on labels: prepending `L` sends `(num,den) ↦ (num, num+den)`;
     prepending `R` sends `(num,den) ↦ (num+den, den)`
     (`sbNum_false_cons`, `sbDen_false_cons`, `sbNum_true_cons`, `sbDen_true_cons`).

3. **Surjectivity** `sb_surjective (a b : ℤ) (1≤a) (1≤b) (IsCoprime a b) :
   ∃ p, sbNum p = a ∧ sbDen p = b`. Strong induction on `(a+b).toNat`
   (`Nat.strong_induction_on`) via the subtractive Euclidean descent:
   - `a = b` ⟹ `IsCoprime a a` ⟹ `IsUnit a` (`isCoprime_self`) ⟹ `a = 1`
     (`Int.isUnit_iff`, `−1` killed by `1 ≤ a`) ⟹ root `[]`.
   - `a < b` ⟹ recurse on `(a, b−a)` then prepend `L`; coprimality preserved by
     `IsCoprime.of_add_mul_left_left` (with `b = (b−a) + a*1`).
   - `b < a` ⟹ recurse on `(a−b, b)` then prepend `R`.

### Why this is the right decomposition

The prepend-transfer lemmas are the crux: the naive "child = remove last move"
relation does **not** give a clean `a↦a−b` recurrence because the boundaries
shift per node. Prepending instead corresponds to a **fixed** left-multiplication
(`T`/`T'`) that commutes with the fold, so the label recurrence is global and
exactly the Euclidean descent. This is the matrix identity
`M_start·X_b·G·v = (M_start·X_b·M_start⁻¹)·(M_start·G·v)` with `M_start` its own
inverse; `T`/`T'` are the conjugated generators, proved elementarily without
matrices.

### Files Modified
- `proofs/Proofs/SternBrocotTreeOQ01.lean` (+~135 lines: T/T', transfer lemmas,
  mediant separation, surjectivity; updated module docstring).

### Next Steps
1. **Docker-up**: `./proofs/scripts/docker-build.sh Proofs.SternBrocotTreeOQ01`;
   grep log for `error:`. Likely-fragile tactics to watch: `omega` on the
   `SB.mk.injEq` conjunctions in `T_step`/`T'_step`; `simp only [..., T]`
   projection reduction in the four transfer lemmas; `by decide` on the two
   `start.step _ = T _ / T' _` facts. If any fail, the fixes are local
   (`congr 1 <;> ring` for the structure eqs; `cases`/`dsimp` to force projection
   reduction).
2. **Injectivity** (remaining open piece): use `sb_left_lt_mediant` /
   `sb_mediant_lt_right` to show the two subtrees of any node occupy disjoint open
   intervals, hence the label is injective on paths. Combined with `sb_surjective`
   + `sb_isCoprime` this closes the full bijection.
3. Register in `Proofs.lean` + add `src/data/proofs/stern-brocot-tree-oq-01/`
   gallery data only after a green build.

---

## Mathlib / Gallery Gap

No Stern–Brocot / mediant / Farey in Mathlib v4.26. Reusable recipe established:
`det = −1` ⟹ lowest terms via Bézout; conjugation-homomorphism transfer lemmas
for prepend recurrences on fold-based tree encodings.
