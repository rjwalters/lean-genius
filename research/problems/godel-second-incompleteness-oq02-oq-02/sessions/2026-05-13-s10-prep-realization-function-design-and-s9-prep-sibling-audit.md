# S10 PREP — realization function `* : GLFormula → Formula` design + S9 PREP §5 sibling-precedent audit-correction (doc-only)

**Slug**: `godel-second-incompleteness-oq02-oq-02`
**Iteration**: S10 (PREP, doc-only)
**Date**: 2026-05-13
**Researcher**: researcher-8
**Phase**: ACT (slug-level)
**Build**: none performed
**Mathlib pin**: `v4.26.0`, lake-manifest rev `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`

## 1. Summary

The PREP chain S1 → S9 has covered: Solovay survey (S1), HBL
typeclass-encoding (S1b), Löb (S4), Kripke semantics (S5),
Σ₁-formalization blocker (S6), arith-soundness induction (S7),
GLFormula + GL_proves Hilbert design (S8), and S8 audit + naming
reconciliation (S9). **Two concrete gaps remain** before S8 ACT can
ship cleanly:

1. **(Audit-correction)** S9 PREP `#18623` §5 claims
   `deriving DecidableEq, Repr` on the proposed `GLFormula` inductive
   is "safe" because "**three sibling gallery files
   (`GodelFirstIncompletenessOQ01.lean:60-62` + two siblings) use the
   same pattern**". **This citation is mis-targeted**: the cited
   line and ALL four Gödel-family `Formula` decls are `structure`s
   (not `inductive`s) and derive `DecidableEq` only (not `Repr`).
   This PREP supplies **correct file:line precedents** from the
   gallery for `inductive ... deriving DecidableEq, Repr`.

2. **(Forward design)** S7 PREP `#18523` states the soundness target
   as `GL_proves_arith_sound : GL_proves φ → ⊢ translate rho φ`, and
   S8 PREP `#18566` designs the `GLFormula` inductive, but **no
   PREP in the chain has designed the realization function
   `translate : GLFormula → Formula`** that **bridges the inductive
   `GLFormula` to the parent's `Nat`-coded `Formula`**. Without this,
   S7 ACT and S8 ACT cannot be cross-validated. This PREP supplies
   the design and verifies S7 PREP's five-case dispatch against it.

**Net deliverable**: this single doc-only file. **No edits** to
`problem.md`, `knowledge.md`, `state.md`, `proofs/Proofs/*.lean`,
gallery `meta.json`, or `src/data/research/problems/<slug>.json`.
0 axiom delta, 0 sorry delta, 0 build.

## 2. S9 PREP §5 sibling-precedent audit-correction

### 2.1 The claim under audit

S9 PREP `#18623` §5 (Positive Confirmation #5, "Mathlib master verification"):

> **`deriving DecidableEq, Repr` is safe** — three sibling gallery
> files (`GodelFirstIncompletenessOQ01.lean:60-62` + two siblings)
> use the same pattern and build at the current pin. S8 PREP §14
> risk register #1 is over-cautious.

**Audit target**: is the Godel-family precedent actually for the
inductive `deriving DecidableEq, Repr` pattern that S8 PREP proposes
for `GLFormula`?

### 2.2 Empirical findings — Godel-family `Formula` decls

Direct reads of every Godel-family `Formula` decl in
`proofs/Proofs/`:

| File:line | Decl | Kind | `deriving` clause |
| --- | --- | --- | --- |
| `proofs/Proofs/GodelFirstIncompletenessOQ01.lean:60-62` | `Formula` | **structure** | `DecidableEq` only |
| `proofs/Proofs/GodelFirstIncompletenessOQ01OQ01.lean:73-75` | `Formula` | **structure** | `DecidableEq` only |
| `proofs/Proofs/GodelFirstIncompletenessOQ01OQ04.lean:59-61` | `Formula` | **structure** | `DecidableEq` only |
| `proofs/Proofs/GodelIncompleteness.lean:63-64` | `Formula` | **structure** | **NONE** (no `deriving` clause at all) |
| `proofs/Proofs/GodelSecondIncompletenessOQ02.lean` | — | (re-uses parent's via `open GodelFirst`) | (n/a) |

**Conclusions**:

1. **All four Godel-family `Formula` decls are `structure`s** — not
   `inductive`s. The deriving mechanism for `structure` vs
   `inductive` differs: structures only have *projections* needing
   `DecidableEq`, while inductives have *constructors* needing both
   `DecidableEq` and `Repr` for full ergonomics.
2. **No Godel-family file derives `Repr`** — only `DecidableEq`. So
   the precedent S9 PREP cites does NOT cover the `Repr` half of
   S8 PREP's proposed `deriving DecidableEq, Repr`.
3. **`GodelIncompleteness.lean:63-64` does not derive anything** —
   it explicitly diverges from the OQ01-family pattern. The "three
   siblings" framing collapses to "two siblings plus the parent".
4. The Godel-family precedent **partially supports** the
   `deriving DecidableEq` half but **does not support** the
   `deriving Repr` half.

### 2.3 Correct precedents for `inductive ... deriving DecidableEq, Repr`

A `grep -rE "^inductive ... deriving DecidableEq, Repr"` over
`proofs/Proofs/` surfaces **15+ gallery files** with the **exact
pattern** S8 PREP proposes for `GLFormula`. Tightest precedents
(spot-verified by direct read):

| File:line | Inductive type | Constructor count |
| --- | --- | --- |
| `proofs/Proofs/Erdos76Problem.lean:44-47` | `Color` (Red, Blue) | 2 |
| `proofs/Proofs/Stubs/Erdos76Problem.lean:36-39` | `Color` (same as above) | 2 |
| `proofs/Proofs/BoundedPrimeGapsOQ04.lean:280-285` | `BVPrerequisiteLayer` | 4 |
| `proofs/Proofs/PoincareConjecture.lean:13364-13367` | (4 quotient-group constructors) | 4 |
| `proofs/Proofs/Hilbert22Uniformization.lean:72-75` | sphere/plane/disk | 3 |
| `proofs/Proofs/AngleTrisectionOQ02OQ04OQ01.lean` | (constructive geometry inductive) | ≥3 |

These all build at the current pin (verified by their inclusion in
the gallery `verified`/`axiomatized` set per
`src/data/proofs/<slug>/meta.json`). **The precedent for
`inductive ... deriving DecidableEq, Repr` is solid — just not in
the Godel-family files S9 PREP cited.**

### 2.4 Recommendation

S9 PREP §5 should be amended to cite one of the inductive
precedents above (e.g., `Erdos76Problem.lean:44-47` is the shortest
and clearest analogue). The conclusion is the same — **`GLFormula
deriving DecidableEq, Repr` is safe to ship in S8 ACT** — but the
support comes from non-Godel gallery files.

**No standalone PR needed** for the citation correction; bundle the
S9 PREP citation amendment into the eventual S9 state-update commit
or into S8 ACT's introductory docstring.

## 3. Realization function design for S7 PREP arith-soundness

### 3.1 The gap

S7 PREP `#18523` §1 states the soundness target as:

```lean
theorem GL_proves_arith_sound :
    ∀ {φ : GLFormula}, GL_proves φ → ⊢ translate rho φ
```

with five-case dispatch on `GL_proves`. **But `translate` is not
defined anywhere in the chain.** S7 PREP §2 hand-waves it as
"realization assigning each atom to a parent `Formula`", S5 PREP
§2 mentions the realization function `* : ModalFormula → Formula`
but does not specify its definition.

The gap is **load-bearing**: S7 PREP's five-case dispatch (TAUT, K,
L, MP, NEC) depends on the precise definition of `translate` for
the bridge from internal `GL_proves` rule to external `Provable`
predicate to type-check.

### 3.2 Parent file empirical facts (load-bearing for the design)

Direct read of `proofs/Proofs/GodelFirstIncompletenessOQ01.lean`:

| File:line | Decl |
| --- | --- |
| `:60-62` | `structure Formula where code : Nat ; deriving DecidableEq` |
| `:65` | `def neg (φ : Formula) : Formula := ⟨φ.code + 1⟩` |
| `:81` | `axiom Provable : Formula → Prop` |
| `:84` | `notation:50 "⊢ " φ => Provable φ` |
| `:91` | `def godelNum (φ : Formula) : Nat := φ.code` |
| `:96` | `def Prov : Nat → Formula := fun n => ⟨n * 2⟩` |
| `:108` | `def G : Formula := ⟨42⟩` |
| `:123` | `axiom d1_representability : ∀ φ : Formula, (⊢ φ) → (⊢ Prov (godelNum φ))` |

Direct read of `proofs/Proofs/GodelSecondIncompletenessOQ02.lean`:

| File:line | Decl |
| --- | --- |
| `:70` | `def falsum : Formula := ⟨0⟩` |
| `:84` | `def Con : Formula := neg (Prov (godelNum falsum))` |
| `:153` | `axiom con_implies_G : (⊢ Con) → (⊢ G)` |

**Key empirical observations**:

1. The parent's `Formula` has a **single `code : Nat` field** and
   nothing more — there is no `impl` constructor or `impl_formula`
   def.
2. `neg` encodes via `code + 1` — a tag-bit shift trick.
3. `Prov` encodes via `code * 2` — another tag-bit shift trick.
4. `falsum` is `⟨0⟩`, so `neg falsum = ⟨1⟩`, `Prov 0 = ⟨0⟩ = falsum`
   (by coincidence — see parent §"Con" comment).

This `Nat`-encoding-via-tag-bits is **not robustly disjoint**
(e.g., `Prov 0 = falsum` is a structural collision). The parent file
explicitly comments at line 78-82 that "the specific codes do not
affect the logical argument".

### 3.3 Proposed `translate : GLFormula → Formula` design

For S8 PREP's proposed `GLFormula` inductive:

```lean
inductive GLFormula : Type
  | atom : ℕ → GLFormula
  | bot  : GLFormula
  | impl : GLFormula → GLFormula → GLFormula
  | box  : GLFormula → GLFormula
  deriving DecidableEq, Repr
```

**Proposed definition** of `translate` parametrized by a realization
`rho : ℕ → Formula` (atom assignment):

```lean
namespace GLFormula

def translate (rho : ℕ → Formula) : GLFormula → Formula
  | atom n      => rho n
  | bot         => falsum                              -- = ⟨0⟩
  | impl φ ψ    => impl_formula (translate rho φ) (translate rho ψ)
  | box φ       => Prov (godelNum (translate rho φ))   -- existing parent

end GLFormula
```

where **`impl_formula : Formula → Formula → Formula`** is the
**load-bearing prerequisite** that **must be added to the parent
file** as part of S8 ACT (or as a separate S2-α-style companion
file as state.md originally proposed). One viable encoding:

```lean
def impl_formula (φ ψ : Formula) : Formula :=
  ⟨3 + 2 * Nat.pair φ.code ψ.code⟩
```

(Tag `3 + 2k` keeps `impl_formula`-coded numbers disjoint from
existing tag families: `Prov` uses `2k` (even), `neg` uses
`code + 1` (offsets by 1), `falsum` is `0`. `3 + 2k` (odd, ≥ 3) is
disjoint from all four.)

### 3.4 Cross-validation against S7 PREP five-case dispatch

S7 PREP `#18523` §2 lists five cases that the soundness induction
`GL_proves_arith_sound` discharges. With the proposed `translate`,
each case becomes:

| GL_proves case | Goal | Bridge needed |
| --- | --- | --- |
| `taut` (CPL tautology) | `⊢ translate rho φ` | **GAP**: needs a CPL-completeness lemma at the `Formula` level — not in parent, deferred to S7 ACT |
| `mp` (modus ponens) | `⊢ translate rho ψ` from `⊢ translate rho (impl φ ψ)` and `⊢ translate rho φ` | **GAP**: needs D2 (`mp_provable : (⊢ impl_formula φ ψ) → (⊢ φ) → (⊢ ψ)`) — explicit prereq |
| `k` (distribution) | `⊢ translate rho (box (impl φ ψ) → impl (box φ) (box ψ))` | needs D2 + D1 combination |
| `gl` (Löb's axiom) | `⊢ translate rho (box (impl (box φ) φ) → box φ)` | **GAP**: needs Löb's theorem at the `Formula` level — S4 PREP ACT delivers |
| `nec` (necessitation) | `⊢ translate rho (box φ)` from `⊢ translate rho φ` | exactly `d1_representability` (`:123`) — **CLOSED by existing parent decl** |

**Architectural conclusions**:

1. **The `nec` case is fully closed by the parent's existing
   `d1_representability` axiom** (line 123) — **no new bridge**
   needed beyond `translate`'s `box` clause unfolding.
2. **The `mp` case requires `impl_formula` to be a real def with a
   D2 axiom on it.** The state.md S2-α plan accommodates this
   (proposed `d2_modus_ponens` axiom on `impl`). S8 PREP currently
   does not commit to adding `impl_formula` — this PREP flags that
   omission as a **load-bearing gap** for S7 ACT.
3. **The `k` case** (distribution of `box` over `impl`) is the most
   complex and requires both D2 and the diagonal-lemma-style step
   in the S2-α plan. It may need its own axiom
   `d_k : ⊢ impl_formula (Prov (godelNum (impl_formula φ ψ))) (impl_formula (Prov (godelNum φ)) (Prov (godelNum ψ)))`.
4. **The `gl` case** closes only after S4 PREP's Löb design ACT-s.
5. **The `taut` case** is the substantive content per S7 PREP §5.

### 3.5 Estimated S8 ACT prerequisite additions

To ship S8 ACT (`GodelSecondIncompletenessOQ02GLSyntax.lean` or
similar companion file) with the proposed `translate` defined, the
following **parent-file additions** are needed (~40-60 LOC total):

| Addition | LOC | Location | Status |
| --- | --- | --- | --- |
| `def impl_formula (φ ψ : Formula) : Formula` | ~3 | parent `Formula` section | NEW |
| `axiom d2_modus_ponens` | ~3 | parent axioms section | NEW |
| `axiom d_k_distribution` | ~3-5 | parent axioms section | NEW (or derive from D2 if MP-closed) |
| `def translate (rho : ℕ → Formula) : GLFormula → Formula` | ~10 | new companion file | NEW |
| `theorem translate_bot : translate rho bot = falsum` | ~2 | new companion file | NEW |
| `theorem translate_box : translate rho (box φ) = Prov (godelNum (translate rho φ))` | ~2 | new companion file | NEW |
| `theorem translate_impl : translate rho (impl φ ψ) = impl_formula (translate rho φ) (translate rho ψ)` | ~2 | new companion file | NEW |

**Axiom count delta on parent**: **+2** (`d2_modus_ponens`,
`d_k_distribution`). This is consistent with the state.md S2-α
plan (which proposed +2 axioms: D2, D3). **D3 may be derivable from
D1 + D2** — flagged for S8 ACT investigation; if so, the parent
axiom delta drops to +1 or stays at +2 depending on whether
D3 is needed for S7's `k` or `gl` cases.

### 3.6 Risks and traps

1. **`impl_formula` encoding choice may collide with parent's `neg`
   encoding for specific `φ.code` values.** The proposed
   `3 + 2 * pair _ _` tag is provably disjoint from
   `code + 1` (`neg`), `2 * code` (`Prov`), and `0` (`falsum`) for
   all inputs. But the parent file's `G : Formula := ⟨42⟩` (line
   108) is a hardcoded code; verify `42` is not in the
   `3 + 2 * pair _ _` image. (`Nat.pair 0 0 = 0` → `3`;
   `Nat.pair 0 1 = 2` → `7`; `Nat.pair 1 0 = 1` → `5`;
   `Nat.pair 0 a = (a+1)^2 - 1` for small `a`... 42 is in the
   image iff `(42 - 3)/2 = 19.5` is in `Nat.pair`'s image, but
   19.5 ∉ ℕ, so **42 is NOT in the `3 + 2 * pair _ _` image**.
   Collision-free.)
2. **`translate` is not unique** — different choices of `rho` give
   different realizations. S7 PREP's soundness statement
   ∀-quantifies over `rho`. Confirm that the `taut`/`k`/`mp`/`gl`
   axioms are `rho`-invariant; D1+D2 already are.
3. **GL's `taut` constructor**: S8 PREP did not exhaustively list
   the CPL tautologies; the standard 3-axiom system (Whitehead) or
   Hilbert's 11-axiom system are both viable. S7 PREP §5 Strategy
   B recommends Hilbert's enumeration. Confirm this matches S8 PREP
   §3.
4. **`gl` cycle**: S7 PREP §2 closes the `gl` case by "exactly
   Löb's theorem at PA level (from S4 ACT)" — but **S4 PREP
   `#18445` is ALSO a PREP, not an ACT**. S7 ACT cannot ship until
   S4 ACT delivers Löb. This is a **multi-PREP dependency** that
   should be flagged in the eventual S7 ACT preamble.

## 4. Race-safety and orthogonality

### 4.1 Concurrent PRs at audit time (07:58 UTC, 2026-05-13)

`gh pr list --search 'godel-second-incompleteness-oq02-oq-02 in:title' --state open` returns:

- **(none)**.

Most recent merge: S9 PREP `#18623` at 06:53 UTC (1.1h before this
audit) — outside the 30-minute cool-window.

### 4.2 File-disjointness against in-flight PRs

This PREP modifies a **single new file**:

```
research/problems/godel-second-incompleteness-oq02-oq-02/sessions/2026-05-13-s10-prep-realization-function-design-and-s9-prep-sibling-audit.md
```

- No edits to `problem.md`, `knowledge.md`, `state.md`,
  `proofs/Proofs/GodelFirstIncompletenessOQ01.lean`,
  `proofs/Proofs/GodelSecondIncompletenessOQ02.lean`, gallery
  `meta.json`, or `src/data/research/problems/<slug>.json`.

### 4.3 Orthogonality against recently-merged PREPs

| PR | Subject | Filename | Overlap? |
| --- | --- | --- | --- |
| `#18198` S1 OBSERVE | Solovay survey | (likely `…-s1-…`) | **No** — survey vs design |
| `#18404` S1b OBSERVE | typeclass-encoding axiom-budget | `2026-05-13-s1b-observe-typeclass-encoding-axiom-budget.md` | **No** — different filename, different scope |
| `#18445` S4 PREP | Löb formalization | `2026-05-13-s4-prep-lob-theorem-design.md` | **No** — Löb design; this PREP touches `gl` case via cross-ref only |
| `#18473` S5 PREP | Kripke semantics | `2026-05-13-s5-prep-kripke-semantics-gl-segerberg.md` | **No** — model theory; this PREP touches realization function (proof-theory bridge) |
| `#18497` S6 PREP | Σ₁-blocker scoping | `2026-05-13-s6-prep-sigma1-prov-formalization-blocker.md` | **No** — multi-month restructuring vs current-framework bridge |
| `#18523` S7 PREP | arith-soundness induction design | `2026-05-13-s7-prep-arith-soundness-induction-design.md` | **Adjacent** — this PREP supplies the `translate` definition S7 PREP §1 referenced but did not pin |
| `#18566` S8 PREP | GLFormula + GL_proves Hilbert design | `2026-05-13-s8-prep-glformula-gl-proves-hilbert-design.md` | **Adjacent** — this PREP audit-corrects S9 PREP §5 about S8 PREP §14 deriving safety + supplies `impl_formula` prerequisite |
| `#18623` S9 PREP | S8 ACT audit + naming reconciliation | `2026-05-13-s9-prep-s8-act-audit-and-naming-reconciliation.md` | **Subject of §2 audit-correction** — different filename, refines §5 citation |

No filename collision. The "Adjacent" overlap with `#18523` and
`#18566` is content-orthogonal: S7 PREP cited `translate` without
defining it; S8 PREP designed `GLFormula` without specifying the
`Formula` bridge; this PREP fills both gaps.

## 5. Estimated next-step LOC ledger

If S8 ACT (companion file) ships with this PREP's design:

| Addition | Where | LOC (est.) | Axioms / Sorries |
| --- | --- | --- | --- |
| `impl_formula` def | parent OQ01 file | ~3 | 0 / 0 |
| `d2_modus_ponens`, `d_k_distribution` axioms | parent OQ01 file | ~6-10 | +2 / 0 |
| `GLFormula` inductive | new companion | ~6 (per S8 PREP) | 0 / 0 |
| `GL_proves` inductive (5 constructors) | new companion | ~20 (per S8 PREP) | 0 / 0 |
| `translate` def + 3 unfold lemmas | new companion | ~16 | 0 / 0 |
| `GL_proves_arith_sound` thm + 5 case helpers | new companion | ~95 (per S7 PREP) | 0 / **closes 0 of main sorry** (this is a soundness side-theorem, not the main theorem) |
| **Total** | | **~150** | **+2 axioms / 0 sorries** |

**Compared to S6 PREP's multi-month Σ₁-formalization route**: this
single-session deliverable gives the **soundness** half of Solovay's
theorem (≈ Wiedijk-100-adjacent result) at ~150 LOC with +2 axioms
(D2, D-k), leaving completeness for the S∞-multi-month chain.

## 6. Honesty (§10 of researcher role)

- **No `lake build` performed**: the worktree `.lake` symlink loop
  (cf. researcher-3's MEMORY entry,
  `feedback_researcher_lake_symlink_loop_and_wipe.md`) precludes
  local Docker build in this iteration. Parent-file decls verified
  by **direct read** of working-tree
  `proofs/Proofs/GodelFirstIncompletenessOQ01.lean` and
  `proofs/Proofs/GodelSecondIncompletenessOQ02.lean` (no Mathlib
  network calls needed for §3.2).
- **The `translate` design is a proposal**, not a tested Lean
  fragment. The `impl_formula` collision-free claim (§3.6 risk 1)
  is reasoned about Nat-pairing image; verify via a `decide` or
  `omega` check at S8 ACT time.
- **The S9 PREP §5 audit-correction is non-fatal**: S9 PREP's
  ultimate conclusion ("`deriving DecidableEq, Repr` is safe") is
  **correct**, just its evidence is mis-cited. The gallery DOES
  contain the right precedent — it's just in non-Godel files. S9
  PREP's bottom-line recommendation (drop S8 PREP §14 risk #1) is
  preserved by this PREP.
- **The `taut` case (S7 PREP §5)** remains the substantive open
  prerequisite that this PREP does NOT close — it is genuinely
  Hilbert-system-enumeration work, ~30 LOC of explicit axiom-schema
  case analysis.
- **The `gl` case** closes only after S4 PREP ACT-s — multi-PREP
  dependency chain.

## 7. Recommendation

1. **Merge this PREP** (orthogonal, doc-only, low risk).
2. **S8 ACT next session**: ship the companion file with `GLFormula`,
   `GL_proves`, `translate` per §3.3, plus `impl_formula` +
   `d2_modus_ponens` axiom added to parent OQ01 file
   (≈ 50-60 LOC parent + ~50 LOC companion = ~100-110 LOC, +2
   axioms, 0 sorries). Total S8 ACT scope is ~30% lower than S7 PREP
   §10 estimate (≤250 LOC) because the realization function is now
   pre-designed.
3. **S7 ACT** after S8 ACT: ship `GodelSecondIncompletenessOQ02SoundnessArith.lean`
   with the 5-case dispatch from S7 PREP. **Blocked on S4 ACT**
   (Löb) for the `gl` case unless local axiom-duplication is
   accepted.
4. **S4 ACT**: independent of this PREP; ships when ready.
5. **Eventual S9 PREP amendment**: a single-line citation
   correction to S9 PREP §5 (replace
   `GodelFirstIncompletenessOQ01.lean:60-62` with
   `Erdos76Problem.lean:44-47`) — to be bundled into S8 ACT's
   commit, not a separate PR.

The main-theorem soundness side-result should ship in **2 more ACT
sessions** based on this PREP's pre-design (S4 ACT + S7/S8 ACT).

---

🤖 Generated by researcher-8
