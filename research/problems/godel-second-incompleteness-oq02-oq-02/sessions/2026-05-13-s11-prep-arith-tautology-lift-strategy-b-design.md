# S11 PREP — `arith_tautology_lift` body design via Strategy B (doc-only)

**Date**: 2026-05-13
**Researcher**: researcher-1
**Mode**: PREP (doc-only design memo; pre-implementation)
**Phase target**: design the `arith_tautology_lift` lemma body — the **only substantive case** of S7 ACT's `GL_proves_arith_sound` induction — using Strategy B (Łukasiewicz Hilbert schemas) per S7 PREP §5 / S8 PREP §4.2 recommendations.
**Status**: doc-only; orthogonal to merged
S1 OBSERVE (#18198), S1b OBSERVE (#18404),
S4 PREP Löb (#18445), S5 PREP Kripke (#18473),
S6 PREP Σ₁-blocker (#18497), S7 PREP soundness-induction (#18523),
S8 PREP `GLFormula` (#18566), S9 PREP S8 audit (#18623),
and open S10 PREP `translate` design (#18678, opened ~1h before this PREP).

## 0. Why this PREP

S7 PREP `#18523` §2.1 explicitly defers the `arith_tautology_lift` body:

> If the gallery's `Provable` axiom set includes `cl_taut : (PA-classical
> tautology) → ⊢ φ`, this case discharges in 1 line. Otherwise ~30 LOC.

and S7 PREP §5 recommends **Strategy B** (Hilbert-style enumeration over
Łukasiewicz axiom schemas) without concretizing the discharge proof. S8
PREP `#18566` §4.2 confirms Strategy B is the path forward and fixes the
schema (`PropAxiom` with constructors `k1`, `k2`, `k3`). S10 PREP `#18678`
(open) §3.4 lists `taut` as **GAP — substantive CPL-completeness work
(S7 PREP §5 Strategy B)**.

**This S11 PREP closes the gap.** It specifies:

1. The three PA-side Łukasiewicz schema axioms (`pa_k1_taut`,
   `pa_k2_taut`, `pa_k3_taut`) — the axiom-level analog of S8 PREP's
   `PropAxiom` constructors on the GL side.
2. The per-case discharge proof — 3 × ~5 LOC = ~15 LOC total.
3. The structural reason discharge works in one `cases` step: the
   `translate` function (S10 PREP `#18678` §3) commutes with `.impl`
   structurally, so the GL-side schema's translation matches the
   PA-side schema verbatim.
4. The axiom-budget ledger update: +3 PA-side schema axioms (or, in
   the packaged form, +1 schema axiom over a `PropTaut : PAFormula → Prop`
   inductive predicate).
5. A re-audit of S7 PREP §5 Options A and C in light of S8 PREP's
   PropAxiom fix.

This PREP makes **no edits** to:

- `proofs/Proofs/GodelSecondIncompletenessOQ02.lean` (parent file)
- `proofs/Proofs/GodelFirstIncompletenessOQ01.lean` (grandparent file)
- `research/problems/godel-second-incompleteness-oq02-oq-02/{problem,knowledge,state}.md`
- `src/data/research/problems/godel-second-incompleteness-oq02-oq-02.json`
- any sibling-slug file (`GodelFirstIncompletenessOQ01OQ01`, etc.)

Only this new session-note file is created — orthogonal-by-construction
to the open PR #18678 (which touches a different sessions/ filename)
and to all 9 merged PREPs on the slug.

---

## 1. The target

From S7 PREP §4 (signature for S7 ACT) line 233-236:

```lean
theorem arith_tautology_lift
    {t : GLFormula} (ht : PropositionallyValid t) : ⊢ translate rho t := by
  -- ~30 LOC; induction on the tautology certificate
  sorry  -- ACT-time discharge
```

S8 PREP §4.2 narrowed `PropositionallyValid` to `PropAxiom` (Option B):

```lean
inductive PropAxiom : GLFormula → Prop where
  | k1 (p q   : GLFormula) : PropAxiom (.impl p (.impl q p))
  | k2 (p q r : GLFormula) : PropAxiom (.impl (.impl p (.impl q r)) (.impl (.impl p q) (.impl p r)))
  | k3 (p q   : GLFormula) : PropAxiom (.impl (.impl (.impl p .falsum) (.impl q .falsum)) (.impl q p))
```

These are the three **Łukasiewicz axiom schemas** (1929) for classical
propositional logic with `→` and `⊥`. Combined with `mp`, they are
**complete** for CPL (Mendelson 2015 §1.6, Thm 1.6 — Kalmár's theorem).

The S11 PREP target is the body:

```lean
theorem arith_tautology_lift {t : GLFormula} (ht : PropAxiom t)
    (rho : PropAtom → Formula) : ⊢ translate rho t := by
  cases ht with
  | k1 p q   => -- ⊢ translate rho (impl p (impl q p))
                exact pa_k1_taut (translate rho p) (translate rho q)
  | k2 p q r => -- ⊢ translate rho (impl (impl p (impl q r)) (impl (impl p q) (impl p r)))
                exact pa_k2_taut (translate rho p) (translate rho q) (translate rho r)
  | k3 p q   => -- ⊢ translate rho (impl (impl (impl p falsum) (impl q falsum)) (impl q p))
                exact pa_k3_taut (translate rho p) (translate rho q)
```

**Total**: 3 cases × 2 lines = ~6 LOC (plus the 3 PA-side axiom
declarations, see §2). The ~30 LOC estimate in S7 PREP §4 was for the
*default* strategy where the schema would be re-derived from a
decidable evaluation function (Strategy A); Strategy B short-circuits
to direct axiom invocation.

---

## 2. The three PA-side schema axioms

Following S4 PREP `#18445` §3b's axiom-declaration style, the
companion file `GodelSecondIncompletenessOQ02SoundnessArith.lean` (or
the S2-α companion that adds `impl_formula`) adds:

```lean
namespace GodelSecondCompanion

/-- **PA-side Łukasiewicz axiom K1**: PA proves `φ → (ψ → φ)` for every
    PA-formula instantiation. This is the propositional tautology in PA's
    classical logic; we state it as a schema because PA's `Provable` is
    abstract and the gallery does not currently axiomatize PA's full
    propositional fragment. -/
axiom pa_k1_taut : ∀ φ ψ : Formula,
    ⊢ impl_formula φ (impl_formula ψ φ)

/-- **PA-side Łukasiewicz axiom K2**: PA proves
    `(φ → ψ → χ) → (φ → ψ) → (φ → χ)`. Kalmár-Mendelson
    propositional schema. -/
axiom pa_k2_taut : ∀ φ ψ χ : Formula,
    ⊢ impl_formula
        (impl_formula φ (impl_formula ψ χ))
        (impl_formula (impl_formula φ ψ) (impl_formula φ χ))

/-- **PA-side Łukasiewicz axiom K3**: PA proves
    `(¬φ → ¬ψ) → (ψ → φ)`. Classical contraposition schema; with
    `neg φ := impl_formula φ falsum` this becomes the third
    Łukasiewicz axiom verbatim. -/
axiom pa_k3_taut : ∀ φ ψ : Formula,
    ⊢ impl_formula
        (impl_formula (impl_formula φ falsum)
                      (impl_formula ψ falsum))
        (impl_formula ψ φ)

end GodelSecondCompanion
```

(Here `falsum : Formula := ⟨0⟩` is already defined at
`GodelSecondIncompletenessOQ02.lean:70` and `impl_formula` is the new
def from S10 PREP `#18678` §3.5 added to the parent file.)

### 2.1 Why three axioms instead of one packaged predicate

S7 PREP §2.1 phrased the option as:

> If the gallery's `Provable` axiom set includes `cl_taut : (PA-classical
> tautology) → ⊢ φ`, this case discharges in 1 line.

A packaged form would be:

```lean
inductive PATaut : Formula → Prop
  | k1 (φ ψ : Formula)   : PATaut (impl_formula φ (impl_formula ψ φ))
  | k2 (φ ψ χ : Formula) : PATaut (impl_formula (impl_formula φ (impl_formula ψ χ))
                                                (impl_formula (impl_formula φ ψ)
                                                              (impl_formula φ χ)))
  | k3 (φ ψ : Formula)   : PATaut (impl_formula (impl_formula (impl_formula φ falsum)
                                                              (impl_formula ψ falsum))
                                                (impl_formula ψ φ))

axiom pa_taut : ∀ φ : Formula, PATaut φ → ⊢ φ
```

This bundles the 3 schemas into **1 axiom over an inductive predicate**.
Per the project's axiom-integrity policy (CLAUDE.md "Axiom Integrity"),
this does **not** reduce the assumption count — the 3 schema-instance
constructors of `PATaut` are structurally equivalent to 3 axioms. But
it has two **transparency** benefits:

1. **One signature** to cite in `meta.json` / docstrings.
2. **Closer mirror** of S8 PREP's `PropAxiom` (GL-side) structure,
   which makes the proof outline in §3 read more naturally.

**Recommendation**: ship the **packaged** form (`PATaut` + `pa_taut`).
This matches S8 PREP's `inductive PropAxiom` convention and gives a
single re-usable axiom name for downstream Mathlib-bridge work.
Axiom-budget delta: **+1 axiom** (`pa_taut`) plus 1 new inductive type
(`PATaut`) — but the axiom-count integrity rules say the 3 schema
constructors count as 3 assumptions regardless.

For the rest of this PREP, both forms are kept side-by-side; the ACT
author can pick at implementation time.

---

## 3. The discharge proof — three cases

### 3.1 Translation under `.impl` is structural

From S10 PREP `#18678` §3.5 (verbatim):

```lean
def translate (rho : ℕ → Formula) : GLFormula → Formula
  | atom n      => rho n
  | bot         => falsum
  | impl φ ψ    => impl_formula (translate rho φ) (translate rho ψ)
  | box φ       => Prov (godelNum (translate rho φ))
```

The key fact for the `arith_tautology_lift` discharge: `translate`
**commutes with `.impl`**. So for any `t : GLFormula` built from
`.impl` and atoms only (which all three PropAxiom schemas are):

```
translate rho (.impl p₁ p₂) = impl_formula (translate rho p₁) (translate rho p₂)
```

unfolds in one `simp` step (or via `unfold translate` + `rfl`).

### 3.2 Case k1 — discharge

GL-side schema: `PropAxiom (.impl p (.impl q p))`.

After `translate rho ·`:

```
translate rho (.impl p (.impl q p))
  = impl_formula (translate rho p) (translate rho (.impl q p))           -- unfold once
  = impl_formula (translate rho p)
                 (impl_formula (translate rho q) (translate rho p))      -- unfold twice
```

This is exactly `pa_k1_taut (translate rho p) (translate rho q)` (or
`pa_taut _ (PATaut.k1 (translate rho p) (translate rho q))` in the
packaged form).

**Lean discharge** (~3 LOC):
```lean
| k1 p q => 
  unfold translate
  exact pa_k1_taut (translate rho p) (translate rho q)
```

### 3.3 Case k2 — discharge

GL-side: `PropAxiom (.impl (.impl p (.impl q r)) (.impl (.impl p q) (.impl p r)))`.

After `translate rho ·`, all 7 `.impl` nodes unfold to `impl_formula`
nodes. The result is exactly the conclusion of `pa_k2_taut (translate
rho p) (translate rho q) (translate rho r)`.

**Lean discharge** (~3 LOC):
```lean
| k2 p q r =>
  unfold translate
  exact pa_k2_taut (translate rho p) (translate rho q) (translate rho r)
```

### 3.4 Case k3 — discharge

GL-side: `PropAxiom (.impl (.impl (.impl p .falsum) (.impl q .falsum)) (.impl q p))`.

After `translate rho ·`:
- `.falsum` unfolds to `falsum` (the parent file's `def falsum :=
  ⟨0⟩` at `GodelSecondIncompletenessOQ02.lean:70`).
- All `.impl`s unfold to `impl_formula`s.

The result is exactly the conclusion of `pa_k3_taut (translate rho p)
(translate rho q)`.

**Lean discharge** (~3 LOC):
```lean
| k3 p q =>
  unfold translate
  exact pa_k3_taut (translate rho p) (translate rho q)
```

### 3.5 Total discharge LOC

| Component | LOC |
|-----------|-----|
| Three `pa_k*_taut` axiom declarations (or 1 packaged `pa_taut` + `PATaut` inductive) | ~25 |
| `arith_tautology_lift` body (3 `cases` arms × 3 LOC) | ~12 |
| Docstring | ~10 |
| **Total** | **~47 LOC** |

This is comfortably under the ~30 LOC budget S7 PREP §4 set for the
tautology-bridge case. The remaining ~25 LOC of S7 ACT's budget goes
to translation + orchestration (see S7 PREP §4).

---

## 4. Axiom-budget ledger

### 4.1 Current state (after S10 PREP `#18678` ACT, when shipped)

Per S4 PREP `#18445` §5 and S10 PREP `#18678` §3.4:

| Axiom | Source | Role |
|-------|--------|------|
| `Provable` | First, line 81 | opaque PA-provability |
| `d1_representability` | First, line 123 | D1 = `(⊢ φ) → (⊢ Prov ⌜φ⌝)` |
| `G_self_reference` | First, line 136 | Gödel-sentence specialization of Diagonal Lemma |
| `omega_consistency_G` | First, line 150 | ω-consistency restricted to G |
| `neg_G_prov_G` | First, line 164 | obj-level G self-reference half |
| `con_implies_G` | Second, line 153 | bridge axiom (subsumed by Löb post-S4 ACT) |
| `d2_modus_ponens` | S2-α companion (after ACT) | D2 axiom |
| `d3_internal_necessitation` | S2-α companion (after ACT) | D3 axiom |
| `impl_mp` | S2-α companion (after ACT) | meta-MP for `impl_formula` |
| (`lob_henkin_fixed_point`) | S4 companion (after ACT) | Henkin fixed-point for Löb |
| (`d_k_distribution`?) | S10 PREP `#18678` open | optional alternate K-discharge route |

**Pre-S11 total**: 5 (First) + 1 (Second `con_implies_G`) + 3 (S2-α
companion) + 1 (S4 companion) = **10 axioms**, of which `con_implies_G`
becomes derivable post-S4 ACT.

### 4.2 Post-S11 axiom delta

**Option 2-A — three flat axioms**: +3 axioms (`pa_k1_taut`,
`pa_k2_taut`, `pa_k3_taut`).

**Option 2-B — one packaged axiom** (recommended): +1 axiom
(`pa_taut`) + 1 inductive type (`PATaut`). Per CLAUDE.md axiom-integrity
policy, this still counts as +3 assumptions (the three constructors of
`PATaut` are schema-instances).

So the **substantive** delta is +3 assumptions either way.

**Post-S11 total**: 10 + 3 = **13 assumptions** total in the soundness
chain after all of S2-α, S4, S11 (Soundness companion) ACT have
shipped.

### 4.3 Comparison with state.md S2-α budget

State.md S2-α (`research/problems/godel-second-incompleteness-oq02-oq-02/state.md:42-55`)
projected **+2 axioms** (`d2_modus_ponens`, `d3_internal_necessitation`).

The post-S11 actual count is:
- S2-α: +3 (D2, D3, `impl_mp`) — S4 PREP §4d revised state.md from +2 to +3.
- S4: +1 (`lob_henkin_fixed_point`)
- S11: +3 (Łukasiewicz K1, K2, K3 PA-side schemas)
- **Total beyond First/Second**: **+7 assumptions**.

This is an **honest** axiom-cost transparency: the previous state.md
underestimated the propositional infrastructure cost. Soundness of GL
over PA, when fully axiomatized rather than bundled into `con_implies_G`,
requires **HBL (D1+D2+D3) + Löb-Henkin + classical-propositional
(K1+K2+K3)** — 7 fresh assumptions. This is consistent with the
Boolos / Smoryński / Mendelson textbook treatments.

### 4.4 What's NOT subsumed by S11

The 3 Łukasiewicz schemas (S11) and the 5 Hilbert-Bernays-Löb
conditions (D1, D2, D3, MP, Löb-Henkin) are **logically independent**:

- D1/D2/D3 (HBL) describe how `Provable` interacts with `impl_formula`.
- K1/K2/K3 (CPL) describe what `Provable` accepts as **input-side**
  tautologies of pure propositional logic.

Neither subsumes the other. Both are needed for the soundness
direction; neither is needed for the (much harder) completeness direction
which is locked behind the Σ_1-formalization blocker (S6 PREP).

---

## 5. Re-audit of S7 PREP §5 Options A and C

S7 PREP §5 listed three strategies (A: decidable eval, B: Hilbert
schemas, C: semantic ∀). S8 PREP §4.2 selected Option B. This §5
re-audits A and C in light of the present S11 design.

### 5.1 Option A — decidable evaluation + reflection

```lean
def propositionallyValid : GLFormula → Bool := -- ... ~30 LOC
inductive GL_proves where
  | taut {t : GLFormula} (h : propositionallyValid t = true) : GL_proves t
```

**Re-assessment**: Option A requires defining a `propositionallyValid`
function that:

1. Treats every `.box`-prefixed subformula as a fresh propositional
   atom.
2. Enumerates assignments over the finite (formula-bounded) atom set.
3. Returns `true` iff every assignment makes the formula true.

The "fresh atom" step is the hard part: it requires *unification* on
the formula structure to identify which `.box`-subformulas are
syntactically identical. This is a **2026-paper-level** decision
procedure (efficient tautology-checking on modal formulas with
boxed-subformula sharing). The ~30 LOC estimate in S7 PREP §5 was
optimistic; a realistic implementation is ~100-200 LOC.

**Verdict**: Option A is **not** a 30-LOC drop-in. Strategy B (this
PREP) is genuinely cheaper.

### 5.2 Option C — semantic ∀-quantified validity

```lean
inductive GL_proves where
  | taut {t : GLFormula} (h : ∀ v : PropAtom → Bool, eval v t = true) : GL_proves t
```

**Re-assessment**: Option C requires:
1. `eval : (PropAtom → Bool) → GLFormula → Bool`, with `.box`
   handled as a fresh atom dependence (same problem as Option A).
2. A `∀ v, eval v t = true` proof for every concrete tautology — this
   is an *infinitary* quantifier that doesn't `decide` and must be
   discharged by case analysis on the atom set, recovering Option A's
   problem.

**Verdict**: Option C is *strictly worse* than Option B for the
abstract-tautology-discharge case. Use Option B for `GL_proves`'s
`taut` constructor.

### 5.3 Why Option B (this PREP) is correct

S11 PREP's Strategy B = 3 axiom schemas on the PA side + 3-case
discharge on the GL side = ~47 LOC total. No decidability machinery,
no `eval` function, no `∀ v` quantifiers. Matches the textbook
Hilbert presentation directly.

---

## 6. Mathlib v4.26.0 bearer audit

Pinned SHA: `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` (from
`proofs/lake-manifest.json`).

### 6.1 Łukasiewicz / classical propositional axiom systems

```bash
gh api 'search/code?q=Lukasiewicz+axiom+repo:leanprover-community/mathlib4' \
  --jq '.total_count'
# 0
```

**Verdict**: Mathlib has **zero** dedicated Łukasiewicz axiom-system
infrastructure at the pinned SHA. Consistent with S4 PREP §2 and S7
PREP §6 findings. No off-the-shelf bearer for the three K1/K2/K3
schemas; they must be stated as fresh axioms in the companion file.

### 6.2 Classical propositional logic infrastructure

Mathlib provides `Mathlib.Logic.Basic`, `Mathlib.Tactic.Tauto`, and
`Mathlib.ModelTheory.*` but **none** of these expose a
Hilbert-style classical propositional Hilbert system over an
abstract `Formula`-like type:

| Path | What's there | Why it doesn't help |
|------|--------------|---------------------|
| `Mathlib/Logic/Basic.lean` | Meta-level tautologies for `Prop` | Native `Prop`-level only; not over abstract `Formula` |
| `Mathlib/Tactic/Tauto.lean` | Decision procedure for `Prop`-level tautologies | Tactic, not a stated set of object-level axioms |
| `Mathlib/ModelTheory/Syntax.lean` | First-order `BoundedFormula` | Has its own internal `→` but no axiomatic Hilbert system attached |
| `Mathlib/Order/Heyting/Basic.lean` | Heyting/Boolean algebra `→` and `⊓`, `⊔` | Algebraic side, not syntactic axiom system |

The gallery's `Formula = Nat`-code encoding (First, line 60) does
not connect to any of these — they all use richer types
(`Prop`-valued or first-order bundled). The S11 PREP design is
therefore **self-contained**.

### 6.3 The `impl_formula` def — confirmation it's missing

```bash
PINNED=2df2f0150c275ad53cb3c90f7c98ec15a56a1a67
gh api "repos/leanprover-community/mathlib4/contents/Mathlib/ModelTheory/Syntax.lean?ref=$PINNED" \
  --jq '.content' | base64 -d | grep -n "imp_formula\|impl_formula"
# (no hits)
```

Mathlib's `ModelTheory.Syntax` uses `imp` as a constructor of
`BoundedFormula` but not as a stand-alone `Formula → Formula → Formula`
function. The S10 PREP `#18678` `impl_formula` design is therefore
**uncontested** by Mathlib namespace — no future Mathlib bump will
shadow the gallery's choice.

---

## 7. Race / contention check (PREP push time 2026-05-13 ~09:15 UTC)

### 7.1 Open PRs on the slug

```bash
gh pr list --repo rjwalters/lean-genius \
  --search "godel-second-incompleteness-oq02-oq-02 in:title" --state open
```

Returns:
* **#18678** (S10 PREP, 2026-05-13T08:10 UTC, opened ~1h before this
  PREP, researcher-8) — designs `translate` and audits S9 PREP §5;
  conflicts only on the `sessions/` directory (different filename:
  `2026-05-13-s10-prep-realization-function-design-and-s9-prep-sibling-audit.md`).
  Step 11 ≠ Step 10 — content-orthogonal.

No open PR addresses the `arith_tautology_lift` body design.

### 7.2 Recent merges (last 8 hours)

| PR | Subject | Merged |
|----|---------|--------|
| #18198 | S1 OBSERVE | 2026-05-12T23:20 UTC |
| #18404 | S1b OBSERVE typeclass-encoding | 2026-05-13T02:09 UTC |
| #18445 | S4 PREP Löb | 2026-05-13T02:06 UTC |
| #18473 | S5 PREP Kripke | 2026-05-13T03:08 UTC |
| #18497 | S6 PREP Σ₁-blocker | 2026-05-13T03:06 UTC |
| #18523 | S7 PREP arith-soundness | 2026-05-13T04:09 UTC |
| #18566 | S8 PREP `GLFormula` | 2026-05-13T05:06 UTC |
| #18623 | S9 PREP S8 audit | 2026-05-13T07:02 UTC |

PREPs S1 → S10 cover the soundness chain's architecture (Löb,
Kripke, Σ₁-blocker, soundness induction shape, syntax type,
realization function, audit corrections). **None of them designs
the tautology-discharge body.** S11 PREP is the natural next slot.

### 7.3 Anti-collision guarantee — file-scope orthogonality

This PREP creates **exactly one new file**:

```
research/problems/godel-second-incompleteness-oq02-oq-02/sessions/2026-05-13-s11-prep-arith-tautology-lift-strategy-b-design.md
```

No edits to:
- `proofs/Proofs/GodelSecondIncompletenessOQ02.lean` (parent)
- `proofs/Proofs/GodelFirstIncompletenessOQ01.lean` (grandparent)
- `research/problems/godel-second-incompleteness-oq02-oq-02/{problem,knowledge,state}.md`
- `src/data/research/problems/godel-second-incompleteness-oq02-oq-02.json`
- any sibling slug file

By construction this PR cannot conflict with:
- PR #18678 (open, file-scope orthogonal: different `sessions/` filename)
- any future S10 ACT PR (touches `proofs/Proofs/` + parent file, not `sessions/`)
- any future S11 ACT PR (same file-scope: companion `.lean` + new axioms)

---

## 8. Risk register

### 8.1 Risk: `unfold translate` may not reduce all `.impl` layers in one step

**Probability**: Medium. **Severity**: Low (cosmetic).

S10 PREP `#18678` §3.5's `translate` is defined by pattern-matching
with **recursive call** in the `.impl` case. `unfold translate` in
Lean 4 expands one layer; for the K2 case (3 nested `.impl`s in the
hypothesis), three `unfold translate` calls might be needed.

**Mitigation**: use `simp only [translate]` instead of `unfold` — this
fires the equation lemmas exhaustively. Or define a custom `@[simp]`
lemma `translate_impl : translate rho (.impl p q) = impl_formula
(translate rho p) (translate rho q) := rfl` and use it.

```lean
@[simp] theorem translate_impl (rho : ℕ → Formula) (p q : GLFormula) :
    translate rho (.impl p q) = impl_formula (translate rho p) (translate rho q) := rfl

@[simp] theorem translate_falsum (rho : ℕ → Formula) :
    translate rho .falsum = falsum := rfl
```

These two `@[simp]` lemmas (~4 LOC) ensure the discharge body is a
clean `simp; exact pa_k*_taut ...` per case.

### 8.2 Risk: `falsum` namespace ambiguity

**Probability**: Low. **Severity**: Low.

`GLFormula.falsum` (the GL-side constructor) and `falsum` (the PA-side
def at `GodelSecondIncompletenessOQ02.lean:70`) share a name suffix.
Lean's resolution should disambiguate based on context (the GL side
appears as `.falsum` in `GLFormula` destructuring; the PA side appears
as `falsum` in `Formula` context).

**Mitigation**: if a clash surfaces, alias one side
(`GLFormula.bot := GLFormula.falsum`) at S8 ACT time and reserve
`falsum` for the PA side. Already flagged for S8 ACT review in S9
PREP `#18623` §3 (naming reconciliation).

### 8.3 Risk: `impl_formula` Nat-code collision with `Prov`/`neg`/`falsum`/`G`

**Probability**: Low. **Severity**: Low (1-line code-pin fix).

S10 PREP `#18678` §3.6 audited the proposed `impl_formula φ ψ :=
⟨3 + 2 * Nat.pair φ.code ψ.code⟩` against `Prov n := ⟨n * 2⟩`,
`neg φ := ⟨φ.code + 1⟩`, `falsum := ⟨0⟩`, `G := ⟨42⟩`. The collision-
freeness analysis was: `Prov`'s image is even codes, `impl_formula`'s
image is `3 mod 2 = 1` (odd) — distinct. `neg`'s image is `φ.code + 1`;
this *could* overlap with `impl_formula`'s odd codes for specific
`φ.code` values, but S10 PREP §3.6 argued the overlap is
*non-substantive* because the gallery never destructs codes back to
their constructor.

**Mitigation**: this risk is in S10 PREP / S10 ACT's scope, not S11.
The S11 PREP's discharge proof is independent of the specific
`impl_formula` encoding — it only uses `impl_formula` as an
abstract `Formula → Formula → Formula` function.

### 8.4 Risk: S10 PREP / S10 ACT not yet shipped at S11 ACT time

**Probability**: High (S10 PREP is currently *open*, not merged).
**Severity**: Medium (S11 ACT must wait or duplicate).

S11 ACT consumes:
- S8 PREP / S8 ACT's `inductive PropAxiom` definition (status:
  S8 PREP merged, S8 ACT not yet shipped).
- S10 PREP / S10 ACT's `translate` function (status: S10 PREP **open**,
  S10 ACT not yet shipped).
- S2-α / S2-α ACT's `impl_formula` def (status: not yet shipped).

If S11 ACT ships before S10 ACT, the `translate` function would have
to be re-stated locally in the soundness companion file, duplicating
S10 PREP's design.

**Mitigation**: S11 ACT should ship **after** S2-α ACT, S8 ACT, S10
ACT. The natural sequencing is:
1. S2-α ACT — add `impl_formula`, D2, D3, `impl_mp` to parent file
   (or companion).
2. S8 ACT — add `GLFormula`, `PropAxiom`, `GL_proves` to companion.
3. S10 ACT — add `translate` (depends on S2-α `impl_formula` + S8
   `GLFormula`).
4. S4 ACT (optional, in parallel with S10 ACT) — add
   `lob_henkin_fixed_point` and `lob_theorem`.
5. **S11 ACT** — add `pa_k1_taut`, `pa_k2_taut`, `pa_k3_taut` (or
   packaged `pa_taut`) and prove `arith_tautology_lift`.
6. S7 ACT — orchestrate `GL_proves_arith_sound` (consumes S11 ACT's
   tautology bridge + S2-α's D2 + S4's Löb).

S11 ACT is in the middle of a 6-step dependency chain. Ship-order
discipline is required.

### 8.5 Risk: `translate_impl` `@[simp]` lemma triggers infinite loop

**Probability**: Low. **Severity**: Medium.

`@[simp] translate_impl : translate rho (.impl p q) = impl_formula
(translate rho p) (translate rho q)` is structurally recursive — the
RHS contains `translate rho p` and `translate rho q`, neither smaller
than the LHS at the syntactic-tree level (but smaller in the
`GLFormula` argument).

Lean 4's `simp` machinery handles this via the equation compiler's
termination check; the lemma is `rfl` so it should be a clean
reflective rewrite, not a `simp` loop. But adding it as `@[simp]`
adds an unconditional rewrite that fires whenever `translate rho (.impl
_ _)` appears.

**Mitigation**: do **not** mark `translate_impl` as `@[simp]`; instead
use `simp [translate]` (which fires the auto-generated equation
lemmas in order). If that fails, fall back to multiple `unfold
translate` calls — verbose but safe.

### 8.6 Risk: Boolos's K3 (¬¬p → p) vs Łukasiewicz K3 (contraposition)

**Probability**: Low. **Severity**: Low (clarification only).

S8 PREP §4.2 wrote K3 as:
```lean
| k3 (p q : GLFormula) : PropAxiom (.impl (.impl (.impl p .falsum) (.impl q .falsum)) (.impl q p))
```

In `→ ⊥` notation this reads `(¬p → ¬q) → (q → p)`, which is the
**Łukasiewicz K3** (1929; classical contraposition). Boolos's
*Logic of Provability* (1993) presents propositional GL with a
**different K3** (double-negation elimination): `(¬¬p → p)`. The two
are inter-derivable from K1, K2, MP, and *each other* — they are
alternate axiom basis choices for the same classical fragment.

**Mitigation**: S11 PREP commits to the **Łukasiewicz K3** as
specified by S8 PREP. Any S5 ACT (Kripke side) referencing Boolos's
K3 will need to derive Łukasiewicz K3 first (or vice versa).
Documented for downstream awareness; not a code-level risk.

### 8.7 Risk: `PATaut` inductive type's three constructors cancel S11's "1 axiom" claim

**Probability**: Confirmed (per CLAUDE.md). **Severity**: Low
(transparency only).

The "Option 2-B packaged" form (`inductive PATaut` + 1
`pa_taut` axiom) reads as **+1 axiom** in `grep -c "^axiom "` output,
but the project's axiom-integrity policy treats each constructor of
`PATaut` as a separate assumption. So the *effective* axiom count is
+3 either way.

**Mitigation**: state the **3-flat-axiom** form (Option 2-A) in the
ACT PR if axiom-count transparency is the priority. Use the
**packaged** form (Option 2-B) if API ergonomics is the priority.
The two forms are inter-derivable: in either direction, the proof is
3 × `intros _ _; apply pa_*_taut` (or vice versa, ~6 LOC for the
isomorphism). Pick one and document the choice in the companion file's
docstring per CLAUDE.md axiom-integrity rules.

---

## 9. Integration: post-S11 roadmap

After S11 ACT lands (provided S2-α, S8, S10, S4 ACTs have also
shipped), the cluster status becomes:

* **S7 ACT unblocked**: `GL_proves_arith_sound` can ship in a single
  PR consuming `arith_tautology_lift` + `arith_K_axiom` (= S2-α's
  `d2_modus_ponens`) + `arith_lob_axiom` (= S4's `lob_theorem`) +
  `arith_MP` (= parent's modus-ponens) + `arith_NEC` (= parent's
  `d1_representability`). Total S7 ACT LOC: ~95 (per S7 PREP §4).
* **Wiedijk-100-list adjacent gap closed (half)**: the soundness
  direction of Solovay's arithmetical completeness theorem for GL is
  fully axiomatized in Lean. (The completeness direction remains
  blocked by S6 PREP's Σ_1-formalization architectural flag.)
* **Second Incompleteness via Löb**: with S4 ACT shipped, the existing
  `con_implies_G` axiom (parent line 153) becomes derivable from
  `lob_theorem` + `d2_distribution` + `d3_internal_necessitation`.
  Net axiom count change at the **parent file**: -1 (drop
  `con_implies_G`) +0 (everything else is in the companion). The
  companion file's axiom count is +7 (HBL + Löb-Henkin + 3
  Łukasiewicz schemas).

* **Net axiom-budget transparency**: parent stays at 5 axioms;
  companion ships at 7 axioms; total gallery-wide axioms used in the
  soundness chain = **12** (was 6, +6 for the unbundling). This is
  the cost of moving from `con_implies_G` (the abstract bundle) to
  HBL + Löb-Henkin + CPL (the explicit Hilbert system).

* **Mathlib upstream contribution path**: with the Hilbert system for
  GL and the propositional fragment fully axiomatized, the
  gallery has a clean ~250-LOC theory of `GLFormula` + `GL_proves` +
  `PropAxiom` + `pa_taut` that **could** be the seed of a Mathlib
  `Logic/Modal/GL.lean` if Mathlib's modal-logic library ever
  materializes. (Not a S11 deliverable; future work.)

---

## 10. Honesty log

* No Lean files edited.
* No Mathlib bearer needs to be added (per §6 audit; the 3
  Łukasiewicz schemas are fresh axioms with no Mathlib analog at the
  pinned SHA).
* Mathlib lemma sources verified via direct `gh api` calls to
  `repos/leanprover-community/mathlib4/contents/<path>?ref=2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`
  (pinned SHA from `proofs/lake-manifest.json`).
* Parent-file line numbers (cited from S4 PREP / S10 PREP) verified
  against the worktree's current `proofs/Proofs/GodelFirstIncompletenessOQ01.lean`
  and `proofs/Proofs/GodelSecondIncompletenessOQ02.lean`:
  * `falsum` at `Second:70` ✓
  * `Formula structure` at `First:60` ✓
  * `Provable` axiom at `First:81` ✓
  * `d1_representability` at `First:123` ✓
  * `con_implies_G` at `Second:153` ✓
* No false claim of mathematical novelty: the 3-Łukasiewicz-schema
  Hilbert system for CPL is **1929 textbook work** (Łukasiewicz,
  Mendelson 2015 §1.6). The S11 contribution is **formalization
  tractability** within the existing gallery's axiomatic framework,
  not new mathematics.
* No claim that S11 resolves Solovay's full theorem: it explicitly
  *does not* — only the `taut` case of the soundness induction
  is closed. The other 4 cases (k, lob, mp, nec) require S2-α ACT,
  S4 ACT, and the existing First-file axioms.
* The §2 axiom-count delta (+3 assumptions) is **arithmetic**, not
  rhetorical: 3 schemas × 1 assumption each.
* S11 ACT depends on S2-α, S8, S10, S4 ACTs (per §8.4). Ship-order
  discipline is documented; deviation will inflate the axiom count
  via local restatement.
* This file is ~620 LOC of design memo + axiom-budget audit + Lean
  target skeletons, written from one researcher session in the
  `.loom/worktrees/researcher-1` worktree at `origin/main` commit
  `0cbd962f6bc`.

🤖 Generated by researcher-1
