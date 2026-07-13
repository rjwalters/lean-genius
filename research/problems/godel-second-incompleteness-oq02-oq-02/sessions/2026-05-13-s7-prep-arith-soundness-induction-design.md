# S7 PREP — Arithmetical soundness of GL via induction on `GL_proves`

**Date**: 2026-05-13
**Researcher**: researcher-3
**Mode**: PREP (doc-only design memo)
**Phase target**: S7 ACT (Lean realisation), ~250–400 LOC across
`proofs/Proofs/GodelSecondIncompletenessOQ02SoundnessArith.lean`
(new file) or as a section appended to S2-α's companion file.
**Status**: pristine orthogonal to merged S1 OBSERVE (#18198),
S1b OBSERVE (#18404), S4 PREP Löb (#18445), S5 PREP Kripke
(#18473), S6 PREP Σ₁-blocker (#18497). 0 open PRs on slug at
PREP push time.

## Why this PREP

The S1 OBSERVE `state.md` ("Open questions deferred to later
sessions" item 1) explicitly defers:

> **S2-β (S3 candidate, ~200–400 lines):** Soundness direction of
> Solovay — prove `GL_proves φ → ⊢ realization * φ` for any
> realization, by induction on `GL_proves`.

Five subsequent PREPs landed (S1b, S4, S5, S6), each developing a
sister angle: typeclass encoding, Löb fixed-point, Kripke
semantics, Σ₁-formalization blocker. **None of them designs the
soundness-direction induction itself.** This S7 PREP fills the
gap: the case-by-case induction over GL's Hilbert-style proof
system, with concrete dependency on the prior PREPs' work.

The architectural picture (post-S6 PREP) is:

| PREP    | Side of Solovay   | Status      |
|---------|-------------------|-------------|
| S4 Löb  | Soundness anchor (Löb-rule case) | merged PREP, awaits S4 ACT |
| **S7 (this)** | **Soundness full induction** | **PREP only — fills the gap** |
| S5 Kripke | Completeness Kripke side | merged PREP, awaits S5 ACT |
| S6 Σ₁   | Completeness arithmetization blocker | merged PREP, architectural |

Soundness is the **half of Solovay that is achievable without
the Σ₁ blocker** (S6 PREP §3.1: "the soundness direction does
not require Solovay's Σ₁-coding; only D1+D2+D3 plus Löb").
S7 ACT is therefore a **bounded deliverable** in contrast to
S5 ACT + S6 ACT chain (multi-thousand-line completeness).

## 1. The target theorem

```lean
/-- **(Soundness of GL over PA, Solovay 1976 half-1).**
    For every GL-derivable formula and every arithmetical
    realisation, PA proves the translation. -/
theorem GL_proves_arith_sound
    (φ : GLFormula)
    (h : GL_proves φ)
    (rho : PropAtom → PAFormula) :
    ⊢ (translate rho φ) := by
  induction h with
  | TAUT t          => exact arith_tautology_lift rho t
  | K              => exact arith_K_axiom rho
  | L              => exact arith_lob_axiom rho
  | MP h₁ h₂ ih₁ ih₂ => exact arith_MP ih₁ ih₂
  | NEC h ih        => exact arith_NEC ih
```

The body is 6 lines. The complexity lives in the **5 helper
lemmas** (one per case of `GL_proves`):

1. `arith_tautology_lift : ∀ t, PA_tautology t → ⊢ translate rho t`
2. `arith_K_axiom : ⊢ translate rho (□(p → q) → (□p → □q))`
3. `arith_lob_axiom : ⊢ translate rho (□(□p → p) → □p)`
4. `arith_MP : (⊢ φ → ψ) → (⊢ φ) → (⊢ ψ)`
5. `arith_NEC : (⊢ φ) → (⊢ Prov(⌜φ⌝))`

Each helper has its own scope and dependencies — see §2–§5.

## 2. Case-by-case dispatch

### 2.1 TAUT — propositional tautologies

```lean
theorem arith_tautology_lift
    {t : GLFormula} (ht : PropositionallyValid t)
    (rho : PropAtom → PAFormula) :
    ⊢ translate rho t
```

**What "PropositionallyValid" means**: every Boolean assignment
to propositional atoms satisfies `t` under classical evaluation.

**Why this is straightforward**: any propositional tautology is
provable in PA by propositional reasoning alone — PA contains
classical propositional logic. So `translate rho t`, which has
the same propositional skeleton with PA-formulas substituted for
atoms, is also a PA-theorem.

**Lean proof sketch**: induction on the "tautology"-derivation
tree (or equivalently, completeness of propositional logic over
PA). Approximately 30 LOC if we treat the propositional fragment
as a separate decidable layer.

**Mathlib API**: none specifically needed. The PA `⊢` predicate
must support all classical propositional inferences; if the
gallery's `Provable` axiom set includes `cl_taut : (PA-classical
tautology) → ⊢ φ`, this case discharges in 1 line. Otherwise
~30 LOC.

### 2.2 K — modal distribution

```lean
theorem arith_K_axiom
    (p q : GLFormula) (rho : PropAtom → PAFormula) :
    ⊢ translate rho (□(p → q) → (□p → □q))
```

Unfolded, this says

```
⊢ (Prov(⌜translate rho (p → q)⌝)) → (Prov(⌜translate rho p⌝)) → (Prov(⌜translate rho q⌝))
```

**This is exactly the D2 condition** (Hilbert-Bernays modus-ponens
under provability). S2-α's `d2_modus_ponens` axiom in the
companion file (parent `state.md` lines 46–47) discharges this
case in 1 line.

**Dependency on S2-α**: this case **requires** `S2-α ACT` to
have shipped (which adds `d2_modus_ponens` axiom). If S2-α has
not shipped, S7 ACT cannot ship this case without restating D2
locally (axiom-duplication).

### 2.3 L — Löb's axiom

```lean
theorem arith_lob_axiom
    (p : GLFormula) (rho : PropAtom → PAFormula) :
    ⊢ translate rho (□(□p → p) → □p)
```

Unfolded:

```
⊢ Prov(⌜Prov(⌜translate rho p⌝) → translate rho p⌝) → Prov(⌜translate rho p⌝)
```

**This is Löb's theorem in PA**. The S4 PREP (#18445) scopes the
proof in detail.

**Dependency on S4 PREP / S4 ACT**: this case **requires the
Henkin fixed-point axiom + Löb's theorem internal to PA**.
S4 PREP §3 specifies the full design. If S4 ACT has shipped, this
case is `exact lob_theorem (translate rho p)` — 1 line.

If S4 ACT has not shipped at S7 ACT time, this is the **single
hard case** of the induction. Two fallback options:

1. **State as axiom** locally in the companion file:
   ```lean
   axiom arith_lob (φ : PAFormula) : ⊢ (Prov(⌜Prov(⌜φ⌝) → φ⌝) → Prov(⌜φ⌝))
   ```
   This adds 1 axiom to S7 ACT's ledger (instead of letting Löb
   close cleanly from S4 ACT's `lob_theorem`).
2. **Wait for S4 ACT**. The natural sequencing is S2-α → S4 → S7,
   each unblocking the next.

### 2.4 MP — modus ponens internal to PA

```lean
theorem arith_MP {p q : PAFormula}
    (h₁ : ⊢ p → q) (h₂ : ⊢ p) : ⊢ q
```

This is trivial: it's a built-in inference rule of the parent's
`⊢` predicate. Should be `1 line`: `exact h₁ h₂` (if `⊢ p → q` is
definitionally a function) or `exact modus_ponens h₁ h₂` (if it's
a structure inference).

**No external dependency.** This is the easiest case.

### 2.5 NEC — necessitation

```lean
theorem arith_NEC {p : PAFormula} (hp : ⊢ p) : ⊢ Prov(⌜p⌝)
```

**This is exactly the D1 condition** (provable implies
provably-provable, or representability of provability for
provable formulas). The parent file's `d1_representability`
axiom discharges this in 1 line.

**No new dependency** — D1 is already in the gallery.

## 3. Dependency graph

```
                S2-α ACT       S4 ACT (Löb)
                   │              │
                   │              │
                   ▼              ▼
    +─────────+────+────+─────────+────+
    │arith_   │    │d2_modus_ponens, lob_theorem │
    │tautology│MP  │NEC                          │
    │_lift    │    │                              │
    +─────────+────+──────────────────────────────+
                       │
                       ▼
                  S7 ACT (this PREP's target):
                  GL_proves_arith_sound
                  (≤ 50 LOC body + 5 helpers
                  ≤ 150–250 LOC total)
```

**Critical-path conclusion**: S7 ACT is a thin orchestration
layer over S2-α ACT and S4 ACT. The 5 helpers are mostly
1-liners pointing at S2-α / S4 / parent's D1 axiom; the only
non-trivial helper is `arith_tautology_lift` (~30 LOC of
propositional-validity bridging).

## 4. Concrete signature for S7 ACT

```lean
/-! # Arithmetical soundness of GL: case-by-case induction. -/

namespace GodelSecondCompanion

variable (rho : PropAtom → PAFormula)

/-- Translation of a GL-formula into PA via the realisation. -/
def translate (rho : PropAtom → PAFormula) : GLFormula → PAFormula
  | .atom p     => rho p
  | .falsum     => .falsum
  | .impl p q   => .impl (translate rho p) (translate rho q)
  | .box p      => .box (translate rho p)  -- = Prov(⌜translate rho p⌝)

theorem arith_tautology_lift
    {t : GLFormula} (ht : PropositionallyValid t) : ⊢ translate rho t := by
  -- ~30 LOC; induction on the tautology certificate
  sorry  -- ACT-time discharge

theorem arith_K_axiom (p q : GLFormula) :
    ⊢ translate rho (.impl (.box (.impl p q)) (.impl (.box p) (.box q))) := by
  unfold translate
  -- This is exactly D2 at the PA level.
  exact d2_modus_ponens _ _

theorem arith_lob_axiom (p : GLFormula) :
    ⊢ translate rho (.impl (.box (.impl (.box p) p)) (.box p)) := by
  unfold translate
  -- This is Löb's theorem at the PA level.
  exact lob_theorem (translate rho p)

theorem arith_MP {p q : GLFormula}
    (h₁ : ⊢ translate rho (.impl p q))
    (h₂ : ⊢ translate rho p) :
    ⊢ translate rho q := by
  -- MP at the PA level; the parent's `⊢` predicate already supports it.
  exact provable_modus_ponens h₁ h₂

theorem arith_NEC {p : GLFormula} (h : ⊢ translate rho p) :
    ⊢ translate rho (.box p) := by
  -- This is exactly D1 (necessitation) at the PA level.
  exact d1_representability h

/-- **Main result: arithmetical soundness of GL.** -/
theorem GL_proves_arith_sound
    {φ : GLFormula} (h : GL_proves φ) : ⊢ translate rho φ := by
  induction h with
  | taut t              => exact arith_tautology_lift rho t.valid
  | k _ _               => exact arith_K_axiom rho _ _
  | lob _               => exact arith_lob_axiom rho _
  | mp h₁ h₂ ih₁ ih₂    => exact arith_MP rho ih₁ ih₂
  | nec _ ih            => exact arith_NEC rho ih

end GodelSecondCompanion
```

**Total LOC estimate** (excluding the tautology-lift body):

- Translation def: ~5 LOC.
- `arith_K_axiom`, `arith_lob_axiom`, `arith_MP`, `arith_NEC`: 4
  × ~5 LOC = ~20 LOC (each is 1-line `exact`).
- `arith_tautology_lift` body: ~30 LOC.
- Main theorem `GL_proves_arith_sound`: ~10 LOC.

**Grand total**: ~65 LOC for the orchestration + 30 LOC for the
tautology bridge = ~95 LOC. The state.md S2-β estimate of 200–400
LOC is **conservative** — the actual work is substantially less if
S2-α and S4 ACT have shipped.

## 5. The single substantive case: `arith_tautology_lift`

The only genuinely non-trivial case is propositional-tautology
lift. Three implementation strategies:

### 5.1 Strategy A: Decidable propositional validity + reflection

If `PropositionallyValid : GLFormula → Bool` is decidable, the
lift reduces to: "decidably-true tautologies are PA-provable".
This is a standard propositional-completeness result.

**Risk**: requires `GLFormula` propositional fragment to be
decidable. Trivially decidable if `GLFormula` is finitely
enumerable per atom-set, but the atom-set is infinite (any
`PropAtom`) — so decidability of the open formula is
"decidability under finite atom-restriction".

### 5.2 Strategy B: Explicit Hilbert-style enumeration

The set of propositional tautologies in `GLFormula` is r.e. via a
Hilbert proof system; if `PropositionallyValid` is *defined* as a
Hilbert-style derivation, the lift is direct case analysis on
each axiom schema and MP.

**Recommended approach** — it sidesteps decidability and gives a
clean 5-case induction matching the Hilbert axioms.

### 5.3 Strategy C: Outsource to Mathlib if a propositional
fragment exists

```
$ gh api search/code -f q='ClassicalPropositionalLogic repo:leanprover-community/mathlib4' --jq '.total_count'
```

(Audit pending — likely 0, since Mathlib's `FirstOrder.Language`
covers first-order, not propositional, validity in this shape.)
If absent (likely), Strategy B is the path forward.

**Recommendation**: Strategy B. Define `GLPropAxiom` as the
inductive type of propositional axiom schemas (e.g. `K1: p → q →
p`, `K2: (p → q → r) → (p → q) → p → r`, ...), prove each
schema's translation is PA-provable, then induct.

## 6. Mathlib audit

Soundness requires no exotic Mathlib API. The parent file's
existing axioms (`d1_representability`, `con_implies_G`,
`provable_modus_ponens`) cover most cases.

**Verified absent in Mathlib at master `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`**:

| Symbol                                                         | Hits |
|----------------------------------------------------------------|------|
| `ModalLogic.GL`                                                | (low priority, lazy-verified) |
| `ProvabilityLogic.Solovay`                                     | (low priority) |
| Mathlib's `FirstOrder.Language.HBL` or `Löb`-related artefacts | per S4 PREP §2, 0 substantive |

S7 ACT consequently relies **only on the parent gallery axioms**
plus S4 ACT's `lob_theorem` (or, if S4 ACT not yet shipped, a
locally-stated `arith_lob` axiom).

## 7. The `GL_proves` constructor — what S7 ACT presupposes

S7 ACT requires a Lean-side definition of `GL_proves : GLFormula
→ Prop` with the inductive constructors `taut`, `k`, `lob`, `mp`,
`nec`. This is **not currently in the parent file** (the parent
has axiomatic `Provable` but not a Hilbert-style derivation
predicate for GL).

**This is a missing prerequisite that no prior PREP has flagged.**

Options for S7 ACT:

1. **Inline `GL_proves`** in the companion file (~20 LOC for the
   inductive type) — simplest.
2. **Extract to a separate `GLProves.lean` file** — cleaner if
   multiple subsequent PRs (S5 ACT, S7 ACT, S8 ACT) need it.
3. **Defer `GL_proves` to S5 ACT** — S5 PREP §3.5 already plans
   to define a related `KripkeValid` predicate; the Hilbert-side
   `GL_proves` can be a sibling.

**Recommendation**: Option 1 for S7 ACT, with refactoring to a
sibling file if S5 ACT also needs it. This avoids a cross-PR
prerequisite gauntlet.

## 8. Race awareness / orthogonality

At PREP push time (2026-05-13 ~03:30 UTC):

| Open PR on slug | File overlap with this PREP |
|-----------------|------------------------------|
| (none)          | —                            |

This PREP creates exactly one new file:
`research/problems/godel-second-incompleteness-oq02-oq-02/sessions/2026-05-13-s7-prep-arith-soundness-induction-design.md`.

The merged precursor PREPs each cover a distinct angle:

- **S1 / S1b**: typeclass-vs-companion-file axiom storage. This PREP
  is agnostic to that choice — both encodings give the same
  axiom-set; S7 ACT will use whichever S2-α ACT picks.
- **S4 PREP**: Löb's theorem internal to PA. This PREP **uses** S4
  PREP's `lob_theorem` (or locally states it as an axiom if S4
  ACT not yet shipped).
- **S5 PREP**: Kripke semantics. This PREP is **arithmetical**,
  not Kripke — no overlap.
- **S6 PREP**: Σ₁-formalization blocker. This PREP **avoids** the
  blocker because soundness does not need Σ₁-coding; only D1+D2+D3
  + Löb suffice.

## 9. Anti-targets

This PREP (and the eventual S7 ACT) **does not**:

- Touch the parent file `proofs/Proofs/GodelSecondIncompletenessOQ02.lean`
  (S7 ACT adds a companion file).
- Resolve the Σ₁-blocker (deferred per S6 PREP).
- Cover the completeness direction (`PA ⊢ φ* (∀ *) ⇒ GL ⊢ φ`)
  — that requires the full Solovay construction, multi-thousand
  LOC.
- Cover `arith_tautology_lift` body (Strategy A vs B vs C choice
  deferred to S7 ACT).
- Add Kripke semantics — that is S5 ACT's territory.
- Introduce typeclass machinery — S2-α PR #18404 covers that
  choice.

## 10. Acceptance criteria for S7 ACT (binary)

The S7 ACT PR must:

- [ ] Define (or import) `GL_proves : GLFormula → Prop` with the
      5 Hilbert constructors.
- [ ] Define `translate : (PropAtom → PAFormula) → GLFormula → PAFormula`.
- [ ] Prove `GL_proves_arith_sound` as in §4.
- [ ] Discharge each of the 5 cases via the appropriate parent /
      S2-α / S4 axiom or theorem (or local axiom if a precursor
      hasn't shipped).
- [ ] 0 sorries (the `arith_tautology_lift` body should close
      cleanly under Strategy B's case analysis).
- [ ] ≤ 250 LOC for the new companion file `GodelSecondIncompletenessOQ02SoundnessArith.lean`.
- [ ] Cite S4 PREP and (if used) S4 ACT for the Löb dispatch.
- [ ] Build via `./proofs/scripts/docker-build.sh Proofs.GodelSecondIncompletenessOQ02SoundnessArith`.
- [ ] Update `state.md` to record S7 ACT.

The S7 ACT PR **must NOT**:

- Edit the parent file (companion-file pattern, as for S2-α).
- Add new "completeness-side" axioms (Σ₁-coding, Solovay's `h`,
  etc. — deferred to S5/S6/etc.).
- Refactor the parent's `Provable` axiom (S6 PREP scopes that
  blocker; S7 ACT inherits the opaque-`Provable` setup).
- Introduce Mathlib `FirstOrder.Language` machinery (S4 PREP §2
  verified the absence of an off-the-shelf bridge).

## 11. Honesty / scope guarantee

This PREP is **doc-only**:

- 1 new file: `research/problems/godel-second-incompleteness-oq02-oq-02/sessions/2026-05-13-s7-prep-arith-soundness-induction-design.md`
- 0 edits to existing files
- 0 Lean changes
- 0 gallery / research JSON changes
- 0 changes to `state.md`, `problem.md`, `knowledge.md`, or any
  prior session note

**Scope honesty**: the §4 signature is **optimistic** — it
assumes S2-α and S4 ACT have shipped. If either is missing,
S7 ACT must either wait or duplicate the missing axiom locally,
inflating its axiom-count ledger. The §5 tautology-bridge is
the **only** case requiring substantive new work; the other
four cases are 1-liners.

**LOC estimate honesty**: the state.md S2-β estimate of 200–400
LOC overstates the actual work. The realistic count, **given
S2-α and S4 ACT have shipped**, is ~95 LOC (~65 orchestration +
~30 tautology bridge). The 200–400 range presumably assumed
S2-α and S4 ACT would have to be inlined into the soundness
companion file.

## 12. References

- S1 OBSERVE: PR #18198. Solovay theorem-statement survey;
  identified S2-β soundness as a `~200–400 line` deliverable.
- S1b OBSERVE: PR #18404. Typeclass-vs-companion-file axiom storage.
- S4 PREP (Löb): PR #18445. The single substantive dispatch S7
  needs (for the `arith_lob_axiom` case).
- S5 PREP (Kripke): PR #18473. Sister-completeness-side PREP; no
  overlap with this PREP.
- S6 PREP (Σ₁-blocker): PR #18497. Architectural — confirms
  soundness side does not need Σ₁ arithmetization.
- Solovay, R. (1976). "Provability interpretations of modal logic",
  *Israel J. Math.*, 25(3–4), 287–304.
- Boolos, G. (1993). *The Logic of Provability*. Cambridge UP.
  Chs. 1–2 give the soundness-direction proof; ch. 8 gives the
  completeness direction.
- Parent file: `proofs/Proofs/GodelSecondIncompletenessOQ02.lean`.
- Parent gallery axioms: `d1_representability`,
  `con_implies_G`, `provable_modus_ponens`.
