# Knowledge — Solovay Splitting (fodor-pressing-down-oq-04)

## 1. Theorem statement

In the `Proofs/FodorPressingDown.lean` framework:

```lean
theorem solovay_splitting {κ : Cardinal.{0}} (hκ : κ.IsRegular) (hκ_unc : ℵ₀ < κ)
    {S : Set Ordinal} (hS : IsStationaryBelow S κ.ord) :
    ∃ part : Ordinal → Set Ordinal,
      (∀ β < κ.ord, part β ⊆ S) ∧
      (∀ β γ, β < κ.ord → γ < κ.ord → β ≠ γ → part β ∩ part γ = ∅) ∧
      (∀ β < κ.ord, IsStationaryBelow (part β) κ.ord) := by
  sorry
```

Stronger forms exist (e.g. an exhaustive partition `⋃ β < κ.ord, part β = S`); the version above is the minimal Solovay statement and is what the classical proof actually produces.

## 2. Classical proof structure (Jech, *Set Theory*, Theorem 8.10)

The proof has three steps. Each step is independently formalizable, and each except step 2 is a routine application of existing infrastructure.

### Step 1 — Reduce to limit ordinals of cofinality < κ

Let `S₀ = {α ∈ S : α is a limit and ω ≤ cf(α) < κ.ord}`. The set of non-limit ordinals below `κ.ord` is non-stationary (it has no accumulation points), and the set of ordinals of cofinality 0 (the limits of limits ... — i.e. *isolated* zeros) is also non-stationary. So `S₀` is stationary and we may WLOG assume `S = S₀`.

**Existing infrastructure:**
- `IsStationaryBelow.of_subset` handles passing to stationary subsets.
- Need a new lemma: `IsStationaryBelow_iff_intersect_clubs` — already implicit in the definition (line 59 of `FodorPressingDown.lean`).
- Need: non-limit ordinals form a non-stationary set. This is the **first sub-lemma** to prove in S2.

### Step 2 — Construct a regressive auxiliary function

For each `α ∈ S` (with `cf α < α`), fix a strictly-increasing cofinal sequence `c_α : cf α → α`. Define `g_α^ξ = c_α^ξ` for `ξ < cf α`.

Claim: there is some `ξ₀ < κ.ord` such that for stationary-many `α ∈ S`, `cf α ≤ ξ₀`. (Otherwise, the function `α ↦ cf α` would be regressive *and* never bounded by any single ordinal — contradiction via Fodor.)

After truncating to such a stationary `T ⊆ S`, we have `cf α ≤ ξ₀` for all `α ∈ T`. We now have, for each `ξ < ξ₀`, a function `h_ξ : T → κ.ord` defined by `h_ξ(α) = c_α^ξ` (with `h_ξ(α) = 0` if `ξ ≥ cf α`).

**Each `h_ξ` is regressive on `T \ {0}`** (because `c_α^ξ < α`). So **Fodor applies**: for each `ξ < ξ₀`, there exists `β_ξ < κ.ord` and a stationary `T_ξ ⊆ T` with `h_ξ = β_ξ` constantly on `T_ξ`.

**Existing infrastructure:**
- `fodor` (line 259) is the direct workhorse.
- Need: **ordinal cofinality lemmas**. Mathlib has `Ordinal.cof`, and `Ordinal.cof_lt` etc. — these are usable directly in S2.
- Need: existence of a strictly-increasing cofinal sequence from `cf α` to `α`. Mathlib provides `Ordinal.lift_lt_of_cof_lt` and `Ordinal.bsup`; the canonical choice goes via `Ordinal.fundamentalSequence`-like constructions.

### Step 3 — Diagonal across the ξ-sequences

Take the intersection of the `T_ξ` over `ξ < ξ₀`. Since `ξ₀ < κ.ord` and `T_ξ` is stationary for each `ξ`, the intersection is still stationary (κ-stationary implies closure under fewer-than-κ intersections; this uses `diagInter_isClubBelow`).

On this common stationary set `T_*`, each `α` is uniquely characterized by its `ξ₀`-tuple `(β_0, β_1, ..., β_ξ, ...)`. There are at most `|ξ₀|^|κ.ord|` such tuples — but in fact at most `κ` of them, by König's lemma + regularity.

A **counting argument** then partitions `T_*` into κ pieces: each tuple-class gives one piece. Since the tuples are all distinct (as `α` varies, the sequence varies), the κ pieces are pairwise-disjoint. By a final Fodor pigeonhole, infinitely many of them (in fact κ of them) are stationary.

**Existing infrastructure:**
- `diagInter_isClubBelow` (line 240).
- Need: κ-many simultaneous applications of Fodor. This is the **hardest step formally** — the iterated choice introduces Σ-tuples indexed by `ξ < ξ₀`, and `Classical.choose` over a κ-indexed family needs `Classical.skolem` or `Classical.axiomOfChoice`.

## 3. Reusable lemmas from FodorPressingDown.lean

| Lemma | Line | Role in Solovay |
|---|---|---|
| `IsClubBelow` | 53 | Club sets are the test family for stationarity. |
| `IsStationaryBelow` | 59 | The conclusion membership predicate. |
| `IsClubBelow.mem_lt` | 62 | Membership ⇒ below-bound (used in counting). |
| `isClubBelow_Iio_of_isSuccLimit` | 71 | Trivial club exists at limit cardinals; used in default value of `F`. |
| `diagInter_isClubBelow` | 240 | The κ-intersection-of-clubs step (Step 3). |
| `fodor` | 259 | Main hammer (Step 2). |
| `IsStationaryBelow.of_subset` | 343 | Restrict to `S₀`, `T`, `T_ξ`. |
| `IsStationaryBelow.nonempty` | 334 | Sanity check (Solovay output is nonempty). |

## 4. Mathlib API to consult

```
Mathlib.SetTheory.Ordinal.Cofinality
  - Ordinal.cof : Ordinal → Cardinal
  - Ordinal.cof_lt
  - Ordinal.cof_le_card
  - Cardinal.IsRegular.cof_eq

Mathlib.SetTheory.Cardinal.Cofinality
  - Cardinal.IsRegular
  - Cardinal.IsRegular.aleph0_le

Mathlib.SetTheory.Ordinal.Arithmetic
  - Ordinal.IsSuccLimit
  - Ordinal.IsLimit (deprecated alias in some versions)
  - Ordinal.bsup, Ordinal.sup

Mathlib.Logic.Equiv.Defs
  - Classical.skolem (the load-bearing choice principle for Step 2-3 across the ξ-index)
```

**No new axioms required.** Classical choice (already used in `fodor` at line 279) suffices. The proof uses no large-cardinal axioms or extensions beyond ZFC.

## 5. Three candidate S2 deliverables (ranked by tractability)

### S2-α (Easy, ~40–80 lines) — Successor-ordinals are non-stationary
Prove the auxiliary lemma:

```lean
theorem successor_ordinals_nonStationary {κ : Cardinal.{0}}
    (hκ : κ.IsRegular) (hκ_unc : ℵ₀ < κ) :
    ¬ IsStationaryBelow {α : Ordinal | ∃ β, α = Order.succ β} κ.ord
```

(Equivalently: the set of *limit* ordinals below `κ.ord` is club.) This is **Step 1 of the Solovay proof** as a standalone result and unlocks downstream reductions. Build verification straightforward; no Fodor needed.

### S2-β (Medium, ~120–250 lines) — Splitting into 2 stationary sets
Prove the **binary** Solovay statement: any stationary `S` can be split into two disjoint stationary subsets.

This is strictly weaker than the full κ-partition but uses the *same* Fodor pigeonhole technique on a single regressive auxiliary function (e.g. `α ↦ first element of c_α` for a fixed cofinal-sequence assignment). Captures the proof idea without the κ-tuple bookkeeping of Step 3.

### S2-γ (Hard, ~400+ lines) — Full Solovay
The full theorem statement above. Requires Step 1 (S2-α), Step 2 (cofinality + Fodor), and Step 3 (iterated choice + counting). Should be **decomposed into companion theorems** rather than attempted as a single proof.

**Recommended S2 start: S2-α.** It is genuinely reusable (the lemma will be referenced again by S2-γ Step 1 and by any future club-guessing or ◇-construction work), and it produces a build-verified deliverable with no external dependencies on Mathlib's cofinality API beyond `IsSuccLimit`.

## 6. Risks and watch-outs

- **Cofinality API drift.** Mathlib has been actively refactoring `Cardinal.IsRegular` and `Ordinal.cof` definitions; check `Mathlib.SetTheory.Ordinal.Cofinality` for the current API before starting S2-γ.
- **Universe polymorphism.** The current file pins `κ : Cardinal.{0}` (line 240). Solovay splitting in full generality is universe-polymorphic; for the gallery proof, sticking with `.{0}` is the right call (matches the rest of the file).
- **Classical choice vs Skolem.** Step 3 requires κ-indexed choice. The existing `fodor` proof uses `Classical.choose` on a single witness; iterating it across `ξ < ξ₀` is what gets messy. Mathlib's `Classical.skolem` should suffice but the type-checker may need explicit unfolding.

## 7. References

- Fodor, G. (1956), "Eine Bemerkung zur Theorie der regressiven Funktionen", *Acta Sci. Math.* (the original Fodor paper).
- Solovay, R. M. (1971), "Real-valued measurable cardinals", *Axiomatic Set Theory* I (the first appearance of the splitting theorem in the form stated above).
- Jech, T., *Set Theory* (3rd ed.), Theorem 8.10 — the textbook reference for the proof sketched in §2.
- Kunen, K., *Set Theory: An Introduction to Independence Proofs* — alternative presentation of Solovay splitting via stationary tower forcing.

## 8. S12 update (2026-07-24): binary splitting PROVED at ω₁

S2-β is complete. `stationary_splits_binary_aleph1` (Part XI) proves every
stationary subset of ω₁ splits into two disjoint stationary subsets — 0
sorries, 0 axioms. The production step was the **unbounded-index
pigeonhole** on fundamental ω-sequences (`omegaSeq`, new
`Ordinal.exists_isFundamentalSeq` API) + two Fodor applications; the
index-of-first-disagreement / `fodor_anti_constant` / `cofSecond` design
is obsolete. See `sessions/2026-07-24-s12-act-binary-split-aleph1.md`.
Remaining: κ-piece partition (§2 Step 3 bookkeeping) and the general-κ
non-ω-cofinal case (Jech trace analysis; vacuous at ω₁).
