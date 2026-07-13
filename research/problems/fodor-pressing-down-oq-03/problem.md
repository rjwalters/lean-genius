# fodor-pressing-down-oq-03 — Reflection Principles and □_κ

## Question

> **(Gallery open question 3 of `fodor-pressing-down`.)** Does the
> formalization extend to the more general **Shelah-style reflection
> principles** (e.g., **□_κ sequences**, which use the *non-club*
> structure)?

The parent entry `fodor-pressing-down` proves Fodor's pressing-down lemma
in a self-contained club/stationary framework, now factored into the
reusable module `Proofs/Club/Basic.lean` (`Ordinal.IsClubBelow`,
`Ordinal.IsStationaryBelow`, `Ordinal.diagInter`, `Ordinal.IsRegressive`).
This OQ asks whether that same substrate can carry the next layer of
combinatorial set theory: **stationary reflection** and the **square
principle □_κ** that obstructs it.

## What "reflection" and "□_κ" mean here

- **Stationary reflection.** A stationary `S ⊆ κ` *reflects at* `α < κ`
  (with `α` a limit of uncountable cofinality) when `S ∩ α` is stationary
  *in* `α`. The reflection principle `Refl(κ)` asserts every stationary
  `S` reflects at some such `α`.

- **□_κ (Jensen's square).** A sequence `⟨C_α : α < κ⁺, α limit⟩` with
  (i) `C_α` club in `α`, (ii) `otp(C_α) ≤ κ`, (iii) *coherence*: if
  `β` is a limit point of `C_α` then `C_β = C_α ∩ β`. From `□_κ` one
  builds a **non-reflecting stationary subset** of `κ⁺`. The square
  sequence is exactly the "non-club structure" the OQ names: a coherent
  family of clubs whose *purpose* is to **defeat** reflection.

So the OQ has two genuinely different halves:

1. **Reflection (positive side).** Formalize the notion of reflection on
   top of `IsStationaryBelow`, and the ZFC-provable *base case*
   (**clubs reflect**).
2. **□_κ (obstruction side).** Formalize a coherent square sequence and
   the non-reflecting stationary set it yields — the genuine frontier.

## Why it matters

1. **Reflection is the organizing theme of modern stationary-set
   combinatorics.** Fodor's lemma is the entry point; reflection vs. its
   failure (via □) is the next structural dichotomy (Jech ch. 8, 23;
   Cummings' *Handbook* chapter on square).
2. **The two halves have opposite logical strength.** Club reflection is
   an outright ZFC theorem; *full* stationary reflection is independent
   of ZFC (needs large cardinals) and is *refuted* by □. A formalization
   must make this asymmetry explicit — over-claiming a positive
   reflection theorem in ZFC would be false.
3. **Mathlib gap.** `Mathlib.SetTheory.Ordinal.Topology` supplies
   `IsAcc` / `IsClosedBelow`; `Cardinal.Cofinality` supplies `Ordinal.cof`.
   Neither Mathlib nor the gallery has *any* stationary-reflection or
   square-sequence API. `Proofs/Club/Basic.lean` is the only Lean-4
   stationarity substrate in the project.

## Scope of this S1 OBSERVE deliverable

Documentation and feasibility only — **no Lean build** (the working
environment this cycle has **no Mathlib `.olean` cache** and disk at 99%,
so nothing compiles; see `state.md`). Specifically:

1. Fix precise definitions of *reflection* and *□_κ* in the file's
   `IsClubBelow`/`IsStationaryBelow` framework (`knowledge.md §2`).
2. Separate the **ZFC-provable** fragment (club reflection, trace of a
   club) from the **independent / obstruction** fragment (full
   reflection, □-driven non-reflection) — with truth values stated
   carefully (`knowledge.md §3`).
3. Inventory which existing `Club/Basic.lean` lemmas are reusable
   directly (`knowledge.md §4`).
4. Locate the Mathlib / gallery API gaps that block the □_κ half
   (`knowledge.md §5`).
5. Propose a graded S2/S3 plan with a **tractable, ZFC-true, ~40–70 LOC
   first deliverable** (club reflection + trace), and mark the □_κ half
   as a multi-file research frontier (`knowledge.md §6`).

## Anchoring file references

- `proofs/Proofs/Club/Basic.lean:44–65` — `IsUnboundedBelow`,
  `IsClubBelow`, `IsStationaryBelow`, `diagInter`, `IsRegressive`.
- `proofs/Proofs/Club/Basic.lean:73–76` — `IsClubBelow.mem_of_isAcc`
  (club is closed under its own accumulation points — the seed of club
  reflection).
- `proofs/Proofs/Club/Basic.lean:95–106` — `isClubBelow_Iio_of_isSuccLimit`
  (`Iio o` is a club below a limit `o`).
- `proofs/Proofs/Club/Basic.lean:196–231` — `IsStationaryBelow.nonempty`,
  `.of_subset`, `.mono` (the reflection layer's monotonicity toolkit).
- `proofs/Proofs/FodorPressingDown.lean:199` — `fodor` (pressing-down; the
  reflection layer's eventual client).
- Mathlib `Mathlib.SetTheory.Ordinal.Topology` — `Ordinal.IsAcc`,
  `Ordinal.IsClosedBelow`, `isAcc_iff`, `isClosedBelow_iff`.
- Mathlib `Mathlib.SetTheory.Cardinal.Cofinality` — `Ordinal.cof`,
  cofinality API for the reflection-point predicate `cf(α) > ω`.
