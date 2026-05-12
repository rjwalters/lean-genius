# Knowledge: Club / Stationary Library Refactor

## 1. Inventory of the current local API (FodorPressingDown.lean)

Source: `proofs/Proofs/FodorPressingDown.lean` (385 lines, 0 sorries, 12
theorems, 3 definitions per `meta.json`). The file's docstring lists
the local infrastructure as "not in Mathlib as of 2026-04."

### 1.1 Definitions in scope (Part I § of the local file)

| Local name              | Lines    | Signature                                                                               |
|-------------------------|----------|-----------------------------------------------------------------------------------------|
| `IsUnboundedBelow`      | 51–52    | `(S : Set Ordinal) (o : Ordinal) : Prop`                                                |
| `IsClubBelow`           | 53–56    | `structure ... where subset_Iio ; closed ; unbounded`                                   |
| `IsStationaryBelow`     | 59–60    | `(S : Set Ordinal) (o : Ordinal) : Prop`                                                |
| `diagInter`             | 87–89    | `(f : Ordinal → Set Ordinal) (o : Ordinal) : Set Ordinal`                               |
| (inline) regressiveness | 254–266  | currently expressed inside `fodor`'s hypothesis `∀ α ∈ S, f α < α ∧ f α < κ.ord`        |

### 1.2 Theorems in scope (Part I § of the local file)

| Local name                    | Lines     | Role                                                              |
|-------------------------------|-----------|-------------------------------------------------------------------|
| `IsClubBelow.mem_lt`          | 62–64     | club member ⇒ < o                                                 |
| `IsClubBelow.mem_of_isAcc`    | 66–68     | club + accumulation point ⇒ in club                               |
| `isClubBelow_Iio_of_isSuccLimit` | 71–84  | `Iio o` is a club when `o` is a limit                             |
| `mem_diagInter`               | 91–93     | unfolding lemma                                                   |
| `diagInter_subset_Iio`        | 94–96     | `diagInter f o ⊆ Iio o`                                           |
| `diagInter_isClosedBelow`     | 108–135   | closed part of `diagInter`-is-club                                |
| `diagInter_isUnboundedBelow`  | 138–238   | unbounded part via zipper construction (~100 lines, the hard core)|
| `diagInter_isClubBelow`       | 240–247   | combined closed + unbounded ⇒ club                                |
| `fodor`                       | 254–~330  | the main lemma (downstream of all the above)                      |

### 1.3 What stays in `FodorPressingDown.lean` after refactor

- Module docstring (lines 1–30).
- Import line list (lines 31–37).
- `diagInter_isUnboundedBelow`'s **proof body** (lines 138–238) — this
  is Fodor-specific because it consumes `κ.IsRegular`. Decision
  deferred to S3 ACT (could move with a parameterized cofinality
  hypothesis).
- `fodor` itself (theorem + proof, lines 254 onward).
- *Maybe* `IsRegressive` (if S2 ACT puts it in the new module, the
  parent loses the inline hypothesis form).

Estimated **post-refactor** parent file size: **~180–200 lines**
(roughly halved).

### 1.4 What moves to the new module

- All five definitions (`IsUnboundedBelow`, `IsClubBelow`,
  `IsStationaryBelow`, `diagInter`, `IsRegressive`).
- Five trivial / mechanical theorems (`IsClubBelow.mem_lt`,
  `IsClubBelow.mem_of_isAcc`, `isClubBelow_Iio_of_isSuccLimit`,
  `mem_diagInter`, `diagInter_subset_Iio`).
- The closed-part of diagInter (`diagInter_isClosedBelow`, ~28
  lines), which is cofinality-free.
- The combined `diagInter_isClubBelow` ⇐ if the unbounded part moves
  too; ⇒ otherwise this is a one-line glue lemma stated in the parent.

## 2. Mathlib alignment survey

### 2.1 What's already in Mathlib (relevant)

| Mathlib name                                    | Used by local file?         | Role                                                  |
|-------------------------------------------------|-----------------------------|-------------------------------------------------------|
| `Ordinal.IsAcc S α`                             | YES, via `IsClubBelow.mem_of_isAcc` | accumulation point of S at α                  |
| `Mathlib.SetTheory.Ordinal.Topology`            | YES, imported                | provides `IsClosedBelow` and `IsAcc`                 |
| `IsClosedBelow S o`                             | YES, structure field         | closure under accumulation strictly below o          |
| `Cardinal.cof`                                  | YES, in `fodor`              | cofinality of an ordinal                              |
| `Cardinal.IsRegular`                            | YES, in `fodor`              | regularity (cof = card itself)                        |
| `Cardinal.IsRegular.aleph0_le_cof`              | YES                          | `ℵ₀ ≤ κ.ord.cof`                                      |
| `Cardinal.IsRegular.nat_lt`                     | YES (via `ω < κ.ord`)        | ω < κ.ord for regular uncountable κ                   |
| `Set.Unbounded r s`                             | NO                           | general-order unboundedness; **not** the same shape   |
| `Set.IsClosed` (topology)                       | NO                           | order topology, but Ordinals use `IsClosedBelow` here|

**Conclusion.** Mathlib has the **closed** half (`IsClosedBelow` lives
in `Mathlib.SetTheory.Ordinal.Topology`) but does **not** have a club
predicate, a stationary predicate, a diagonal-intersection
construction, or a regressive-function predicate as of v4.26.0.

### 2.2 What needs new code

| New definition / lemma          | Justification                                                                 |
|---------------------------------|-------------------------------------------------------------------------------|
| `Ordinal.IsUnboundedBelow`      | Mathlib's `Set.Unbounded r s` is general-order, not interval-bounded          |
| `Ordinal.IsClubBelow`           | not in Mathlib                                                                 |
| `Ordinal.IsStationaryBelow`     | not in Mathlib                                                                 |
| `Ordinal.diagInter`             | not in Mathlib                                                                 |
| `Ordinal.IsRegressive`          | not in Mathlib (Mathlib has the term for `Ordinal.Regressive` in the
                                    fixedPoints of `f`, but not the predicate form)                                |

### 2.3 Naming convention proposal

**Option A (recommended):** all definitions live in the `Ordinal`
namespace. Concrete names:

```
Ordinal.IsUnboundedBelow
Ordinal.IsClubBelow            -- structure
Ordinal.IsStationaryBelow
Ordinal.diagInter
Ordinal.IsRegressive           -- generalized: takes ord-set S, not just S = κ.ord
```

Rationale: matches `Ordinal.IsAcc` (existing in
`Mathlib.SetTheory.Ordinal.Topology`); avoids `Set` namespace collision
with `Set.Unbounded` (which has a different shape).

**Option B (alt):** definitions live in the `Set` namespace (since they
classify `Set Ordinal`s):

```
Set.IsUnboundedBelow         -- conflicts with possible Set.Unbounded variant
Set.IsClubBelow
...
```

Rationale: matches `Set.Unbounded`. **Rejected** as primary because the
*ordinality* is essential to the semantics, and the `Ordinal` namespace
better signals this.

**Option C (alt):** `Cardinal.IsClubBelow` parameterized by κ. Rejected
because the predicate truly is about ordinals (`o : Ordinal`), not
cardinals; only the regularity hypothesis comes from `Cardinal`.

**Locked decision (S1 OBSERVE):** Option A. The S2 ACT skeleton uses
`Ordinal.IsClubBelow` etc. throughout.

### 2.4 File path proposal

**Option 1 (recommended):** `proofs/Proofs/Club/Basic.lean`.

Pros: nests under `Proofs/Club/` for future siblings (`Proofs/Club/
DiagonalIntersection.lean`, `Proofs/Club/Galvin.lean`, etc.). Cons:
introduces a new directory.

**Option 2:** `proofs/Proofs/OrdinalClub.lean`. Flat. Acceptable but
less extensible.

**Option 3:** `proofs/Proofs/SetTheory/Club.lean`. Matches Mathlib's
`Mathlib/SetTheory/Ordinal/...` hierarchy. Cons: introduces *two* new
directories under `Proofs/`.

**Locked decision (S1 OBSERVE):** Option 1
(`proofs/Proofs/Club/Basic.lean`). One new directory; trivial
`proofs/Proofs.lean` import-line update (alphabetical at
"`import Proofs.Club.Basic`").

### 2.5 Universe polymorphism boundary

The local file pins `κ : Cardinal.{0}` everywhere `IsClubBelow` /
`IsStationaryBelow` interact with regularity. The new module must
match: the definitions are pure `Ordinal` (universe-polymorphic in
principle), but `diagInter_isUnboundedBelow` requires the
`Cardinal.{0}` instance for `κ.IsRegular`'s `cof` machinery.

**Locked decision (S1 OBSERVE):** the new module is
*definitionally* universe-polymorphic where possible (`IsClubBelow S o`
takes `o : Ordinal.{u}` and `S : Set Ordinal.{u}`), but the
combinatorial lemma `diagInter_isClubBelow` and Fodor itself stay at
`Cardinal.{0}` until a downstream consumer (`fodor-pressing-down-oq-04`
or others) requests otherwise. This matches Mathlib's pragmatic
universe-polymorphism pattern.

## 3. Migration plan (S2 → S4)

### S2 ACT — definitional core

Create `proofs/Proofs/Club/Basic.lean` with:

- The five definitions (`IsUnboundedBelow`, `IsClubBelow`,
  `IsStationaryBelow`, `diagInter`, `IsRegressive`).
- Three mechanical lemmas (`IsClubBelow.mem_lt`,
  `IsClubBelow.mem_of_isAcc`, `mem_diagInter`,
  `diagInter_subset_Iio`).
- Stub `isClubBelow_Iio_of_isSuccLimit` (preserves the existing
  proof verbatim).

Build target: ~80 LOC. **No** new Mathlib import beyond what
`FodorPressingDown.lean` already pulls.

Estimated effort: ~30 min focused Lean (mostly copy-rename).

### S3 ACT — combinatorial core

Move `diagInter_isClosedBelow` to the new file (cofinality-free, ~28
lines). Keep `diagInter_isUnboundedBelow` in the parent file *or*
move it depending on review preference (the lemma has a regularity
hypothesis `hκ : ℵ₀ ≤ κ.ord.cof`; moving it requires the new file to
either depend on `Cardinal.Cofinality` or accept a generic
"unboundedness preserved by ω-suprema" hypothesis).

Build target: +28 LOC in new file, –28 LOC in parent.

### S4 ACT — Fodor stays put

Trim `FodorPressingDown.lean`:

- Remove the five definitions and three mechanical lemmas (now in the
  new file).
- Insert `import Proofs.Club.Basic` at the top.
- Refactor the namespace from `FodorPressingDown` opening directly to
  `FodorPressingDown` re-exporting / using `Ordinal.IsClubBelow`
  (qualified). Optional `export Ordinal (IsClubBelow IsStationaryBelow
  diagInter)` if reader feedback prefers unqualified names inside the
  file.
- Update `meta.json` `lineCount` and `theoremCount` for
  `fodor-pressing-down-oq-04` (parent slug) and add a new
  `leanFiles[]` entry pointing at `Proofs/Club/Basic.lean`.

Estimated effort: ~20 min mechanical.

### S5 (optional) — sister-slug consumer

Ship a one-line Lean change to `fodor-pressing-down-oq-04`'s eventual
file (or, if that slug is still in NEW phase, just update its
`problem.md` to reference the new API as the recommended starting
point).

## 4. Risks and mitigations

| Risk                                                  | Mitigation                                                  |
|-------------------------------------------------------|-------------------------------------------------------------|
| Parent build breaks during S2/S3/S4                   | All S(N) shipped as **build-pending** until S4 final commit |
| `IsClubBelow.mem_of_isAcc` import cycle               | New file imports `Mathlib.SetTheory.Ordinal.Topology` directly; no cycle |
| Naming push-back at Mathlib upstream stage            | S1 OBSERVE locks naming; upstream rename is a search-replace |
| `diagInter_isUnboundedBelow` move causes Mathlib import bloat | S3 keeps it in parent; only the *closed* half moves      |
| Sister slug oq-04 starts before S4 lands              | Race-check via `gh pr list --search fodor-pressing-down`; coordinate |

## 5. Sister-slug compatibility (oq-04 Solovay splitting)

Solovay's theorem on stationary set splitting (the goal of oq-04)
needs **identical** infrastructure: `IsClubBelow` /
`IsStationaryBelow` over a regular uncountable κ, plus diagonal
intersections. The eventual oq-04 Lean file's signature:

```lean
theorem Ordinal.solovay_split {κ : Cardinal.{0}} (hκ_reg : κ.IsRegular)
    (hκ_unc : ω < κ.ord) {S : Set Ordinal}
    (hS : Ordinal.IsStationaryBelow S κ.ord) :
    ∃ T₁ T₂ : Set Ordinal,
      Disjoint T₁ T₂ ∧
      Ordinal.IsStationaryBelow T₁ κ.ord ∧
      Ordinal.IsStationaryBelow T₂ κ.ord ∧
      T₁ ∪ T₂ ⊆ S
```

is precisely the language oq-01 establishes. Without oq-01, oq-04
either inlines its own `IsStationaryBelow` (defeating the point) or
depends on the entire `FodorPressingDown.lean` file (defeating
modularity). With oq-01 done, oq-04 starts with one import line.

## 6. Estimated total cost (S1 OBSERVE → S5)

| Phase | Effort      | Cumulative LOC delta |
|-------|-------------|----------------------|
| S1 OBSERVE | doc-only (~700 LOC markdown/JSON) | +0 Lean |
| S2 ACT     | new module skeleton + 5 mechanical lemmas | +80 Lean |
| S3 ACT     | move closed half of diagInter | +28 Lean (parent –28) |
| S4 ACT     | trim parent file, update meta.json | parent –150 net |
| S5 ACT     | sister-slug compatibility note in oq-04 problem.md | +0 Lean (doc-only) |

**Net Lean LOC delta: ≈ +110 in new module, –150 in parent, total
–40.** Sorry count unchanged at 0.

## 7. Out of scope for this OQ

- Upstreaming to Mathlib (separate PR against `leanprover-community/
  mathlib4`).
- Universe polymorphism beyond `Cardinal.{0}` (deferred to a future
  OQ if requested).
- Other stationary-set results (Galvin, Erdős-Tarski) — those are
  separate consumers of the new module.
- Aristotle integration — the lemmas are short and mechanical; no
  Aristotle assistance is needed.
