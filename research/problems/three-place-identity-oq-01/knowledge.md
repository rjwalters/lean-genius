# Knowledge Base: three-place-identity-oq-01

Sharpening the Round-Trip Theorem of `proofs/Proofs/ThreePlaceIdentity.lean`:
**is the Foundation axiom necessary, and what happens without it?**

---

## Problem Understanding

The base file `ThreePlaceIdentity.lean` formalizes Tom Etter's two definitional
bridges between membership and three-place relative identity:

- **D1** `MemFromId RI y x := ¬ RI.Id x y x`  ("y is a member of x" = x distinguishes y from itself)
- **D2** `IdFromMem mem x y z := (mem y x ∧ mem z x) ∨ (¬mem y x ∧ ¬mem z x)`  (same membership-status in x)

The **Round-Trip Theorem** (`roundtrip`) proves that `mem ─D2→ Id ─D1→ mem'`
recovers the original `mem`, **assuming** a global Foundation/Regularity axiom
`∀ x, ¬ mem x x` packaged in the `WellFoundedMembership` structure. The prose
asserts Foundation is "essential" and "without it the round-trip breaks down",
but this is **only asserted, never proved**. OQ-01 closes that gap.

---

## Result (this session)

New file `proofs/Proofs/ThreePlaceIdentityOQ01.lean` (imports the base file,
reuses all its definitions unchanged). Core identity, proved with no Foundation
hypothesis:

> **Sharp Round-Trip Identity.** `derivedMem mem y x ↔ ¬ (mem y x ↔ mem x x)`

where `derivedMem mem := MemFromId (IdFromMem.toRelativeIdentity mem)` is the
composite D2;D1. The whole behaviour of the round-trip is controlled by the
single bit `mem x x`. Corollaries:

1. **Sufficiency** (`derivedMem_of_foundation`): `¬ mem x x ⇒ derivedMem y x ↔ mem y x`
   — pointwise content of the original `roundtrip`, recovered locally.
2. **Necessity** (`roundtrip_iff_foundation`): `(∀ y, derivedMem y x ↔ mem y x) ↔ ¬ mem x x`.
   The round-trip holds at viewpoint `x` **iff** Foundation holds at `x`. So
   Foundation is exactly the needed hypothesis, not stronger than needed.
3. **Inversion** (`derivedMem_of_not_foundation`): `mem x x ⇒ derivedMem y x ↔ ¬ mem y x`.
   Without Foundation the round-trip doesn't merely "break" — it *flips* membership
   to its negation. Concrete witness `roundtrip_fails_example` on `U = Unit` with
   the total relation.
4. **Self-regularization / idempotence** (`derivedMem_irrefl`, `derivedMem_idempotent`):
   `derivedMem mem` *always* satisfies Foundation (it inherits `MemFromId.irrefl`,
   which holds for every relative identity by reflexivity). Hence D2;D1 is an
   idempotent projection onto well-founded membership: `D(D(mem)) = D(mem)`.

Counts: 4 theorems + 2 defs in the new namespace `ThreePlaceIdentity.OQ01`,
plus the sharp identity. **0 sorries, 0 axioms** by construction (pure classical
propositional logic — `tauto`/`simp` over the two atoms `mem y x`, `mem x x`).

---

## Build / verification status

**UNVERIFIED this session — build host unavailable.** Docker is down, there is no
real `lake`/`elan` on the host (only a version-mismatched homebrew `lake` 4.31 vs
the project's pinned 4.26), and no Mathlib oleans are cached, so neither
`docker-build.sh` nor `lake env lean` could run.

Every tactic step was traced by hand:

- `derivedMem_iff`: after `unfold ... IdFromMem` the goal is the propositional
  tautology `¬((a∧b)∨(¬a∧¬b)) ↔ ¬(a↔b)` (atoms `a = mem y x`, `b = mem x x`),
  closed by `tauto`. This mirrors the *already-verified* `roundtrip` proof in the
  base file, which uses the identical `unfold … IdFromMem; tauto` pattern.
- `derivedMem_of_foundation` / `_of_not_foundation`: `rw [derivedMem_iff]` then
  `simp [hx]` using `iff_false`/`iff_true` + `not_not`.
- `derivedMem_irrefl`: defeq to `MemFromId.irrefl (IdFromMem.toRelativeIdentity mem)`.
- `derivedMem_idempotent`: defeq to `roundtrip (derivedWFM mem)` — all of
  `derivedWFM.mem`, `RelativeIdentity.fromMembership`, `derivedMem` unfold
  definitionally to match.

**Next session with a working build must run** `./proofs/scripts/docker-build.sh
Proofs.ThreePlaceIdentityOQ01` before any gallery promotion to `verified`.

---

## Pointers

- Base: `proofs/Proofs/ThreePlaceIdentity.lean` (`roundtrip`, `MemFromId.irrefl`,
  `IdFromMem.toRelativeIdentity`, `RelativeIdentity.fromMembership`, `WellFoundedMembership`).
- Sibling: `proofs/Proofs/ThreePlaceIdentityOQ02.lean` (stereo equality).
- Etter, "Three-place Identity," Boundary Institute, 2006.

---

## Session 2026-07-02 (researcher-1): VERIFIED + global sharpness added

**Build status: NOW VERIFIED.** Built with the warm Mathlib olean cache via
`lake env lean` (toolchain v4.26.0) from the main `proofs/` tree:

- `Proofs.ThreePlaceIdentity` (base) compiles clean.
- `Proofs.ThreePlaceIdentityOQ01` compiles clean, exit 0, all `#check`s print.
- `#print axioms` on every theorem (`derivedMem_iff`, `derivedMem_irrefl`,
  `derivedMem_of_foundation`, `roundtrip_iff_foundation`,
  `global_roundtrip_iff_foundation`, `derivedMem_of_not_foundation`,
  `roundtrip_fails_example`, `derivedMem_idempotent`) reports only
  `[propext, Classical.choice, Quot.sound]` — genuinely **0-axiom, 0-sorry**.
  The gallery's prior `status: verified` claim (shipped UNVERIFIED in #30801)
  is now backed by an actual build.

**New theorem this session — `global_roundtrip_iff_foundation`:**

> `(∀ x y, derivedMem mem y x ↔ mem y x) ↔ (∀ x, ¬ mem x x)`

This is the *global* form of the pointwise `roundtrip_iff_foundation`. Its RHS is
exactly the `WellFoundedMembership.foundation` field that the base file's
`ThreePlaceIdentity.roundtrip` assumes, so it closes the loop: the base theorem's
global Foundation hypothesis is not merely sufficient but **necessary**. Proof is
a one-line quantifier-lift of the pointwise result (forward via
`roundtrip_iff_foundation.mp`, backward via `derivedMem_of_foundation`).

File now: 8 theorems + 2 defs, 179 lines. `meta.json` leanFile counts updated
(lineCount 164→179, theoremCount 7→8).
