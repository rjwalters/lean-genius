# Research State: burnside-counting-oq-01

**Phase**: S1 ACT — rotatedIndex_add discharged (axiom → theorem); S1b STATE-SYNC adds S2 ACT bearer-API pin + Docker / disk blocker note
**Owner**: researcher-1 (S1 ACT 2026-05-30; S1b STATE-SYNC 2026-06-03)
**Iteration**: 1 (S1b is a sub-step, not a fresh iteration)
**Last Updated**: 2026-06-03Z
**Branch**: `research/burnside-counting-oq-01-s1-discharge-axiom` (merged) → `research/burnside-counting-oq-01-s1b-state-sync-*` (this SYNC)

## Lean file inventory (post S1, Docker-verified)

```
File:        proofs/Proofs/BurnsideCounting.lean
Lines:       370 (was 255 at S0)
Theorems:    7 (was 6; rotatedIndex_add promoted from axiom to theorem)
Definitions: 7 (unchanged)
Sorries:     0
Axioms:      4 (was 5; fixed_point_sum_binary_4, coloringSetoid,
                 coloringQuotientFintype, binary_necklaces_4 remain)
Build:       ✔ Docker 3058/3058 jobs clean
```

## What's Done (S1)

- **Discharged `rotatedIndex_add` axiom** to a fully-proved theorem.
  The proof comes with three short Nat-modular auxiliaries
  (`mod_eq_sub`, `mod_of_shift`, `mod_of_eq`) and an 8-leaf case
  enumeration over the sign-cases of `(i.val ⋚ r.val)`,
  `(r.val + s.val ⋚ n)`, and (where applicable)
  `(i.val ⋚ r.val + s.val - n)`. Proof outline:
  1. Bounds: `r.val < n`, `s.val < n`, `i.val < n` via `ZMod.val_lt`
     and `Fin.isLt`.
  2. Composition fact: `(r + s).val = (r.val + s.val) % n` via
     `ZMod.val_add`.
  3. Reduce `Fin n` equality to a `Nat` equality on `.val` via
     `Fin.ext` + `show`.
  4. Flatten `r.val % n → r.val`, `s.val % n → s.val`,
     `(r + s).val → (r.val + s.val) % n`, and apply `Nat.mod_mod`.
  5. Case-split on `r.val ≤ i.val` (case A) vs `i.val < r.val`
     (case B), then on `r.val + s.val ⋚ n`, then (in case B with
     wrap) on `i.val ⋚ r.val + s.val - n`.
  6. Each of the 8 leaves normalizes both sides to a common `ℕ`
     value (either `i.val + n - r.val - s.val`,
     `i.val - r.val - s.val`, `i.val - r.val + n - s.val`, or
     `i.val + n - r.val + n - s.val`) using the auxiliaries, then
     closes by `rw`.

The proof is +115 LOC over the original 2-line axiom statement,
including three private auxiliary lemmas. No new imports
(`ZMod.val_lt` and `ZMod.val_add` come from the already-imported
`Mathlib.Data.ZMod.Basic`; `Nat.mod_mod`, `Nat.mod_eq_of_lt`, and
`Nat.add_mod_right` are in core).

## Why a bare `omega` doesn't suffice here

omega has full Nat mod / truncated-subtraction support, but for this
identity it must internally case-split four ways on the `(i, r, s)`
sign region; in practice the Lean 4 / Mathlib `omega` does not lift
the implicit `r.val + s.val = n * q + (r.val + s.val) % n` (with
`q ∈ {0, 1}`) combined with the inner `(i.val + n - r.val) % n`
case-split. Materializing both case splits by hand brings each leaf
to a linear identity that omega *does* close (when invoked via the
three Nat-mod auxiliaries).

## Axiom inventory (after S1)

The remaining 4 axioms in `BurnsideCounting.lean` are *content* axioms,
not modular-arithmetic infrastructure:

1. `fixed_point_sum_binary_4` (Part IV) — the `|Fix(0)| + |Fix(1)| +
   |Fix(2)| + |Fix(3)| = 24` computation. Discharge candidate: route
   through `native_decide` once `IsFixedByRotation` is fully decidable
   in the rotation/coloring API.
2. `coloringSetoid` (Part IV) — the orbit equivalence relation for
   colorings under rotation. Discharge candidate: derive from
   `MulAction.orbitRel` once the `AddAction (ZMod n)` ↔
   `MulAction (Multiplicative (ZMod n))` bridge is built.
3. `coloringQuotientFintype` (Part IV) — `Fintype` instance for the
   coloring quotient. Discharge candidate: standard once `coloringSetoid`
   is concrete.
4. `binary_necklaces_4` (Part IV) — the headline `= 6` necklace count.
   Discharge candidate: combine `burnside_lemma` +
   `fixed_point_sum_binary_4` + `|ZMod 4| = 4`.

S1 discharged the *infrastructure* axiom (the modular-arithmetic
composition law). The remaining 4 are about the abstract group-action
API + the concrete computation, sitting one bridge-build away from full
discharge.

## What's Next (S2+ priority)

1. **S2 (highest priority)**: build the `AddAction → MulAction` bridge for
   `ZMod n` acting on `Coloring n k`, via `Multiplicative (ZMod n)`. This
   would let `coloringSetoid` be derived rather than axiomatized, and
   unblock `binary_necklaces_4` via `burnside_lemma`. The companion file
   `BurnsideCountingOQ03OQ03.lean` already sketches this connection
   chain explicitly.
2. **S3**: discharge `fixed_point_sum_binary_4` via `native_decide`
   (provided `IsFixedByRotation` is decidable, which it is — there is
   an `instance` at line ~218 of `BurnsideCounting.lean`).
3. **S4**: combine S2 + S3 to discharge `binary_necklaces_4` and reach
   the `verified` badge for the entire file.

## Verified Mathlib API (used in S1 proof)

| Lemma | Module | Statement |
|---|---|---|
| `ZMod.val_lt` | `Data.ZMod.Basic:61` | `[NeZero n] → (a : ZMod n).val < n` |
| `ZMod.val_add` | `Data.ZMod.Basic:646` | `[NeZero n] → (a + b).val = (a.val + b.val) % n` |
| `Nat.mod_eq_of_lt` | `Nat.Defs` | `a < n → a % n = a` |
| `Nat.mod_mod` | core | `a % n % n = a % n` |
| `Nat.add_mod_left` | core | `(n + a) % n = a % n` |
| `Fin.isLt` | core | `(i : Fin n).val < n` |
| `Fin.ext` | core | `(a b : Fin n) (h : a.val = b.val) : a = b` |
| `omega` | tactic | closes `Nat`/`Int` linear arithmetic with `%`/bounds |

All names re-verified against `leanprover-community/mathlib4` HEAD before
writing.

## Session Log

- **2026-06-03 (S1b STATE-SYNC, researcher-1)**: doc-only — confirmed
  4-day bearer byte-stability (`BurnsideCounting.lean` SHA1 `5879ade40b5…`,
  only #21148 in its history); pinned Mathlib bearer-API for **S2 ACT**
  (`AddAction.toMulAction`, `MulAction.orbitRel`, `Multiplicative G`
  instances) and sketched ~20-25 LOC bridge to discharge `coloringSetoid`
  + `coloringQuotientFintype` axioms in one PR. Documented session-wide
  Docker / disk-pressure blocker (host disk 5.1 Gi free / 100% capacity;
  below ≥10 Gi pre-flight threshold; same blocker observed on sibling
  slugs `spherical-law-of-sines-oq-03` PR #22209 and `ehrhart-cube-proven-oq-05`
  PR #22210 this session). No Lean / JSON / parent edits. S2 ACT is
  the next concrete deliverable, ready to paste-and-Docker the moment
  disk recovers. See `sessions/2026-06-03-s1b-state-sync-blocker-and-s2-bearer-pin.md` §2-§3.

- **2026-05-30 (S1, researcher-1)**: ACT — discharged `rotatedIndex_add`.
  File 255 → 370 LOC, axioms 5 → 4, theorems 6 → 7. Build verified with
  `./proofs/scripts/docker-build.sh Proofs.BurnsideCounting` →
  3058 / 3058 jobs clean. Companion file `BurnsideCountingOQ03OQ03.lean`
  docstring (line 20) updated to reflect the new "4 inherited axioms"
  reality. meta.json sync: lineCount 255 → 370, axiomCount 5 → 4,
  theoremCount 6 → 7, assumptions text, mainTheorems entry for
  rotatedIndex_add (type "axiom" → "supporting", significance/description
  rewritten), openQuestions list trimmed.
