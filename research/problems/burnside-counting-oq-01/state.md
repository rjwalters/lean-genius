# Research State: burnside-counting-oq-01

**Phase**: **S3 ACT** — `fixed_point_sum_binary_4` discharged (axiom → theorem via `native_decide`)
**Owner**: researcher-1 (S1 ACT 2026-05-30; S1b STATE-SYNC 2026-06-03; S2 ACT 2026-06-09); **researcher-9 (S3 ACT 2026-06-10)**
**Iteration**: 3 (S3 is a fresh iteration after S2)
**Last Updated**: 2026-06-10Z
**Branch**: `research/burnside-counting-oq-01-s3-act-fixed-point-sum`

## Lean file inventory (post S3, Docker-verified)

```
File:        proofs/Proofs/BurnsideCounting.lean
Lines:       394 (was 387 at S2; +7 LOC for docstring on the new theorem)
Theorems:    8 (was 7; fixed_point_sum_binary_4 promoted from axiom to theorem)
Definitions: 9 (unchanged from S2)
Sorries:     0
Axioms:      1 (was 2 at S2; only binary_necklaces_4 remains)
Build:       ✔ Docker 3058/3058 jobs clean
             (3 pre-existing simpArgs linter warnings at 77/299/301; untouched)
```

## What's Done (S3, this iteration)

- **Discharged `fixed_point_sum_binary_4` axiom** to a `native_decide`
  theorem. The pre-existing `DecidablePred (@IsFixedByRotation 4 2 _ r)`
  instance at line 329 + `DecidableEq (Fin 4 → Fin 2)` + `Subtype.fintype`
  + `DecidableEq ℕ` form a complete decidability chain; `native_decide`
  evaluates the chain at kernel time to verify `16 + 2 + 4 + 2 = 24`.
  The proof body is one tactic; the `+7 LOC` is a docstring annotation.

### Why `native_decide` (not `decide`)

`decide` would also typecheck in principle, but enumerating 16 colorings
× 4 rotations through plain `decide` may hit elaboration size limits in
some Lean versions; `native_decide` compiles the decidability proof to
native code and is the standard idiom for this scale of finite check.
Both are sound at the kernel level.

## What's Done (S2)

- **Discharged `coloringSetoid` axiom** as `AddAction.orbitRel (ZMod n) (Coloring n k)`.
- **Discharged `coloringQuotientFintype` axiom** via `Quotient.fintype` +
  a new `coloringSetoid_decidableRel` instance.
- File 370 → 387 LOC, axioms 4 → 2, definitions 7 → 9.

## What's Done (S1)

- **Discharged `rotatedIndex_add` axiom** to a fully-proved theorem (PR #21148).

## Axiom inventory (after S3)

The remaining 1 axiom in `BurnsideCounting.lean`:

1. `binary_necklaces_4` (Part IV) — the headline `= 6` necklace count.
   Discharge candidate: combine `burnside_lemma` (MulAction form) +
   `fixed_point_sum_binary_4` (now a theorem, this PR) + `|ZMod 4| = 4`
   ⟹ `24 / 4 = 6`. Bridge needed:
   `AddAction.orbitRel.Quotient (ZMod 4) (Coloring 4 2)` ↔
   `MulAction.orbitRel.Quotient (Multiplicative (ZMod 4)) (Coloring 4 2)`
   via `Multiplicative`, or apply `to_additive` to `burnside_lemma` to
   produce an `AddAction`-form variant. **Once S4 lands,
   `BurnsideCounting.lean` is axiom-free (0 of 5 original axioms remain).**

### Axioms discharged in earlier iterations

- **S1 (PR #21148)**: `rotatedIndex_add`.
- **S2 (researcher-1, 2026-06-09)**: `coloringSetoid`, `coloringQuotientFintype`.
- **S3 (this PR, 2026-06-10)**: `fixed_point_sum_binary_4`.

## What's Next (S4 priority — recommended for next picker)

1. **S4**: discharge `binary_necklaces_4` via `burnside_lemma` +
   `fixed_point_sum_binary_4` (now a theorem) + `|ZMod 4| = 4`. Bridge
   `AddAction.orbitRel.Quotient` ↔ `MulAction.orbitRel.Quotient` via
   `Multiplicative` (S1b STATE-SYNC plan §2.1), or `to_additive` on
   `burnside_lemma`. Estimated ~30-50 LOC.
2. **Optional cleanup**: the 3 pre-existing `simpArgs` linter warnings
   at lines 77/299/301 (untouched since pre-S2; cosmetic).

## Session Log

- **2026-06-10 (S3 ACT, researcher-9)**: ACT — discharged
  `fixed_point_sum_binary_4` axiom via `native_decide`. File 387 → 394
  LOC (+7 for docstring; proof body is one tactic). Axioms 2 → 1,
  theorems 7 → 8. Decidability chain: `Coloring 4 2 = Fin 4 → Fin 2`
  finite + `DecidableEq`; `IsFixedByRotation r` decidable via existing
  instance at line 329; `Subtype.fintype` for each of the 4 fixed-point
  sets; final `DecidableEq ℕ` on `… = 24`. Build verified
  `./proofs/scripts/docker-build.sh Proofs.BurnsideCounting` →
  3058 / 3058 jobs clean (same 3 pre-existing simpArgs warnings as S2).
  Gallery JSON sync: lineCount 387 → 394, theoremCount 7 → 8 (gallery
  mirror was at 6 pre-S2 sync; bumped to 8), axiomCount 2 → 1,
  iteration 2 → 3, attemptCounts.total 2 → 3,
  attemptCounts.approachesTried 2 → 3, lastUpdate
  2026-06-09T20:50:00Z → 2026-06-10T02:50:00Z, builtItems += new
  fixed_point_sum_binary_4 entry, one new S3 insight.


**Last Updated**: 2026-06-09Z
**Branch**: `research/burnside-counting-oq-01-s1-discharge-axiom` (merged) → `research/burnside-counting-oq-01-s1b-state-sync-*` (merged) → `research/burnside-counting-oq-01-s2-act-orbitrel-bridge-*` (this PR)

## Lean file inventory (post S2, Docker-verified)

```
File:        proofs/Proofs/BurnsideCounting.lean
Lines:       387 (was 370 at S1; +17 LOC for S2 ACT)
Theorems:    7 (unchanged)
Definitions: 9 (was 7; +coloringSetoid def, +coloringQuotientFintype def;
                 coloringSetoid_decidableRel instance also added)
Sorries:     0
Axioms:      2 (was 4 at S1; fixed_point_sum_binary_4 and binary_necklaces_4
                 remain; coloringSetoid and coloringQuotientFintype
                 discharged this PR)
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

## Axiom inventory (after S2)

The remaining 2 axioms in `BurnsideCounting.lean` are both *content*
axioms about the specific binary 4-necklace computation:

1. `fixed_point_sum_binary_4` (Part IV) — the `|Fix(0)| + |Fix(1)| +
   |Fix(2)| + |Fix(3)| = 24` computation. Discharge candidate: route
   through `native_decide` once `IsFixedByRotation` is fully decidable
   in the rotation/coloring API.
2. `binary_necklaces_4` (Part IV) — the headline `= 6` necklace count.
   Discharge candidate: combine `burnside_lemma` +
   `fixed_point_sum_binary_4` + `|ZMod 4| = 4`.

### Axioms discharged in earlier iterations

- **S1 (PR #21148)**: `rotatedIndex_add` — modular-arithmetic
  composition law for rotations. Proved unconditionally via
  `ZMod.val_add` + an 8-leaf case enumeration.
- **S2 (this PR)**: `coloringSetoid` — orbit equivalence relation.
  Derived as `AddAction.orbitRel (ZMod n) (Coloring n k)`. The actual
  bridge is simpler than the S1b STATE-SYNC plan suggested: Mathlib's
  `orbitRel` is `@[to_additive]`, so `AddAction.orbitRel` exists
  directly — no `Multiplicative`-bridge needed.
- **S2 (this PR)**: `coloringQuotientFintype` — `Fintype` instance for
  the coloring quotient. Derived via `Quotient.fintype` from finite
  `Coloring n k = Fin n → Fin k` and a new decidable-orbit-relation
  instance `coloringSetoid_decidableRel` (each orbit membership reduces
  to `∃ x : ZMod n, x +ᵥ b = a`, decidable by
  `Fintype.decidableExistsFintype`).

## What's Next (S3+ priority)

1. **S3**: discharge `fixed_point_sum_binary_4` via `native_decide`
   (provided `IsFixedByRotation` is decidable, which it is — there is
   an `instance` at line ~218 of `BurnsideCounting.lean`).
2. **S4**: combine S3 with `burnside_lemma` to discharge
   `binary_necklaces_4` and reach the `verified` badge for the entire
   file. With `coloringSetoid` now `= AddAction.orbitRel (ZMod n) (Coloring n k)`,
   `Quotient (coloringSetoid n k) = AddAction.orbitRel.Quotient (ZMod n) (Coloring n k)`,
   which is exactly the orbit-quotient type that `burnside_lemma` (in its
   `MulAction` form) would consume after a `Multiplicative`-bridge. For
   S4, the cleanest path is either (a) restate `burnside_lemma` in
   `AddAction` form using `to_additive` lemmas, or (b) build the
   `Multiplicative` bridge for the orbit equivalence specifically.

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

- **2026-06-09 (S2 ACT, researcher-1)**: ACT — discharged `coloringSetoid`
  and `coloringQuotientFintype` axioms. File 370 → 387 LOC (+17),
  axioms 4 → 2, definitions 7 → 9 (+coloringSetoid def, +coloringQuotientFintype def,
  +coloringSetoid_decidableRel instance). Approach: instead of building
  the `Multiplicative (ZMod n)` bridge that the S1b STATE-SYNC pinned,
  observed that Mathlib's `orbitRel` carries `@[to_additive]`, so
  `AddAction.orbitRel (ZMod n) (Coloring n k)` is directly available.
  `coloringSetoid` is now a 2-line `def` aliasing this. For Fintype on
  the quotient, registered a `DecidableRel (coloringSetoid n k).r`
  instance using `decidable_of_iff` + `AddAction.mem_orbit_iff` +
  `Fintype.decidableExistsFintype` (membership in orbit reduces to a
  finite ∃ over `ZMod n`), then `coloringQuotientFintype` is
  `Quotient.fintype` applied with the setoid + decidability in scope
  via `letI`/`haveI`. Build verified with
  `./proofs/scripts/docker-build.sh Proofs.BurnsideCounting` →
  3058 / 3058 jobs clean (3 pre-existing simpArgs warnings in untouched
  code at lines 77, 299, 301). meta.json sync: lineCount 370 → 387,
  axiomCount 4 → 2, definitionCount 7 → 9, assumptions text rewritten,
  3 new originalContributions added, openQuestions trimmed (now lists
  just S3 + S4 + Polya + dihedral generalizations).

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
