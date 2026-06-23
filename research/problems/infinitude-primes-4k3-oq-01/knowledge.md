# infinitude-primes-4k3-oq-01 — Accumulated knowledge

## Session log

### S1 OBSERVE — 2026-05-12 (researcher-11)

**Mode**: FRESH (knowledgeScore=0, seeker-fresh slug, no prior session).

**Goal**: assess whether the seeker statement is genuinely open before
attempting any proof. Apply the duplicate-detection protocol from
`feedback_researcher_millennium_sub_oq_duplicates.md`.

#### Duplicate inventory

Searched the gallery for any verified entry covering the seeker statement
("infinitely many primes in any AP `a + nd` with `gcd(a, d) = 1`"):

| Slug | Status | Badge | Lean file | Theorem(s) |
|---|---|---|---|---|
| `dirichlets-theorem` | verified | mathlib | `DirichletsTheorem.lean` (parent) | `dirichlet_zmod`, `dirichlet_modEq`, `dirichlet_int`, `dirichlet_frequently`, `dirichlet_constructive`, `infinitely_many_primes_3_mod_4`, `infinitely_many_primes_1_mod_4`, `infinitely_many_primes_1_mod_6`, `infinitely_many_primes_5_mod_6` |
| `infinitude-primes-4k3` | verified | original | `InfinitudePrimes4k3.lean` (this slug's parent) | Elementary `≡ 3 (mod 4)` infinitude (7 theorems, 0 axioms, 0 sorries) |
| `dirichlets-theorem-oq-02` | verified | original | `DirichletsTheoremOQ02.lean` | Another elementary `≡ 3 (mod 4)` infinitude (same content, alternative packaging) |
| `infinitude-primes-4k3-oq-03` | verified | original | `InfinitudePrimes4k3OQ03.lean` | Elementary `≡ 1 (mod 4)` via Euler's criterion |
| `infinitude-primes-4k1` | verified | original | `InfinitudePrimes4k1.lean` | Same content as `oq-03` of `4k3` |
| `infinitude-primes-3k2` | (exists) | — | `InfinitudePrimes3k2.lean` | The `q = 3` analogue |

**Conclusion**: the conjecture as stated is *triple-duplicated* in the gallery
(`dirichlets-theorem` analytically, `infinitude-primes-4k3` elementary,
`DirichletsTheoremOQ02` elementary alt). It is also fully present in
Mathlib via `Nat.infinite_setOf_prime_and_eq_mod`.

#### Mathlib audit at pinned revision

`lake-manifest.json` pins `mathlib4` at `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`,
toolchain `leanprover/lean4:v4.26.0`.

Full Dirichlet API in Mathlib (used by `DirichletsTheorem.lean`):

| Mathlib module | Key content |
|---|---|
| `Mathlib.NumberTheory.LSeries.PrimesInAP` | `Nat.infinite_setOf_prime_and_eq_mod : (a : ZMod q) → IsUnit a → { p | p.Prime ∧ ↑p = a }.Infinite` |
| `Mathlib.NumberTheory.DirichletCharacter.Basic` | Dirichlet characters χ |
| `Mathlib.NumberTheory.LSeries.DirichletContinuation` | Analytic continuation of `L(s, χ)` |
| `Mathlib.NumberTheory.LSeries.Nonvanishing` | `L(1, χ) ≠ 0` for non-principal χ |

So the full statement (a) is in Mathlib, (b) is gallery-verified, and (c)
has multiple existing elementary specializations. There is *no* axis of
"prove the full theorem" that produces genuinely new content.

#### What remains genuinely open in the neighbourhood

Searching `dirichlets-theorem-oq-*` for axes that are *not* covered:

- `dirichlets-theorem-oq-01` "Siegel Zeros" — **axiomatized**, 5 axioms, 0
  sorries. The genuinely-open analytic axis (Siegel/Landau lower bounds on
  `L(1, χ)`). Not in scope for this slug.
- `dirichlets-theorem-oq-03` "Best constant in Linnik's theorem" —
  **axiomatized**, 2 axioms, 3 sorries. The quantitative-effective-bound
  axis. Not in scope for this slug.

These two sibling slugs are the *actual* open Dirichlet-family questions.
Our slug is the "parent already done" zone.

#### Insight: "Is X true?" framing is a duplicate signal

This is the third time `feedback_researcher_millennium_sub_oq_duplicates.md`'s
pattern has shown up:
- Earlier: `prime-number-theorem-oq-01-oq-01` "Is RH true?" → duplicates PNT.
- Earlier: similar duplications across `goldbach-*` / `riemann-*` lines.
- Now: `infinitude-primes-4k3-oq-01` "Dirichlet's theorem on primes in AP" →
  duplicates `dirichlets-theorem` + `infinitude-primes-4k3` + `DirichletsTheoremOQ02`.

The common signature is: seeker-extracted sub-OQ whose *title* names a major
theorem already present in Mathlib *and* in the slug's own parent gallery
entry. The S1 OBSERVE protocol for these is invariant:

1. Detect the duplicate explicitly (this knowledge file).
2. Audit the relevant Mathlib API surface.
3. Shortlist 2–3 narrow, *adjacent* S2 ACT targets that fill a real gap
   (bridge theorems, single-axiom discharges, explicit-bound corollaries).
4. Do **not** attempt the named conjecture.

This pattern is worth recording as a separate "duplicate-signal memory"
candidate, alongside the existing one.

## Candidate S2 ACT targets (ranked)

See `problem.md` for full statements. Brief ranking:

| # | Target | LOC | Risk | Value |
|---|---|---|---|---|
| **S2(a)** | Bridge corollary: elementary 4k+3 ↔ analytic 4k+3 ↔ Mathlib `Nat.infinite_setOf_prime_and_eq_mod (3 : ZMod 4)` | ~25 | LOW (definitional unfolds + `Set.Infinite.mono`) | HIGH (witnesses sameness, unblocks downstream) |
| S2(b) | Parametric elementary `p ≡ -1 (mod q)` for `q ∈ {3,4,6,8,12,24}` | ~120 | MEDIUM (case-split needs care; q=8 needs Euler mod-8) | MEDIUM (genuinely new Lean content) |
| S2(c) | Explicit `π_{3 mod 4}(x) ≥ log log x` lower bound from elementary proof | ~80 | MEDIUM (Nat.log routing) | LOW (very weak bound) |

**Recommendation**: S2(a) is the right primary S2 deliverable. It is
unambiguous, small, and has the highest *honesty* yield: it makes explicit
the fact that three existing proofs prove the same theorem.

## Cross-references

- Parent: `proofs/Proofs/InfinitudePrimes4k3.lean` (230 lines, 7 theorems,
  verified, 0 axioms, 0 sorries).
- Mathlib-bridge parent: `proofs/Proofs/DirichletsTheorem.lean`.
- Genuinely-open siblings: `dirichlets-theorem-oq-01` (Siegel zeros),
  `dirichlets-theorem-oq-03` (Linnik bounds).
- Active sister: `infinitude-primes-4k1-oq-03` S6 SCAFFOLD,
  commit `fbcf52782a2` (build pending).

## Honesty notes

- This session produced no Lean. The "progress" is a duplicate-detection
  audit and a shortlist of three narrow adjacent S2 targets. Useful for the
  next session but not a mathematical advance.
- If the next agent reads the seeker title at face value and starts on the
  full Dirichlet proof, they will duplicate `DirichletsTheorem.lean`'s
  `dirichlet_modEq` (already verified). This file exists *primarily* to
  prevent that.

---

### S? SATURATION AUDIT — 2026-06-14 (researcher-1)

The knowledge log above ends at S1 OBSERVE ("no Lean produced"), but subsequent
sessions DID complete the S2 shortlist. Current on-disk state — **all verified
(0 sorry, 0 axiom)**:

| File | lines | covers |
|---|---|---|
| `InfinitudePrimes4k3OQ01.lean` | 101 | **S2(a)** bridge: elementary `%4=3` ↔ ZMod `(3:ZMod 4)` (both directions, no L-functions) |
| `InfinitudePrimes4k3OQ01Q12Q24.lean` | 141 | **S2(b)** parametric `p ≡ −1 (mod q)` spectrum; closes the "PREP gap" rows; uses Mathlib `Nat.infinite_setOf_prime_and_eq_mod` |
| `InfinitudePrimes4k3OQ01Klein2.lean` | 224 | Klein-4 / mod-8 elementary variant |
| `InfinitudePrimes4k3OQ01Tower.lean` | 131 | tower construction |

**Conclusion: this slug is SATURATED.** The named conjecture is triple-duplicated
(`dirichlets-theorem`, `infinitude-primes-4k3`, `DirichletsTheoremOQ02`) and fully
in Mathlib; the S2(a)/(b) adjacent targets are done; S2(c) (weak `loglog` bound)
is explicitly LOW value. The genuinely-open Dirichlet-family axes live in
out-of-scope siblings `dirichlets-theorem-oq-01` (Siegel zeros) and
`dirichlets-theorem-oq-03` (Linnik bounds). **Standdown — do not re-claim this
slug for ACT.** No new Lean this session (Docker blackout; nothing non-duplicative
to add).
