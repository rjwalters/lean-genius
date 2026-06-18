# Knowledge Base: kaprekar-constant-oq-01

Kaprekar's constant 6174: the global attractor of the digit-sort subtraction map
`T` on four-digit decimal strings (not all digits equal), reached in ≤7 steps.

---

## Problem Understanding

- Domain: four-digit strings `0000`–`9999` (i.e. `n < 10000`), excluding repdigits
  (`0000, 1111, …, 9999`), whose orbit collapses to `0`.
- `T(n) = D(n) − A(n)` where `D`/`A` reassemble the digits in descending/ascending
  order. The claim is a finite, fully decidable dynamical-systems fact.
- Because `6174` is a fixed point, "reaches `6174` within 7 steps" is *exactly*
  `T^[7](n) = 6174`. So the bounded-convergence claim is a single clean equation.

---

## Insights

- **Arithmetic-only `T` (no `Nat.digits` / `mergeSort`).** Digits are extracted with
  `/` and `%`; the four digits are sorted ascending by an explicit **5-comparator
  sorting network** (`min`/`max` only). This keeps `T` cheap to reduce, avoiding the
  kernel cost of `Nat.digits` and list `mergeSort`. The recombination is
  `D − A = (z·1000+y·100+x·10+w) − (w·1000+x·100+y·10+z)` for ascending `w≤x≤y≤z`.
- **Sorting network verified.** The 5-comparator network
  `(a,b)(c,d)(a,c)(b,d)(b,c)` reproduces `sorted` on all 10000 inputs (Python check).
- **All claims checked exhaustively in Python before writing Lean:**
  - `T(6174) = 6174`.
  - `6174` is the **unique** non-repdigit fixed point in `[0,10000)`.
  - `T^[7](n) = 6174` for **every** non-repdigit `n < 10000` (0 exceptions).
  - **Bound is sharp:** `max steps = 7` (some inputs need the full seven), so
    `T^[6]` does not always reach `6174`.

## Lean Formalization (this session)

File: `proofs/Proofs/KaprekarConstantOQ01.lean` (≈106 lines, **orphan / unregistered**
— intentionally NOT added to `Proofs.lean` so an unverified file cannot break the
gallery build under the Docker blackout).

Statements:
- `kaprekar_fixed : kaprekarStep 6174 = 6174` — by `decide` (kernel-checked).
- `kaprekar_converges : n < 10000 → NonRepdigit n → kaprekarStep^[7] n = 6174`.
- `kaprekar_unique_fixed : n < 10000 → NonRepdigit n → kaprekarStep n = n → n = 6174`.
- `kaprekar_bound_sharp : ∃ n < 10000, NonRepdigit n ∧ kaprekarStep^[6] n ≠ 6174`.

## Session 2 (2026-06-18, researcher-1): shrink the trusted surface

Goal was axiom elimination; Docker was again in full blackout (`docker info` times
out, `rc=124`, load ≈21), so nothing could be machine-verified. Made the two
**high-confidence, build-independent** reductions that cut `native_decide` from three
enumerations to one, leaving `Lean.ofReduceBool` as the file's *sole* non-foundational
axiom:

- **`kaprekar_unique_fixed` is now structural** — no enumeration. A fixed point `n`
  satisfies `kaprekarStep^[7] n = n` by `Function.iterate_fixed` (verified at pin:
  `Mathlib/Logic/Function/Iterate.lean:90`, `iterate_fixed (h : f x = x) (n) : f^[n] x = x`),
  and `kaprekarStep^[7] n = 6174` by `kaprekar_converges`, so `n = 6174`. Proof term:
  `(Function.iterate_fixed hf 7).symm.trans (kaprekar_converges n h hn)`.
- **`kaprekar_bound_sharp` is now a single witness** — `0014`. Python: `14` is the
  *smallest* non-repdigit needing all seven steps (`T^[6] 14 = 4176 ≠ 6174`).
  Proof term: `⟨14, Finset.mem_range.mpr (by omega), by decide, by decide⟩`.

Only `kaprekar_converges_all` (over `Finset.range 10000`) still uses `native_decide`.
Gallery status remains **axiomatized / axiom** (axiomCount 1, `Lean.ofReduceBool`).
PR: `research/kaprekar-oq01-structural-uniqueness` (build-pending).

### Verified design for the 0-axiom (`verified`) version

The remaining `native_decide` is the *only* obstacle to a `verified`/0-axiom entry.
Plain kernel `decide` over `Finset.range 10000 × 7` iterations is the risk the prior
session flagged. The principled fix — **the digit-multiset reduction** — was fully
checked in Python this session (every claim below returned `True` over all 10000
inputs):

- `kaprekarStep` depends only on the *sorted* digits: **`kaprekarStep n = kaprekarStep (canon n)`**
  where `canon n := w·1000+x·100+y·10+z` for `(w,x,y,z) = sortAsc4 (digits n)`.
- There are exactly **715** canonical (sorted-digit) representatives among `0..9999`
  (= multisets of size 4 over 10 symbols, `C(13,4)`).
- `NonRepdigit n ↔ NonRepdigit (canon n)`; convergence over the 715 reps in 7 steps
  holds; some rep needs 7 (sharp).

**Lean plan** (each lemma needs only `omega`, which on the pin handles `min`/`max` and
`/`,`%` by literals — no enumeration in these steps):
1. `sortAsc4_sorted (a b c d) : let (w,x,y,z) := sortAsc4 a b c d; w≤x ∧ x≤y ∧ y≤z`
   — `unfold sortAsc4; simp only []; omega`.
2. `sortAsc4_lt10` (digits `<10` ⇒ outputs `<10`) — same shape.
3. `sortAsc4_fixed_of_sorted : w≤x→x≤y→y≤z→ sortAsc4 w x y z = (w,x,y,z)` — `omega` per component.
4. `digits_recombine : w,x,y,z<10 → digits (w·1000+x·100+y·10+z) = (w,x,y,z)` — `omega` (div/mod by literals).
5. `kaprekarStep_canon : kaprekarStep n = kaprekarStep (canon n)` — combine 1–4
   (both sides are `recombine (sortAsc4 (digits ·))`; canon's digits re-sort to themselves).
6. `iterate_canon : kaprekarStep^[7] n = kaprekarStep^[7] (canon n)` — peel one step with
   `Function.iterate_succ_apply` (pin line 64), rewrite by lemma 5, re-roll with same.
7. `conv_reps : ∀ w<10, ∀ x<10, ∀ y<10, ∀ z<10, w≤x→x≤y→y≤z→ ¬(w=x∧x=y∧y=z) →
   kaprekarStep^[7] (w·1000+x·100+y·10+z) = 6174 := by decide`
   — uses the efficient `Nat.decidableBallLT` instance; only the ~715 ordered tuples do
   the heavy `^[7]` reduction, the other ~9285 short-circuit on the order hypotheses.
   **This single `decide` is the only feasibility unknown** — must be confirmed by build.
8. `kaprekar_converges` for general `n`: `iterate_canon` + show `canon n` matches a tuple
   from `conv_reps` (its digits are sorted & `<10`).

If step 7's `decide` times out, fall back: keep `native_decide` for convergence only
(current state) — uniqueness/sharpness stay axiom-free regardless.

---

## Dead Ends / Risks

- **Step-7 `decide` feasibility is unverified** (Docker blackout). 715 heavy reductions
  is ~14× lighter than the 10000-case `Finset.range` form, and all Nat ops are
  GMP-accelerated in the kernel, so it is *plausible* but not confirmed. A build settles it.
- The min/max sorting-network lemmas (1–4) rely on `omega` understanding `min`/`max`
  and `/`,`%`-by-literal. Both are supported on the current pin but untested here.

---

## Build Status

**BUILD-PENDING.** This session ran under a full tooling blackout:
- Docker daemon down (`docker version` shows no Server; sibling builds hung at the
  config banner for ~30 min; no containers running).
- Aristotle MCP returns `Resource not found` (404).

The Lean file is complete and Python-cross-checked but **not yet machine-verified**.
Next Docker session: `./proofs/scripts/docker-build.sh Proofs.KaprekarConstantOQ01`,
grep for `error:`, then (if green) register in `Proofs.lean`, add `src/data/proofs`
gallery integration with `status: axiomatized` / `axiomCount` reflecting
`Lean.ofReduceBool`, and flip pool status to `completed`.

---

## Next Steps

1. Docker build-verify `Proofs.KaprekarConstantOQ01` when the daemon returns.
2. If green: register + gallery integration (status `axiomatized`, badge `axiom`).
3. Optional follow-up: 0-axiom version via digit-multiset representatives + a
   `T`-factors-through-multiset lemma (the `decide`-feasible 715-case route).
4. Optional generalization: characterise Kaprekar cycles for ≥5 digits (no single
   fixed point; e.g. 5 digits has cycles, not a constant).

---

## Session 3 (2026-06-18, researcher-1) — 0-axiom companion drafted (BUILD-PENDING)

Implemented the multiset-canonicalisation route from the Lean plan above as a standalone
companion `proofs/Proofs/KaprekarConstantOQ01ZeroAxiom.lean`. Key simplification over the
original sketch: the convergence enumeration does **not** need to be restated over
`(w,x,y,z)` tuples. State it over `n` with a canonicality guard:

```
conv_canon : ∀ n < 10000, canon n = n → NonRepdigit n → kaprekarStep^[7] n = 6174 := by decide
```

The decidable guard `canon n = n` short-circuits the ~9285 non-sorted strings before the
heavy `^[7]` reduction, so the kernel only runs the 715 seven-step reductions. General
convergence follows from three idempotence/preservation facts (`canon_lt`, `canon_idem`,
`nonRepdigit_canon`, all `omega`) plus `iterate7_canon` (one-step peel via
`Function.iterate_succ_apply` ×2 + `kaprekarStep_canon`). Uniqueness/sharpness reuse the
structural argument from the verified file.

**STILL UNVERIFIED** — written under Docker/Aristotle blackout (daemon down, load ~20). A
detached gated build was launched (sentinel `/tmp/r1-kaprekar-zeroaxiom.done`). Open risks,
in order of likelihood to fail:
1. `conv_canon`'s kernel `decide` may time out on 715×7 reductions (the central gamble;
   fall back to `native_decide` there if so — keeps everything else axiom-free).
2. `kaprekarStep_canon` / `canon_idem` `omega` goals are large (8 nested `min`/`max` +
   div/mod-by-literal); relies on `omega` zeta-reducing `let` and modelling `min`/`max`.

Do NOT swap this in for the verified `native_decide` file or claim 0-axiom/verified status
until `./proofs/scripts/docker-build.sh Proofs.KaprekarConstantOQ01ZeroAxiom` is green and
`#print axioms KaprekarConstantOQ01ZeroAxiom.kaprekar_converges` shows no `Lean.ofReduceBool`.
