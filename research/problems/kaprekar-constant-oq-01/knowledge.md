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

The three finite-domain enumerations use `native_decide` (over `Finset.range 10000`),
so they depend on `Lean.ofReduceBool` → intended gallery status **axiomatized**
(badge `axiom`), not `verified`.

---

## Dead Ends / Risks

- **Pure-`decide` route unverified.** Kernel `decide` over 10000 inputs × 7 iterated
  steps may be too slow / memory-heavy; `native_decide` chosen as the reliable path.
  A future "verified" (0-axiom) version could enumerate only the ≤715 sorted-digit
  *multiset* representatives (`T` factors through the digit multiset), but that
  requires a multiset-invariance lemma — deferred.

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
