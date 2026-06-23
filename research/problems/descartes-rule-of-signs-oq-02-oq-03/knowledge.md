# Knowledge Base: descartes-rule-of-signs-oq-02-oq-03

Seeker task: **"Close the `budan_parity` axiom via Mathlib's FTA."**

---

## Problem Understanding

`proofs/Proofs/DescartesRuleOfSignsOQ02.lean` formalizes **Budan's theorem** with a 3-axiom
budget (`budan_upper_bound`, `budan_parity`, `budanCount_large`). The target axiom
(`DescartesRuleOfSignsOQ02.lean:244`):

```
axiom budan_parity_axiom (p : ℝ[X]) (hp : p ≠ 0) (a b : ℝ) (hab : a < b) :
    Even (budanCount p a - budanCount p b - rootsInInterval p a b)   -- ℕ-subtraction
```

where (file defs):
- `budanCount p x := signChangesInList (budanSequence p p.natDegree x)` — sign changes (zeros
  dropped) in the derivative-evaluation sequence `[p(x), p'(x), …, p⁽ⁿ⁾(x)]` (`:181`).
- `rootsInInterval p a b` — `#{real roots in (a,b]}` with multiplicity (`:203`).
The truncated subtraction is well-defined because `budan_upper_bound` gives
`rootsInInterval ≤ budanCount a − budanCount b`.

---

## Session 2026-06-15 (S1, researcher-2) — ORIENT: correct route pinned, seeker framing refined

**Mode:** FRESH (knowledge score 0). **Both backends down** (Docker `docker info` times out;
Aristotle MCP `prove` → `"Resource not found"` on a trivial ping). Build-free: numerical
verify-before-assert + Mathlib bearer audit at the repo pin (`lean-toolchain` v4.26.0,
mathlib rev `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`).

### The big finding: Mathlib HAS Descartes' rule — but only the BOUND, not the parity

`Mathlib/Algebra/Polynomial/RuleOfSigns.lean` exists at the pin and proves
**`Polynomial.roots_countP_pos_le_signVariations`** (`:382`): `P.roots.countP (0 < ·) ≤
signVariations P` — the Descartes **upper bound**, with `signVariations P :=
(nonzero_signs.destutter (· ≠ ·)).length - 1` (`:50`). A grep of that file for
`even`/`odd`/`parity` returns **nothing** — Mathlib does **not** prove the parity refinement.
This exactly mirrors the in-file split: Mathlib's `roots_countP_pos_le_signVariations` ↔ this
file's `budan_upper_bound`; the parity half is unformalized **both** upstream and here. So
`budan_parity` is a genuine gap, not duplicable from Mathlib.

### The seeker's "via FTA / complex conjugate pairs" is the GLOBAL intuition; the local interval
### parity has a cleaner, formalizable route (numerically certified, 288/288 — `verify_budan_parity.py`)

The "non-real roots come in conjugate pairs" picture is the standard hand-wave for the *global*
Descartes count. The *local* `(a,b]` parity decomposes more cleanly:

- **(A) Mathlib bridge.** `budanCount p x = signVariations (taylor x p)`. The Taylor coefficients
  of `p(X+x)` are `p⁽ᵏ⁾(x)/k!` — same **signs** as `p⁽ᵏ⁾(x)`, so the two sign-change counts
  coincide. (`Polynomial.taylor` ∈ `Mathlib/Algebra/Polynomial/Taylor.lean`.) This is optional —
  one may instead reprove parity directly on the in-file `signChangesInList` (see P1 below),
  avoiding the bridge entirely.
- **(B) Parity-of-sign-variations is an ENDPOINT fact.** `signVariations` is `destutter`-length−1;
  a destuttered ±1 list `[s₀,…,s_m]` is strictly alternating, so `s_m = s₀·(−1)^m`, hence
  `parity(length−1) = parity(m) = [s₀ ≠ s_m]` = (first nonzero sign ≠ last nonzero sign). For the
  derivative sequence: first entry `= p(x)`; last entry `= p⁽ⁿ⁾(x) = n!·leadingCoeff p` (degree
  `n`), which is **sign-constant in x**. Therefore
  **`parity(budanCount p x) = [sign(p(x)) ≠ sign(leadingCoeff p)]`** (when `p(x) ≠ 0`).
- **(C)** Cancelling the common `sign(leadingCoeff p)`:
  **`parity(budanCount p a) ⊕ parity(budanCount p b) = [sign p(a) ≠ sign p(b)]`**.
- **(D) The genuine FTA content.** `[sign p(a) ≠ sign p(b)] ⟺ Odd(rootsInInterval p a b)`. Via
  the real factorization `p = leadingCoeff · ∏_{real rᵢ}(X−rᵢ) · ∏(positive-definite quadratics)`:
  `sign p(a)·sign p(b) = ∏_{real r} sign((a−r)(b−r)) = (−1)^{#real roots in (a,b) w/ mult}`
  (complex pairs are positive on ℝ; even multiplicities don't flip parity). With `p(a),p(b) ≠ 0`
  the half-open `(a,b]` count has the same parity as `(a,b)`.

(A)+(B)+(C)+(D) ⇒ `budanCount p a − budanCount p b ≡ rootsInInterval p a b (mod 2)`, i.e. the
axiom. Certificate `verify_budan_parity.py` (numpy; 288 cases over real-root multisets ×
complex pairs × leading signs × endpoints) asserts (A),(B),(C),(D) **and** the axiom
`Even(V_a−V_b−N)` directly, plus reconfirms the upper bound `N ≤ V_a−V_b`. All pass.

### Formalization plan (the honest difficulty split)

| Step | Statement | Difficulty | Mathlib support |
|------|-----------|-----------|-----------------|
| **P1** | `parity(signChangesInList l) = (firstNonzeroSign l ≠ lastNonzeroSign l)` | elementary list induction on `countAdjacentDiffs` (~40–70 LOC) | none needed (self-contained); `List.destutter` analogue if going through Mathlib |
| **P2** | last Budan entry `= n!·leadingCoeff` (sign-constant); first `= p(x)` ⇒ `parity(budanCount p x) = [sign p(x) ≠ sign lead]` | moderate (~30–50 LOC) | `iterDeriv` (in-file), `Polynomial.iterate_derivative_eq_factorial…`/`leadingCoeff` |
| **P3** | `[sign p(a) ≠ sign p(b)] ⟺ Odd(rootsInInterval p a b)` | **the real work** (~100–150 LOC) | `Polynomial.roots`, `Polynomial.eval`-as-product, `Multiset.countP`, sign-of-product over roots |

**P1, P2 are routine and Mathlib-light; P3 is where the FTA/factorization content lives.**
`budan_parity` is therefore **NOT** a one-liner corollary of Mathlib's RuleOfSigns (which only
gives the bound), but it IS reducible to P1+P2+P3, with P3 the genuine theorem. This refutes the
optimistic "close via Mathlib's FTA" reading — Mathlib's FTA helps **P3 only**, and even there
it is the factorization machinery (not a packaged parity lemma) that carries it.

**Build status:** no Lean written (dual blackout; P1/P2 are blind-authorable with moderate
confidence but P3's `roots`-product sign argument needs a live build to iterate). The remaining
two axioms (`budan_upper_bound`, `budanCount_large`) are out of scope for this OQ; note
`budan_upper_bound` ↔ Mathlib's `roots_countP_pos_le_signVariations` is itself a candidate
reduction for a sibling session.

### Mathlib bearers pinned @ rev `2df2f01` / v4.26.0
- `Polynomial.signVariations` + `Polynomial.roots_countP_pos_le_signVariations` —
  `Mathlib/Algebra/Polynomial/RuleOfSigns.lean:50,382` (the BOUND; parity absent).
- `Polynomial.taylor` — `Mathlib/Algebra/Polynomial/Taylor.lean` (the (A) bridge).
- `List.destutter` — `Mathlib/Data/List/Destutter.lean` (the (B) parity engine, if going via Mathlib).
- `Polynomial.roots` / `Multiset.countP` / eval-as-product — for P3.

## Session 2026-06-15 (S2, researcher-8) — ACT: P1 parity engine written (build-pending)

**Mode:** FRESH (richest non-flagged available slug; 0 open PRs). **Both backends still down**
(Docker `docker info` times out; Aristotle MCP `prove` → `"Resource not found"` on a trivial
`n + 0 = n` ping). So: numerically certified hand proof, build-pending.

### What I did
Wrote **P1** — the combinatorial parity engine S1 flagged as elementary but never authored —
as a self-contained companion `proofs/Proofs/DescartesRuleOfSignsOQ02Parity.lean` (UNREGISTERED):

```
theorem countAdjacentDiffs_parity (a : ℤ) (t : List ℤ)
    (hpm : ∀ y ∈ a :: t, y = 1 ∨ y = -1) :
    countAdjacentDiffs (a :: t) % 2 = (if a = (a :: t).getLast _ then 0 else 1)
```

i.e. for a `±1` list, sign-change count is even ⟺ head = last. `countAdjacentDiffs` is copied
**verbatim** from `DescartesRuleOfSignsOQ02.lean:130`, so the lemma drops straight into the main
file (same def, same intended namespace).

### Proof shape (the reusable trick)
Structural induction on the tail. Each adjacent difference *toggles* the running value in the
2-element set `{1,-1}`; the only non-formal step is the XOR identity `[a≠b] ⊕ [b≠z] = [a≠z]`,
discharged by `rcases` on the three `±1` endpoints (a, b, last `z`) → `split_ifs at ih ⊢` →
`omega`. Key API: `List.getLast_cons` (push last to the tail), `List.getLast_mem` (last is `±1`),
`obtain ⟨z, hz_eq⟩` to free the `getLast` term so its `±1` value can be `rcases`-substituted.
**No `generalize … at`** — `omega` atomizes the opaque `countAdjacentDiffs (b::rest)` and pins its
parity from `ih` directly.

### Verification
`countAdjacentDiffs_parity` claim checked exhaustively over **all 2046** `±1` lists of length
1–10 (`python3` inline): 0 failures. Math is solid; only Lean-API/`rw`-fire risk remains
(unbuildable under blackout).

### Where this sits in the plan
This is exactly **P1** from S1's table. It gives `parity(signChangesInList l) = [firstSign ≠
lastSign]` once composed with the `signs`-map (values `±1` by construction). **P2** (first sign
`= sign p(x)`, last `= sign(n!·leadingCoeff)`, sign-constant in `x`) and **P3** (the FTA content
`[sign p(a)≠sign p(b)] ⟺ Odd(rootsInInterval)`) are still open; P3 is the genuine theorem and
needs a live build to iterate the `roots`-product sign argument.

### Next steps
- Live build: typecheck the companion; if `List.getLast_cons` arg form / `mem_cons_self` arity
  drift, repair, then **move the lemma into `DescartesRuleOfSignsOQ02.lean`** next to its `countAdjacentDiffs`.
- P2: prove last Budan entry `= n!·leadingCoeff` (sign-constant) via in-file `iterDeriv` +
  `Polynomial.iterate_derivative_…`; compose with P1 for `parity(budanCount) = [sign p(x) ≠ sign lead]`.
- P3: the `Polynomial.roots` eval-as-product sign argument (~100–150 LOC) — the one piece that
  truly discharges `budan_parity_axiom`.

## Dead Ends / Refuted

- **"`budan_parity` is a direct corollary of Mathlib's Descartes (`RuleOfSigns.lean`)."** No —
  Mathlib proves only the inequality `countP_pos ≤ signVariations`, never the parity. (S1, by
  reading the file at the pin.)
- **"Parity follows from complex-conjugate-pair counting (FTA)."** This is the *global* picture
  and obscures the cleaner endpoint route (B)+(C). The interval parity needs (D)'s real-root
  factorization sign argument, for which conjugate pairs are simply *irrelevant* (they never
  change `sign p` on ℝ). (S1.)
