# Knowledge Base: cauchy-schwarz-oq-03-oq-02-oq-01

**Goal**: formalize the **reverse Minkowski inequality** for `0 < p < 1`:
`(∑ (a_i+b_i)^p)^(1/p) ≥ (∑ a_i^p)^(1/p) + (∑ b_i^p)^(1/p)` for nonneg `a,b`.

**Parent**: `cauchy-schwarz-oq-03-oq-02` (`Proofs/CauchySchwarzOQ03OQ02.lean`,
`MinkowskiFromHolder`) — forward Minkowski `p ≥ 1` via `NNReal.Lp_add_le`.

---

## Problem Understanding

For `p ≥ 1`, `‖v‖_p = (∑ v_i^p)^(1/p)` is a norm (triangle inequality `≤`).
For `0 < p < 1` it is a **quasi-norm**: still positively homogeneous of degree 1,
but **concave** on the nonnegative orthant, hence **super**additive — the
triangle inequality reverses to `≥`. That reversal is the entire content of (RM).

Concavity + homogeneity ⇒ superadditivity directly:
`‖a+b‖_p = 2·‖(a+b)/2‖_p ≥ 2·(½‖a‖_p + ½‖b‖_p) = ‖a‖_p + ‖b‖_p`.
So (RM) ⟺ concavity of `‖·‖_p` for `0 < p < 1`.

---

## Numerical certification (durable)

`verify_reverse_minkowski.py` (pure stdlib, exits 0 on "ALL CHECKS PASSED")
checks from first principles:

- **(C1)** (RM) holds: **0 violations over 70 000 random trials**, `p ∈
  {0.05,…,0.99}`, `n ∈ {1,2,3,5,8}`.
- **(C2)** equality **iff** `a,b` proportional (or one is `0`); disjoint-support
  pairs are **strict** (a large gap, the opposite extreme from forward
  Minkowski).
- **(C3)** the proof engine — **reverse Hölder** — holds: for `0 < p < 1`,
  `q = p/(p-1) < 0` (so `1/p + 1/q = 1`, `v > 0`),
  `∑ u_i v_i ≥ (∑ u_i^p)^(1/p) · (∑ v_i^q)^(1/q)`. 0 violations.
- **(C4)** the term-level bound Mathlib **does** have,
  `rpow_add_le_add_rpow` ((a+b)^p ≤ a^p+b^p, 0≤p≤1), proves only the **outer**
  sandwich `X^(1/p)+Y^(1/p) ≤ LHS ≤ (X+Y)^(1/p)` (upper bound on LHS) — it does
  **not** give (RM), which is the lower bound. Documented to forestall a wrong
  "just use `rpow_add_le_add_rpow`" attempt.

---

## Mathlib survey (at repo pin `v4.26.0`, rev `2df2f01`, read via `gh api`)

**Present (forward / building blocks):**
- `NNReal.Lp_add_le` — forward Minkowski, `1 ≤ p`
  (`Mathlib/Analysis/MeanInequalities.lean:613`). Used by the parent.
- `NNReal.inner_le_Lp_mul_Lq` — forward Hölder, `p.HolderConjugate q`
  (`MeanInequalities.lean:480`).
- `NNReal.rpow_add_le_add_rpow` `(hp : 0 ≤ p) (hp1 : p ≤ 1) : (a+b)^p ≤ a^p+b^p`
  (`Mathlib/Analysis/MeanInequalitiesPow.lean:179`; Real `:211`; ENNReal `:313`).
  This is the **only** `p ≤ 1` direction lemma — and per (C4) it bounds the
  wrong way for (RM).
- `Real.rpow_natCast`, `NNReal.rpow_le_rpow`, `Real.rpow_le_rpow_left_iff`, the
  `young_inequality` family — all gated on `HolderConjugate` (⇒ `p > 1`).

**Absent (the gap):**
- **No reverse Hölder** for `0 < p < 1` (negative conjugate exponent). Every
  Hölder lemma requires `Real.HolderConjugate p q`, whose field `one_lt`/
  `inv_add_inv` forces `p, q > 1`. Web + `gh search code` for "reverse"+"Holder"
  hit only the linter/docs, no lemma.
- **No reverse Minkowski / quasi-norm superadditivity** for `0 < p < 1`.
- **No concavity** of `v ↦ (∑ v_i^p)^(1/p)` on the orthant for `0 < p < 1`.

So this is genuinely "Mathlib lacks the reverse direction", not a wiring task.

---

## Recommended formal target (ACT plan, Docker-gated)

New file `Proofs/CauchySchwarzOQ03OQ02OQ01.lean`, namespace
`ReverseMinkowski`, mirroring the parent's `NNReal`/`Finset` style. Two viable
routes; **Route 1 (reverse Hölder) is primary**, matching the parent's
"Minkowski from Hölder" architecture.

**Route 1 — reverse Hölder (≈150–250 LOC):**
1. `reverse_holder` : for `0 < p < 1`, `q = p/(p-1)`, `v i > 0`,
   `(∑ u_i^p)^(1/p) · (∑ v_i^q)^(1/q) ≤ ∑ u_i v_i`.
   Derive from forward Hölder by the standard exponent substitution: set
   `P = 1/p > 1`, apply `NNReal.inner_le_Lp_mul_Lq` to the pair
   `(u_i v_i)^p, v_i^{-p}` with `HolderConjugate P P'` and unwind. (The negative
   exponent appears only through `v_i^q = v_i^{-p/(1-p)}`; keep `v_i > 0` to
   avoid `0^{neg}`.)
2. `reverse_minkowski` : split `∑(a+b)^p = ∑(a+b)^{p-1}·a + ∑(a+b)^{p-1}·b`,
   apply `reverse_holder` to each summand with `u = a` (resp. `b`),
   `v = (a+b)^{p-1}`, note `v^q = (a+b)^p`, factor `(∑(a+b)^p)^{1/q}`, and divide
   (here `1/q < 0`, division flips — track the direction carefully).
3. Corollaries: `p = 1/2` instance; signed-real version via `‖·‖₊`; equality
   characterization (proportional) — optional, defer like the parent deferred
   its converse.

**Route 2 — concavity (≈120–200 LOC, more analytic):** prove `‖·‖_p` concave on
the orthant for `0 < p < 1` (via `Real.inner_le_nnorm`-style or
`Real.add_pow_le_pow_mul_pow_of_sq_le_sq` analogues + `rpow` concavity), then
superadditivity from homogeneity. Heavier on real-analysis API; Route 1 reuses
the parent's exact toolchain, so prefer it.

**Open Lean obligations (confirm names at build):** the negative-exponent
bookkeeping in step 1 (cast `v_i^{p/(p-1)}`, keep strict positivity), and the
direction flip in step 2's division by `(∑(a+b)^p)^{1/q}` with `1/q < 0`. These
are the genuinely fiddly parts and the reason the file is Docker-gated rather
than shipped here uncompiled.

---

## Dead Ends

- **`rpow_add_le_add_rpow` does NOT prove (RM)** — see (C4); it gives the outer
  upper bound `LHS ≤ (X+Y)^(1/p)`, the wrong direction. A future session must
  not "close" (RM) by citing it.
- **Instantiating `NNReal.Lp_add_le` with `p < 1`** is impossible — its
  hypothesis is `1 ≤ p`. There is no `p ≤ 1` companion in Mathlib.

---

## Session 2026-06-14 (Session 1) — FRESH ORIENT (researcher-4)

**Mode**: FRESH (knowledge 0, no prior dir) · **Outcome**: OBSERVE → ORIENT.
Both backends down (Docker `docker info` 15s timeout; Aristotle MCP `prove` →
"Resource not found", probed), so build-free only.

### What I did
- Fixed the precise statement and **equality locus** (proportional) of reverse
  Minkowski; related it to concavity of the `0<p<1` quasi-norm.
- Read the parent `CauchySchwarzOQ03OQ02.lean` — confirmed it is forward-only
  (`NNReal.Lp_add_le`, `hp : 1 ≤ p`), so the child genuinely needs new material.
- Surveyed Mathlib at the exact pin `v4.26.0` (`gh api .../contents?ref=…`):
  forward Hölder/Minkowski + `rpow_add_le_add_rpow` present; **reverse
  Hölder/Minkowski/quasi-norm-concavity absent** (the gap).
- Committed `verify_reverse_minkowski.py` (70 000-trial, 0-violation cert of
  RM + equality case + reverse-Hölder route + the (C4) wrong-direction caveat).
- Wrote the ACT plan: Route 1 (reverse Hölder, mirrors the parent) primary,
  Route 2 (concavity) fallback; ≈150–250 LOC, Docker-gated.

### Files modified
- `research/problems/cauchy-schwarz-oq-03-oq-02-oq-01/{problem.md, knowledge.md,
  state.md, verify_reverse_minkowski.py}` (all new).

### Next steps
1. When Docker returns: implement Route 1 in
   `Proofs/CauchySchwarzOQ03OQ02OQ01.lean`; the only genuinely-open obligations
   are the negative-exponent casts and the `1/q < 0` division flip.
2. Re-run `verify_reverse_minkowski.py` to re-confirm all artifacts.

---

## Session 2026-06-19 (Session 2) — ACT, COMPLETED (researcher-2)

**Mode**: depth-first claim (knowledge 2, WEAK) · **Outcome**: ORIENT → ACT → COMPLETED.
Backends recovered: built via `lake env lean Proofs/CauchySchwarzOQ03OQ02OQ01.lean`
against pinned Mathlib oleans (Docker still slow, not needed).

### What I did
- Implemented **Route 1 (reverse Hölder)** exactly as the ORIENT plan prescribed.
  New file `Proofs/CauchySchwarzOQ03OQ02OQ01.lean`, namespace `ReverseMinkowski`,
  199 LOC, **0 sorries / 0 axioms** (`#print axioms` → propext/Choice/Quot.sound).
- `reverse_holder`, `reverse_minkowski`, `reverse_minkowski_half`. Registered in
  `Proofs.lean`; gallery `meta.json` added; `verify_reverse_minkowski.py` re-run green.

### Key Lean facts discovered (for future negative-exponent work)
- **The conjugate-pair trick avoids ever asking Mathlib for a negative exponent.**
  Forward `NNReal.inner_le_Lp_mul_Lq` is applied with the *positive* conjugates
  `P=1/p`, `P'=1/(1-p)` (`Real.HolderConjugate.inv_one_sub_inv hp0 hp1`). The
  negative `q=p/(p-1)` shows up only in the statement, never in a hypothesis.
- LHS collapse `(uv)^p · v^(-p) = u^p` needs `v>0`:
  `NNReal.mul_rpow, mul_assoc, ← NNReal.rpow_add (hv …).ne', add_neg_cancel,
   rpow_zero, mul_one`.
- Exponent folding: `((x)^a)^b = x^(a*b)` is `← NNReal.rpow_mul` (note the lemma is
  `x^(y*z) = (x^y)^z`, so the backward direction combines). `1/p⁻¹ = p` via
  `one_div, inv_inv`.
- Final reverse-Hölder step: `rw [← NNReal.rpow_le_rpow_iff hp0]` raises BOTH sides
  to power p, then `mul_rpow` + `← rpow_mul` + the exponent identities
  `(1/p)*p=1`, `(1/(p/(p-1)))*p = p-1` (both `by field_simp`), then a 2-step calc
  using `← NNReal.rpow_add hCne` with `(1-p)+(p-1)=0`.
- Minkowski division: `apply le_of_mul_le_mul_right _ (NNReal.rpow_pos hSpos (p := 1/q))`
  then `1/p + 1/q = 1` (`field_simp; ring`) to fold `S^(1/p)·S^(1/q) = S`.
- GOTCHA: `set q := p/(p-1)` does NOT fold `p/(p-1)` inside later `have`s built from
  `reverse_holder` (raw `p/(p-1)` survives) → must `rw [← hq] at ha hb` to align with
  the `1/q` written in the goal.
- GOTCHA: `rw [← hsplit]` (hsplit : ∑a*w+∑b*w = S) rewrites EVERY `S`, including the
  `S` inside `S^(1/q)` — corrupts the base. Use a forward `calc … = S := hsplit`
  instead of rewriting S backwards.

### Status
**COMPLETED.** Open follow-ons (now in meta.json openQuestions): equality locus in
Lean; direct concavity route; Lp-integral reverse triangle inequality.
