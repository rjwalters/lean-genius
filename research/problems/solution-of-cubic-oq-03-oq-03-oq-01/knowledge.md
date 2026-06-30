# Knowledge Base: solution-of-cubic-oq-03-oq-03-oq-01

Discharging the three remaining axioms of `proofs/Proofs/GeneralQuartic.lean`.

---

## Problem Understanding

The OQ ("prove the Ferrari factorization axioms") is **stale**: the Ferrari
factorization declarations are already proven theorems (lines 167/183/207/232/323).
The file has **3 axioms, 0 sorries**. The real target is those 3 axioms — see
`problem.md` for the table.

All three are **routine, classical facts** (FTA for a quartic; the quadratic
formula for a biquadratic). None is open mathematics. This is an axiom-discharge
de-risking ORIENT, build-gated by Docker being down this session.

---

## Per-axiom buildability assessment

### (A1) `quartic_has_four_roots` — MEDIUM, ~80 LOC
`quarticPoly a b c d = X⁴ + C a·X³ + C b·X² + C c·X + C d` is **monic of degree 4**
(GeneralQuartic.lean:74), so for all coefficients it splits over ℂ.

**Confirmed bearers @ Mathlib v4.26.0:**
- `IsAlgClosed.splits` (`FieldTheory/IsAlgClosed/Basic.lean:64`) — every ℂ-poly splits.
- `Polynomial.Splits.eq_prod_roots_of_monic` (alias `eq_prod_roots_of_monic_of_splits_id`,
  `Algebra/Polynomial/Splits.lean:203`) — monic + splits ⇒ `p = ∏ (X − rᵢ)`.
- `Polynomial.Splits.natDegree_eq_card_roots` (`Splits.lean:176`) — `card (roots p) = 4`.
- `Polynomial.mem_roots` — for `p ≠ 0`, `x ∈ roots p ↔ IsRoot p x`.

**Route:** monicity ⇒ `p ≠ 0`; `mem_roots` gives `eval x = 0 ↔ x ∈ roots p`; the
roots multiset has card 4 (`natDegree_eq_card_roots`); destructure it into
`r₁,r₂,r₃,r₄` (repeats allowed) so multiset-membership becomes the 4-fold
disjunction. The only finicky bit is enumerating a card-4 `Multiset` into four
named elements (no `Multiset.card_eq_four` helper at the pin — do it stepwise from
`card_eq_three` analogue or via `roots.toList` length-4 pattern match).

### (A2) `biquadratic_forward` — MEDIUM, ~60 LOC
With `q = 0`, set `w = y²`; then `y⁴ + p y² + r = w² + p w + r`. Let
`s = Complex.cpow (p²−4r) (1/2)`. The **only** non-elementary fact needed is
`s² = p²−4r`, supplied by:
- **`Complex.cpow_nat_inv_pow`** (`Analysis/SpecialFunctions/Pow/Complex.lean:137`,
  v4.26.0): `(x ^ (n⁻¹ : ℂ)) ^ n = x` for `n ≠ 0`; with `n = 2` and `1/2 = 2⁻¹`
  (`one_div`) this is exactly `s² = p²−4r`. (Also `Complex.cpow_ofNat_inv_pow`, line 142.)

Given `s² = p²−4r`, the resolvent quadratic factors as `w² + p w + r = (w−z₁)(w−z₂)`
with `z₁,₂ = (-p ± s)/2` (verified symbolically, see script). A root of the LHS
makes a factor vanish; ℂ is an integral domain ⇒ `w = z₁ ∨ w = z₂`.

### (A3) `biquadratic_backward` — EASY, ~40 LOC
Converse: substitute `y² = z₁` (or `z₂`) and reduce `z² + p z + r` to 0 using the
same factorization + `s² = p²−4r`. Pure `ring`/substitution once `s²` is rewritten.

**Total estimate: ~150–200 LOC, all bearers present at the pin. Docker-gated only.**

---

## Durable verification (build-free)

`verify_quartic_axioms.py` (sympy + cmath) checks, with all assertions passing:
- **A2/A3 core:** `z² + p z + r ≡ (z−z₁)(z−z₂)` under `s² = p²−4r`; Vieta sum/product.
- **A3 backward:** `y² ∈ {z₁,z₂} ⇒ y⁴ + p y² + r = 0`.
- **A2 forward:** `w² + p w + r = 0 ⇒ (w−z₁)(w−z₂) = 0 ⇒ w = z₁ ∨ w = z₂`.
- **cpow branch:** principal `√` (Python `**0.5` = `Complex.cpow · (1/2)`) satisfies
  `s² = D` over 2000 random complex `(p,r)` and on the negative-real branch cut —
  grounding the one branch-sensitive Lean fact.
- **A1:** `X⁴+aX³+bX²+cX+d ≡ ∏(X−rᵢ)` under Vieta; `eval(rᵢ)=0 ∀i` and non-roots ≠ 0
  over 3000 random root tuples (including repeated roots).

This grounds the math behind all three axioms so the Lean discharge is a
transcription task, not a discovery task.

---

## Dead Ends / Cautions

- **Do not** re-attempt the Ferrari *factorization* declarations — they are already
  theorems. Target only A1/A2/A3.
- The `cpow(·, 1/2)` square is the **only** subtle step; it is NOT `ring`-provable —
  it needs `Complex.cpow_nat_inv_pow` + a `one_div`/`2⁻¹` normalization. A naive
  `field_simp; ring` will fail on the biquadratic axioms.
- A1's multiset-of-4 enumeration into a disjunction is where blind Lean is risky;
  this is why the discharge is Docker-gated rather than written blind this session.

---

## Next Steps (ACT, build-gated)

1. **A3** first (easiest): rewrite `s²`, then `ring`. Confirms the cpow pattern.
2. **A2**: reuse the `(w−z₁)(w−z₂)` factorization; `mul_eq_zero`.
3. **A1**: `IsAlgClosed.splits` → `eq_prod_roots_of_monic` → `natDegree_eq_card_roots`
   → destructure card-4 multiset → `mem_roots`. Candidate for Aristotle once the
   surrounding scaffolding compiles.
4. Update `meta.json` `axiomCount` 3 → 0 and `status` once all three land green.

---

## Session Log

### 2026-06-14 (Session 1) — ORIENT

**Mode**: FRESH · **Outcome**: progress (ORIENT, no .lean; both backends down)

- Claimed fresh available OQ (knowledge 0). Docker hangs; Aristotle backend
  "Resource not found" — build-free session.
- Read `GeneralQuartic.lean`: found OQ framing stale (Ferrari factorization already
  theorems); isolated the **3** genuine remaining axioms A1/A2/A3.
- Confirmed every needed Mathlib bearer **present at pin v4.26.0** via `gh api`
  (`Complex.cpow_nat_inv_pow`, `IsAlgClosed.splits`, `Splits.eq_prod_roots_of_monic`,
  `Splits.natDegree_eq_card_roots`, `Polynomial.mem_roots`).
- Wrote `verify_quartic_axioms.py`; all assertions pass (quadratic-formula
  factorization, biquadratic forward/backward, principal-branch `s²=D`, quartic
  root-set split).
- Verdict: all 3 axioms buildable, ~150–200 LOC, Docker-gated. Phase OBSERVE→ORIENT.
- **Next**: ACT — discharge A3, A2, A1 in that order.

### 2026-06-16 (Session 2) — ACT (build-pending discharge written)

**Mode**: DEPTH (knowledge WEAK→RICH) · **Outcome**: progress (all 3 axioms
written as theorems in an UNREGISTERED orphan; dual blackout so build-pending)

- Dual blackout confirmed this session: `docker info` times out (>30s); Aristotle
  MCP `prove` returns `{"status":"error","message":"Resource not found."}` (404).
  So no Lean build and no Aristotle — same blackout the other 06-16 sessions hit.
- Wrote **`proofs/Proofs/GeneralQuarticAxiomsDischarge.lean`** — a staging file,
  deliberately **NOT** imported by `Proofs.lean` (zero risk to the registered
  `Proofs` build / gallery). Contains theorem versions of all three axioms,
  statements mirroring the `axiom` lines verbatim so they can be inlined to
  replace them and drop `axiomCount` 3→0:
  - `cpow_half_sq` — the one non-`ring` fact `s² = p²−4r` for `s = (p²−4r)^{1/2}`,
    via `Complex.cpow_nat_inv_pow` after rewriting `1/2 = ((2:ℕ):ℂ)⁻¹`.
  - `biquadratic_backward'` (A3) — `rw [y⁴=(y²)², hz]` then
    `linear_combination (1/4)*hs`. **HIGH confidence.**
  - `biquadratic_forward'` (A2) — factor `(y²−z₁)(y²−z₂)=0` via
    `linear_combination h − (1/4)*hs`, then `mul_eq_zero` + `sub_eq_zero.mp`.
    **HIGH confidence.**
  - `quartic_has_four_roots'` (A1) — `unfold quarticPoly; compute_degree!` for
    `natDegree=4`; `IsAlgClosed.splits _ : p.Splits`;
    `Splits.natDegree_eq_card_roots` for `card roots = 4`; destructure length-4
    `roots.toList` into `[r₁,r₂,r₃,r₄]`; `Polynomial.mem_roots hp0` +
    `IsRoot.def`. **MEDIUM confidence** — the length-4 `rcases`/`cases tl`
    enumeration and `compute_degree!` are the only unverified-by-build steps.
- **API NOTE (v4.26 drift from S1 notes):** `Splits` is now a **one-argument**
  predicate `p.Splits` (splits over its own field). `IsAlgClosed.splits` is the
  class field `∀ p, p.Splits` (use `IsAlgClosed.splits _ : p.Splits`).
  `IsAlgClosed.splits_codomain` is **deprecated** (since 2025-12-09). Use
  `Splits.natDegree_eq_card_roots : p.Splits → p.natDegree = card p.roots`
  (not the old `splits_iff_card_roots`). `Polynomial.mem_roots (hp : p ≠ 0)`,
  `Multiset.length_toList`, `Multiset.mem_toList`, `Polynomial.IsRoot.def` all
  present.
- Verified the **exact** `linear_combination` coefficients are ring identities
  (sympy residual 0 for A2, A3-b1, A3-b2). Existing `verify_quartic_axioms.py`
  still passes (all 8 checks). So A2/A3 are de-risked to "transcription is
  correct"; only Lean-elaboration surprises remain.
- Did **NOT** touch `meta.json` axiomCount (still 3) — the registered file still
  has the 3 axioms; no overclaiming until they're replaced & build-verified.
- **Next (Docker up):** (1) `docker-build.sh Proofs.GeneralQuarticAxiomsDischarge`
  to verify; fix any A1 enumeration/elaboration nits. (2) Inline the three proofs
  into `GeneralQuartic.lean` replacing the `axiom` lines, delete the orphan,
  rebuild `Proofs.GeneralQuartic`. (3) Set `meta.json` leanFile.axiomCount 3→0
  and bump status/badge to verified/original. (4) Aristotle is the fallback for
  A1 if the manual enumeration fights the elaborator (404 this session).
