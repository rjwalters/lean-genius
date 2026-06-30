# Knowledge Base: amgm-inequality-oq-02-oq-01-oq-03

Newton–Girard k=3 closed form  p₃ = e₁³ − 3·e₁·e₂ + 3·e₃  over a Finset.

---

## Problem Understanding

Reduce the third power sum to elementary symmetric polynomials. Concrete (n=3) form is
the classical sum-of-cubes factorisation a³+b³+c³ = (a+b+c)³ − 3(a+b+c)(ab+ac+bc) + 3abc.
problem.md asks for the **concrete Finset** statement (parent's diagonal/off-diagonal
template), not just the MvPolynomial API.

---

## Insights

- **A proven in-repo recurrence makes the universal form nearly free.** The sibling
  `AmgmInequalityOQ02OQ01OQ02OQ01.lean` already proves (0 sorries) the recurrence
  `psum_three_eq : p₃ = e₁·p₂ − e₂·p₁ + 3·e₃` plus `psum_two_eq : p₂ = e₁² − 2e₂` and
  `psum_one_eq_esymm_one : p₁ = e₁`. The fully reduced closed form is just their `ring`
  combination — it was never stated explicitly anywhere in the gallery.
- **Universal ⊇ concrete.** The MvPolynomial closed form over `[Fintype σ] [CommRing R]`
  specialises to every concrete Finset-of-values instance by evaluation, so it is the
  *more general* statement, not a weaker one.
- **Ordered-triple partition multiplicities are 1 / 3 / 6** (all-equal / exactly-two-equal
  / all-distinct), verified exactly. The "exactly-two-equal" class contributes `3·D` with
  `D = ∑_i ∑_{j≠i} f i² f j`, and `D = e₁·p₂ − p₃`. These are the reusable combinatorial
  facts the OQ is meant to produce.
- `2·e₂ = ∑_{i≠j} f i f j` (ordered distinct pairs); the parent left this as a remark, but
  it is needed to phrase the answer through the `powersetCard` e₂.

## Built Items

- `proofs/Proofs/AmgmInequalityOQ02OQ01OQ03.lean` (build-pending, unregistered):
  - `psum_three_closed` — universal MvPolynomial closed form p₃ = e₁³ − 3e₁e₂ + 3e₃
    (corollary of the sibling's three proven lemmas; 0 sorries).
  - `cube_sum_three` — concrete n=3 sum-of-cubes instance (`by ring`; 0 sorries).
- `research/problems/.../lean/SKELETON_finset_concrete.lean` — ACT-ready skeleton for the
  general concrete Finset version: defs (e₁,e₂,e₃,p₂,p₃,D via powersetCard/erase) + the
  four lemmas (cube_partition crux, D_collapse, two_e2_eq_off_diag, final) with both
  Route A (direct partition) and Route B (aeval bridge) spelled out.
- `research/problems/.../lean/verify_newton_girard_k3.py` — durable cert: closed form,
  recurrence, k=2, partition (1/3/6), D=e₁p₂−p₃, 2e₂=off-diag, exact over n=0..8.
- `proofs/Proofs/AmgmInequalityOQ02OQ01OQ03Finset.lean` (S2, build-pending, unregistered):
  concrete general-Finset Route A. PROVEN over any CommRing: `sq_split` (k=2 split,
  inlined from parent), `D_collapse` (L3), `p2_closed`, `two_mul_p3_closed`
  (2·p₃ = 2·closed, via `linear_combination cube_partition + 3·D_collapse + 3·e₁·p2_closed`,
  sympy-checked). PROVEN over `[NoZeroDivisors R]`+`(2:R)≠0`: `newton_girard_three_finset`
  (cancel the 2 via `mul_left_cancel₀`). Remaining `sorry`: `cube_partition` (L2),
  `two_e2_eq_offPairs` (L4) — the two genuine combinatorial bridges.

## ⚠️ Char-2 obstruction (S2 finding — corrects the S1 skeleton)

**Route A (direct ordered-triple partition) does NOT prove the closed form over a general
CommRing.** Combining the three concrete facts
  (L2) `cube_partition`: e₁³ = p₃ + 3·Doff + 6·e₃,
  (L3) `D_collapse`:     Doff = e₁·p₂ − p₃,
  (L4)+(k=2):            p₂ = e₁² − 2·e₂,
yields exactly **`2·p₃ = 2·(e₁³ − 3e₁e₂ + 3e₃)`** (sympy-checked, residual 0; see
`two_mul_p3_closed`). Over ℤ/ℚ/ℝ the 2 cancels; over a ring with 2-torsion (𝔽₂) it
collapses to 0 = 0 and gives nothing. The closed form is still *true* over 𝔽₂ (verified
exhaustively, and the universal `psum_three_closed` proves it for every CommRing) — it is
just **not derivable from L2/L3/L4 there**. The S1 skeleton's "final assembly is all `ring`"
is therefore false over char 2. Consequences:
- Route A closes only under `[NoZeroDivisors R]` + `(2:R) ≠ 0` (cancel the 2).
- **Full general-CommRing generality requires Route B** (evaluate the proven universal
  `psum_three_closed` through `MvPolynomial.aeval` on the subtype `{x // x ∈ s}`), which
  carries the polynomial Newton recurrence and so survives char 2.

## Mathlib Gaps

- No general **Finset** Newton's identity; Mathlib's Newton identities live in
  `MvPolynomial` (`psum_eq_mul_esymm_sub_sum`, `mul_esymm_eq_sum`). The concrete Finset
  statement must be built (Route A, char≠2 only) or bridged via `aeval` (Route B, general).
- No single-lemma bridge `s.powersetCard 2 ↔ s.offDiag` for L4; needs `Sym2`/`sum_sym2`.

## Next Steps

1. Build-verify `AmgmInequalityOQ02OQ01OQ03Finset.lean` (Docker down this session). The
   proven parts (sq_split, D_collapse, p2_closed, two_mul_p3_closed, the char≠2 final) are
   name-checked vs the parent's compiled tactics + Mathlib master; only L2/L4 are `sorry`.
2. **Prefer Route B** for the general-CommRing concrete closed form: one `aeval` reindexing
   lemma (powersetCard of subtype-univ → powersetCard of s) supersedes BOTH L2 and L4 and
   avoids the char-2 hole entirely. This is now the recommended path, not Route A.
3. If staying on Route A: `cube_partition` (L2) and `two_e2_eq_offPairs` (L4) are good
   Aristotle candidates once the backend is back (404 all of 2026-06-15).

---

## Dead Ends

- **Route A cannot prove the general-CommRing closed form** (S2): the L2+L3+L4 assembly only
  reaches `2·p₃ = 2·closed`, which is `0=0` in char 2. The combinatorial partition is sound,
  but the route is incomplete over rings with 2-torsion. Use Route B for full generality.
- The ordered-triple partition (L2) multiplicities (1/3/6) are cert-confirmed and sound;
  only the Lean bookkeeping remains (it's valid content, just char≠2-limited as an assembly).

---

## Session 2026-06-15 (Session 1) — ACT (universal closed form shipped)

**Mode**: FRESH · **Outcome**: progress (build-pending, dual blackout)

### What I Did
- Confirmed the OQ wants the concrete Finset form; found the sibling's proven recurrence.
- Shipped `AmgmInequalityOQ02OQ01OQ03.lean`: universal closed form `psum_three_closed`
  (corollary of compiled lemmas) + concrete `cube_sum_three` (n=3). 0 sorries.
- Wrote ACT-ready skeleton + Python cert for the general concrete Finset version, with
  the ordered-triple partition multiplicities (1/3/6) verified exactly.

### Key Findings
- Closed form p₃ = e₁³ − 3e₁e₂ + 3e₃ was missing from the gallery; now a one-step `ring`
  corollary of the existing recurrence.
- Partition crux confirmed: cube = p₃ + 3D + 6e₃, D = e₁p₂ − p₃.

### Files Modified
- proofs/Proofs/AmgmInequalityOQ02OQ01OQ03.lean (new, build-pending)
- research/problems/amgm-inequality-oq-02-oq-01-oq-03/{knowledge.md, state.md,
  lean/SKELETON_finset_concrete.lean, lean/verify_newton_girard_k3.py}

### Next Steps
Build-verify + register; finish the concrete general Finset version (Route A crux L2).

## Session 2026-06-15 (Session 2, researcher-8) — ACT (Route-A assembly + char-2 finding)

**Mode**: REVISIT/CONTINUE · **Outcome**: progress (build-pending, dual blackout)

### What I Did
- Worked the concrete-Finset Route A from the S1 skeleton. While deriving the final
  assembly I found the **char-2 obstruction**: L2+L3+L4 combine to `2·p₃ = 2·closed`, not
  `p₃ = closed`. Confirmed exhaustively that the closed form still holds over 𝔽₂ but is
  *not derivable* from these three facts there.
- Shipped `proofs/Proofs/AmgmInequalityOQ02OQ01OQ03Finset.lean` (build-pending):
  PROVEN over any CommRing — `sq_split` (k=2, inlined parent technique), `D_collapse` (L3),
  `p2_closed`, `two_mul_p3_closed`; PROVEN over `[NoZeroDivisors]`+`2≠0` —
  `newton_girard_three_finset` (cancel 2). Remaining `sorry`: `cube_partition` (L2),
  `two_e2_eq_offPairs` (L4).
- sympy-verified both `linear_combination` coefficients (residual 0); cert reproduces.

### Key Findings
- **Char-2 obstruction**: the S1 "final assembly is all `ring`" claim is false over a general
  CommRing. Route A is sound only with a cancellable 2; Route B (aeval) is required for full
  generality and is now the recommended path (one reindexing lemma supersedes L2+L4).
- `linear_combination cube_partition + 3·D_collapse + 3·e₁·p2_closed` gives `2·p₃ = 2·closed`.

### Files Modified
- proofs/Proofs/AmgmInequalityOQ02OQ01OQ03Finset.lean (new, build-pending, unregistered)
- research/problems/amgm-inequality-oq-02-oq-01-oq-03/knowledge.md, state.md, research JSON

### Next Steps
Build-verify the proven parts; pursue Route B (aeval reindexing) for the general closed form;
L2/L4 → Aristotle when backend returns.
