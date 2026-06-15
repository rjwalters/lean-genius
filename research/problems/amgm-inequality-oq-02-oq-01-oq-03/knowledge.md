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

## Mathlib Gaps

- No general **Finset** Newton's identity; Mathlib's Newton identities live in
  `MvPolynomial` (`psum_eq_mul_esymm_sub_sum`, `mul_esymm_eq_sum`). The concrete Finset
  statement must be built (Route A) or bridged via `aeval` (Route B).

## Next Steps

1. Build-verify `AmgmInequalityOQ02OQ01OQ03.lean` (Docker down this session); on success
   register it in `proofs/Proofs.lean` and add the gallery `src/data/proofs/<slug>/`.
2. Finish the concrete general Finset version from `SKELETON_finset_concrete.lean`. The
   only real work is the `cube_partition` crux (L2); the rest is `ring`/`erase` algebra.
3. The `cube_partition` (L2) and `two_e2_eq_off_diag` (L4) lemmas are good Aristotle
   candidates once the backend is back (404 all of 2026-06-15).

---

## Dead Ends

- None yet. The direct ordered-triple partition (L2) is the unverified crux, but its
  multiplicities (1/3/6) are cert-confirmed, so it is sound — only the Lean bookkeeping
  remains.

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

## Session 2026-06-15 (Session 2) — partial proof + a Route-A correctness finding (build-pending)

**Mode**: continue · **Outcome**: progress + finding (dual blackout, build-pending).

New file `proofs/Proofs/AmgmInequalityOQ02OQ01OQ03Finset.lean` turns the S1 skeleton
into a partially-proven file:

- **PROVEN `D_collapse` (L3)**: `Doff = e₁·p₂ − p₃` via `Finset.sum_erase_eq_sub`
  (pull `fᵢ²` out, `∑_{j≠i} fⱼ = e₁ − fᵢ`, distribute). 0 sorries.
- **PROVEN `offdiag_pair_eq`**: `∑ᵢ∑_{j≠i} fᵢfⱼ = e₁² − p₂` (`linear_combination -h`
  off the parent `AMGMInequalityOQ02OQ01.sq_sum_eq_diag_plus_offdiag`). Reusable.
- **PROVEN `two_mul_newton_girard`**: `2·p₃ = 2·(e₁³ − 3e₁e₂ + 3e₃)`, the honest
  endpoint of Route A, assembled by `linear_combination hL2 + 3·hL3 + 3·e₁·hL4 −
  3·e₁·hpar` (coefficients verified in sympy). Valid over any `CommRing`. (Depends
  on the two cruxes `cube_partition`, `two_e2_eq_off_diag`, still `sorry`.)

**FINDING (corrects the S1 skeleton).** Route A's ordered-triple partition
determines only **`2·p₃`**, not `p₃`. The skeleton's final "÷2" step is **invalid
over a general commutative ring** — it fails in characteristic 2 (e.g. `ℤ/2`,
where the four relations hold but do not pin `p₃` without a `½`). The bare identity
`p₃ = e₁³ − 3e₁e₂ + 3e₃` is nonetheless TRUE over every ring (integer
coefficients); proving it in full generality requires **Route B** — the `aeval`
specialization of the already-proven universal `psum_three_closed` — not the
partition. So `newton_girard_three_finset` is left as a documented `sorry` to be
closed by Route B, and Route A's reach is recorded exactly by
`two_mul_newton_girard`.

**Remaining cruxes** (the only blocking `sorry`s): `cube_partition` (L2,
`powersetCard 3` ↔ ordered triples, mult. 1/3/6) and `two_e2_eq_off_diag` (L4,
`powersetCard 2` ↔ ordered pairs) — both good Aristotle targets once the backend
returns. The Route-B `aeval` bridge (its one fiddly step is the `powersetCard`
reindex from `univ : Finset ↥s` onto `s`) is the path for the general main theorem.
