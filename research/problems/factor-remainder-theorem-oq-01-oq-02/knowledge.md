# Knowledge Base: factor-remainder-theorem-oq-01-oq-02

Insights accumulated during research on this problem.

---

## Problem Understanding

Extend the parent's multiplicity factor theorem — `(X − a)ᵏ ∣ p ↔ p, p′, …, p^{(k−1)}`
all vanish at `a`, proved over a **characteristic-zero field** via ordinary iterated
derivatives — to **positive (indeed arbitrary) characteristic** using **Hasse (divided-power)
derivatives**. The parent's open question explicitly asked for this.

---

## Insights

- The Hasse derivative is exactly the Taylor coefficient: Mathlib's `taylor_coeff` gives
  `(taylor a p).coeff m = (hasseDeriv m p).eval a`, with **no division by `m!`**. This is the
  whole reason the criterion survives in characteristic `p`, where `p^{(m)}(a)/m!` is
  meaningless once `m! = 0`.
- The clean route is a **ring-automorphism transfer**: `q ↦ q.comp (X + C a)` (which equals
  `taylor a` by `taylor_apply`) is a ring automorphism of `R[X]` carrying `X − a` to `X`, so
  `(X − a)ᵏ ∣ p ↔ Xᵏ ∣ taylor a p`. This step needs **no** characteristic hypothesis and is
  proved purely with composition lemmas (`mul_comp`, `pow_comp`, `sub_comp`, `add_comp`,
  `comp_assoc`). The `taylorEquiv`/`map_dvd_iff` route also works in principle but fought
  AlgEquiv coercions (`↑↑(taylorEquiv a)` did not match `coe_taylorEquiv` under `rw`/`simp`);
  the explicit `comp`-witness proof was more robust.
- Then `X_pow_dvd_iff` (`Xⁿ ∣ q ↔ ∀ d < n, q.coeff d = 0`) plus `taylor_coeff` finish the main
  theorem in three rewrites.
- The divisibility characterization needs **no `p ≠ 0` hypothesis** (unlike `rootMultiplicity`),
  so `factor_theorem` and `double_root_iff` are strictly more general than the parent's.
- Char-`p` witness: over `ZMod 2`, `derivative (X²) = C 2 · X = 0` (since `2 = 0`), so the char-0
  criterion would falsely certify `(X)³ ∣ X²`; `(hasseDeriv 2 (X²))(0) = (taylor 0 (X²)).coeff 2
  = (X²).coeff 2 = 1 ≠ 0` correctly refutes it. Computed via `taylor_coeff` + `taylor_zero`
  + `coeff_X_pow` (avoids needing a `hasseDeriv`-of-`X^n` lemma).

---

## Dead Ends

- `rw [coe_taylorEquiv]` / `simp only [coe_taylorEquiv]` on `taylorEquiv a x` — the AlgEquiv
  double-coercion `↑↑(taylorEquiv a)` does not match the lemma pattern cleanly. Use the
  `comp`-based proof instead.

---

## Session 2026-06-23 (Session 1) — Hasse multiplicity factor theorem

**Mode**: FRESH · **Outcome**: completed (verified, 0 axioms, 0 sorries)

### What I Did
- Wrote `Proofs/FactorRemainderTheoremOQ01OQ02.lean` (6 theorems, 0 defs, ~131 lines).
- Main: `pow_X_sub_C_dvd_iff_hasseDeriv_eval_eq_zero` over any `CommRing`, no char/`p ≠ 0`
  hypotheses; plus `pow_X_sub_C_dvd_iff_taylor`, `factor_theorem`, `double_root_iff`,
  `le_rootMultiplicity_iff_hasseDeriv`, and the `ZMod 2` witness `hasseDeriv_detects_char_p`.
- Kernel-verified on Mathlib v4.26.0 via host `lake env lean` (Docker host was wedged;
  used `lake exe cache get` to fetch oleans). `#print axioms` = `[propext, Classical.choice,
  Quot.sound]`.

### Files Modified
- proofs/Proofs/FactorRemainderTheoremOQ01OQ02.lean
- src/data/proofs/factor-remainder-theorem-oq-01-oq-02/{meta,annotations,tacticStates}.json

### Next Steps
- Possible follow-ups: separability characterization (separable ⟺ no shared root with first
  Hasse derivative); full Taylor expansion identity `p = ∑ₘ (hasseDeriv m p)(a)·(X − a)ᵐ`.
