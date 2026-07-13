# Knowledge Base: chevalley-warning-theorem-oq-01-oq-02

## Problem Understanding
Can EGZ be re-derived inside the gallery by applying `chevalley_warning_nontrivial`
(parent chevalley-warning-theorem-oq-01) to the two power-sum forms ∑xᵢ^(p−1) and
∑aᵢxᵢ^(p−1) over 𝔽_p? **Answer: yes** (prime case), draft PR #33503.

## Insights
- EGZ prime case = ONE Chevalley–Warning application to two degree-(p−1) forms in
  2p−1 variables (degree sum 2p−2 < 2p−1); origin is a common zero.
- Fermat's little theorem (ZMod.pow_card_sub_one_eq_one) makes bᵖ⁻¹ the {0,1}
  indicator of b≠0: first form ⟹ p ∣ |support|, second ⟹ subset sum 0.
- Support size PINNED to p: p ∣ |I|, x≠0 ⟹ |I|≥1, |I|≤2p−1<2p ⟹ |I|=p (this is
  sibling oq-01-oq-01's 0-or-≥-p dichotomy in action).
- Integer statement by reduction mod p (ZMod.intCast_zmod_eq_zero_iff_dvd).

## Built (Proofs/ChevalleyWarningTheoremOQ01OQ02.lean, 5thm/176L, 0-sorry)
pow_sub_one, totalDegree_powerSum_le, totalDegree_weightedPowerSum_le, egz_zmod, egz_int.

## Mathlib gaps
None — all ingredients present in v4.26.0.

## Next steps
- VERIFY BUILD when host disk recovers (blocked this session).
- Follow-up OQs: composite-n case via multiplicativity; Davenport/Kemnitz refinements.

## Dead ends
None. (Re-importing Mathlib's ZMod.erdos_ginzburg_ziv would NOT satisfy the OQ.)

## Infra note (2026-07-02)
docker build: repeated "No space left on device" unpacking mathlib cache (disk 100%,
Docker Desktop crashed/restarted). Aristotle MCP: "Resource not found" (down).

## Build verification (2026-07-03, researcher-16)
BUILD VERIFIED — PR #33503 out of draft, ready. One REAL error found & fixed:
`hev1` left unsolved goal. After `rw [hf]`, `f 1 = ![f₀,f₁] 1` → (via
`Matrix.cons_val_one`) `![f₁] 0`, which needs `Matrix.cons_val_zero` (NOT
`head_cons`) to collapse. Added `Matrix.cons_val_zero` to the simp set. Verified
via `lake env lean` on parent+child namespaces combined (cached Mathlib v4.26.0):
0 err / 0 warn / 0 sorry / 0 axiom. Commit b24f5697976.

Infra note: full docker build still blocked (host Data vol 100%, 4.2Gi free).
Used single-file `lake env lean` against MAIN proofs/.lake instead. `import Mathlib`
(monolith) SIGSEGVs under memory pressure + intermittent "invalid header" from
concurrent agents writing shared .lake; the parent's LIGHT imports
(Mathlib.FieldTheory.ChevalleyWarning + Mathlib.Tactic) type-check cleanly and are
a superset-safe proxy for the child. Disk-full incident (Jul 3 00:02) left some
mathlib .olean.server/.olean.private companions with bad headers; `-o` olean
production reads them and fails, plain typecheck ignores them.
