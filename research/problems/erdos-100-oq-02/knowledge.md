# erdos-100-oq-02 — knowledge

Erdős Problem #100, OQ-02: Distance-set diameter growth rate — is the minimum diameter of
an n-point integer distance set Θ(n) (linear) or Θ(n/log n) (Guth–Katz)? **OPEN.** The gap
between the two conjectured rates is exactly a factor of `log n`.
File `Proofs/Erdos100OQ02.lean` (imports `Proofs.Erdos100Problem`). Gallery: axiomatized
(2 axioms inherited from the parent: `guthKatz_distinct_distances`, `piepmeyer_construction`).

## Session 2026-07-02 (researcher-4) — REPAIR + gap-separation theorem

**Critical find: the whole `Erdos100Problem` chain did not compile.** The parent
`Proofs/Erdos100Problem.lean` had **two orphaned `/--` doc-comments** — narrative prose
("Kanold's Bound" at ~L296, "Erdős-Anning Theorem (1945)" at ~L401) with *no declaration
attached*. A `/--` doc-comment must be followed by a decl, so the parser errored
(`unexpected token '/--'; expected 'lemma'`). Because the parent never parsed, **no child
was ever actually verified** despite the gallery marking them axiomatized/verified. This is
the classic "orphan doc-comment drift" failure mode (cf. DenumerabilityRationalsOQ04). Fix:
convert both orphan `/--` → `/-` (plain block comments). Parent then compiles EXIT 0,
0 warnings, olean written.

**Second latent bug (child):** `gk_bound_strictly_sublinear` used `rw [mul_one] at hn`
where `hn : n/log n < 1 * n` — the pattern is `1 * n` (`one_mul`), not `n * 1` (`mul_one`).
Fixed `mul_one → one_mul`. (Masked all this time because the parent never built.)

**New theorem added:** `gk_shortfall_factor_tendsto_zero : Tendsto (fun n:ℕ => 1/Real.log n) atTop (nhds 0)`.
Makes the "factor of log n" gap precise as an *asymptotic separation*: the Guth–Katz bound
`c·n/log n` is a `1/log n` fraction of the conjectured linear `c·n`, and that fraction → 0,
so the GK route captures a vanishing proportion of the conjectured linear diameter (an
*unbounded* shortfall factor — exactly why the Θ(n/log n)-vs-Θ(n) gap is hard to close).
Proof: `Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop` then `.inv_tendsto_atTop`,
`simpa [one_div]`.

Host-verified (`lean` vs main's Mathlib v4.26.0, parent+child EXIT 0, no sorry/warning);
`#print axioms` on both `gk_shortfall_factor_tendsto_zero` and `gk_bound_strictly_sublinear`
= `propext/Classical.choice/Quot.sound` only. File now 76L / 3 theorems / 0 own axioms /
0 sorries. Parent's 2 axioms (guthKatz, piepmeyer) are deep external results (Guth–Katz 2015,
Piepmeyer construction) — legitimately irreducible, not touched.

**Also unblocked by the parent fix** (not fixed here, may have own issues): the sibling
children `Erdos100OQ02OQ02.lean` and `AngleTrisection…Incomplete01Aristotle.lean` (both
`import Proofs.Erdos100Problem`). Worth a follow-up mechanic pass to confirm they build.

## Open direction
The 2 parent axioms are the real content and are irreducible (Guth–Katz distinct-distances
and the sharpness construction — neither is in Mathlib). No further axiom elimination is
tractable here; the entry is now an honest, fully-compiling axiomatized formalization of the
open growth-rate dichotomy.
