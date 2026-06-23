# S13 AUDIT — `meerschaert_scheffler` soundness + state correction

**Date**: 2026-06-13
**Agent**: researcher-1
**Mode**: REVISIT (RICH, knowledge score 31)
**Phase**: OBSERVE / AUDIT (build-free — Docker down, Aristotle backend 404)
**Outcome**: Two findings. (A) The knowledge base was materially stale.
(B) The sole remaining axiom `meerschaert_scheffler` appears to be **mis-stated**:
as literally written its RHS is **unsatisfiable for non-degenerate
operator-stable laws**, while its LHS is provably true — so the asserted
biconditional is **false** at concrete instances (e.g. `d=1`, `Sg=[[1]]`).

No Lean files were modified this session (no verification route available;
the fix is non-trivial and must land under recovered build infra).

---

## 0. Infra reality at session start (2026-06-13)

- **Docker daemon**: DOWN (`docker info` hangs / empty `Server:`). Local
  `docker-build.sh` cannot verify any Lean change.
- **Aristotle MCP**: backend `https://aristotle.harmonic.fun/api/v1/project`
  returns **404** (confirmed via `scripts/aristotle/mcp-smoke-test.sh`). No
  server-side verification route.
- **CI**: does not build Lean.
- **Disk**: recovered to 15% used (git writes safe).

Conclusion: only **build-free** work is safe to ship. This session is an
audit + documentation correction, which fits.

---

## 1. State correction — the knowledge base was stale

`knowledge.md` (and the progressSummary in the research JSON) described the
parent file `proofs/Proofs/CentralLimitTheoremOQ01OQ01OQ04.lean` as carrying
**6 axioms** with an active "discharge roadmap" to take `axiomCount 6 → 4`
(S7/S8/S9 ACT on `gaussian_has_scalar_exponent`,
`gaussian_is_operator_stable`, `gaussian_in_own_doa`, plus E.1/E.2 honesty
corrections).

**Current actual state of the parent file (verified by reading, 2026-06-13):**

| Metric | Stale knowledge.md | Actual now |
|--------|--------------------|------------|
| `axiom` declarations | 6 | **1** (`meerschaert_scheffler`, line 409) |
| sorries | 0 | 0 |
| line count | 343–359 | 529 |
| theorems | 9–10 | 15 |

All of the "routine" Gaussian axioms in the old roadmap have since been
discharged to `theorem`s and merged (e.g. `gaussian_has_scalar_exponent`
@186, `gaussian_is_operator_stable` @216, `gaussian_in_own_doa` @442,
`scalar_exponent_ge_half` @392, `finite_cov_in_gaussian_doa` @499 — all now
proven, several flagged as *vacuous discharges of mis-encoded hypotheses*).
The S7–S12 "ACT/PREP" roadmap entries in the old `nextSteps` are **obsolete**.

A future session claiming this problem should NOT pursue the old
axiom-elimination roadmap — it is done. The only axiom left is the deep one,
and (per §2) it is not merely deep but mis-stated.

---

## 2. Soundness finding — `meerschaert_scheffler` RHS is unsatisfiable

### 2.1 The axiom as written (parent lines 409–419)

```lean
axiom meerschaert_scheffler (d : ℕ) (φ : (Fin d → ℝ) → ℂ) :
    (∃ ψ : (Fin d → ℝ) → ℂ, InOperatorDomainOfAttraction d φ ψ) ↔
    ∃ (E : Matrix (Fin d) (Fin d) ℝ) (ν : (Fin d → ℝ) → ℂ),
      ∀ t : ℝ, 0 < t →
      ∀ ξ : Fin d → ℝ,
      Filter.Tendsto
        (fun n : ℕ =>
          (φ (fun i => (n : ℝ) * ξ i)) ^ n /
          ν (fun i => ∑ j, NormedSpace.exp ℝ (Real.log t • E) i j * ξ j))
        Filter.atTop (nhds 1)
```

The numerator scaling is `φ(fun i => (n:ℝ) * ξ i)` — i.e. the argument
**grows** like `n·ξ`. This is the crux.

### 2.2 Concrete falsifying instance

Take `d = 1`, `Sg = !![1]` (so `φ = gaussCharFun 1 Sg`), `ξ = ![1]`,
and any `t > 0`.

**LHS is TRUE.** `gaussian_in_own_doa 1 Sg` (parent line 442) proves
`InOperatorDomainOfAttraction 1 φ φ`, so `∃ ψ, InOperatorDomainOfAttraction 1 φ ψ`
holds with `ψ = φ`.

**RHS is FALSE.** Compute the numerator. With
`quadForm 1 Sg ξ = Sg 0 0 · ξ 0 · ξ 0 = 1` and the quadratic scaling
`quadForm(c·ξ) = c²·quadForm(ξ)` (parent §II):

```
φ(n·ξ)            = exp(-quadForm(n·ξ)/2)        = exp(-n²/2)
(φ(n·ξ))^n        = exp(-n²/2)^n                 = exp(-n³/2)  → 0   as n → ∞.
```

The denominator `ν(fun i => ∑ j, exp(log t • E) i j * ξ j)` is **independent
of `n`** (n appears only in the numerator). So for any fixed choice of the
existentially-quantified `E` and `ν`, the denominator is a constant `c ∈ ℂ`
in `n`, and the ratio behaves as:

- if `c ≠ 0`: `exp(-n³/2)/c → 0 ≠ 1`;
- if `c = 0`: in Mathlib `z / 0 = 0`, so the ratio is `0` for every `n`, → `0 ≠ 1`.

Either way the `Tendsto … (nhds 1)` fails at this single `ξ` (and this `t`),
and the RHS requires it to hold for **all** `ξ` and **all** `t > 0`. Hence
**no** `(E, ν)` satisfies the RHS: the RHS is false.

**Therefore** the biconditional asserted by `meerschaert_scheffler 1 φ` is
`True ↔ False` = `False`. The axiom asserts a false proposition at this
instance.

### 2.3 Why this matters (axiom integrity)

This is not "deep-but-true-and-unproven." It is a **false** axiom instance.
Because `gaussian_in_own_doa` already proves the LHS, anyone who `open`s this
namespace can:

1. apply `meerschaert_scheffler 1 φ |>.mp ⟨φ, gaussian_in_own_doa 1 Sg⟩` to
   obtain the RHS, then
2. derive `False` from a proof of `¬RHS` (the limit computation above).

So the parent file is, in principle, **logically inconsistent** via this
single axiom — a strictly worse status than "axiomatized with a sound but
unproven assumption." The gallery currently advertises this file as
`axiomCount: 1`; that count is honest, but the *nature* of the axiom should be
recorded as **suspected-unsound / mis-stated**, not "deep result pending
Mathlib."

### 2.4 Root cause (likely transcription error)

The genuine Meerschaert–Scheffler DOA criterion (M&S 2001, Thm 8.2.1) is a
**regular-variation-of-the-tail-measure** condition, written with a
**shrinking** normalization `A_n → 0` (e.g. `A_n = n^{-E}`), not a growing
`n·ξ` argument inside the characteristic function. The `(φ(n·ξ))^n` form
conflates:

- the **convolution** normalization (which uses `A_n ξ` with `A_n → 0`, as in
  `InOperatorDomainOfAttraction` / `IsOperatorStable` in this very file), and
- the **tail-measure RV ratio** (which is stated on the Lévy measure, not on
  `(φ(·))^n`).

The current statement is a chimera of the two and matches neither.

---

## 3. Recommended fix (for an ACT session under recovered infra)

**Do not paste-ship blind.** When Docker (or Aristotle) is back, one of:

1. **Preferred — restate to match M&S 8.2.1.** Replace the RHS with the
   correct tail/normalization form. The cleanest in-file-consistent version
   reuses the existing `IsOperatorStable`/`InOperatorDomainOfAttraction`
   normalization shape (shrinking `A_n`), so that the Gaussian case is a
   genuine instance rather than a contradiction. This is real mathematical
   modelling work (matrix regular variation is still absent from Mathlib, so
   the RHS will remain an honest axiom — but a *true* one).

2. **Minimum honesty patch.** If a full restatement is out of scope, change
   the numerator argument from `(n : ℝ) * ξ i` to a shrinking normalization
   `ξ i / (n : ℝ)` (or `ξ i * (n:ℝ)^(-1)`) and re-derive whether the Gaussian
   instance then holds with `ν = ψ` and `E = (1/2)·I`. This needs a build to
   confirm — flag as ACT, not PREP-ship.

3. **Disprove-and-document.** Land a `theorem`
   `meerschaert_scheffler_as_stated_is_false : ¬ (meerschaert_scheffler_statement 1 (gaussCharFun 1 !![1]))`
   proving `¬RHS` for the witness above, and demote the axiom to a clearly
   labelled `*_BROKEN` placeholder. This converts the soundness bug into a
   *verified* negative result (still needs a build for the limit lemma
   `Tendsto (fun n => exp(-n³/2)) atTop (nhds 0)`).

The R1 "Gaussian-specialised restatement" planned in S1 is **superseded**:
its premise (that the Gaussian satisfies the axiom RHS by `matrix_exp_log` +
`gaussian_in_own_doa`) is exactly what §2 shows to be false for the *as-stated*
RHS. Any R1 work must wait on the §3 fix.

---

## 4. Witness, paste-ready (for the §3.3 disprove route)

For the ACT session, the load-bearing analytic fact is:

```lean
-- numerator → 0
example : Filter.Tendsto (fun n : ℕ => Real.exp (-(n:ℝ)^3 / 2)) Filter.atTop (nhds 0) := by
  sorry  -- Real.tendsto_exp_atBot ∘ tendsto of -(n^3)/2 → atBot
```

and then `(φ(n·ξ))^n = ((exp(-n²/2) : ℂ))^n = exp(-n³/2 : ℝ) : ℂ`, whose norm
is `exp(-n³/2) → 0`, so the complex sequence → 0 ≠ 1 for any fixed
denominator. (Unverified — Docker down. Statement-level only.)

---

## 5. Honest progress accounting

- **Lean delta this session**: none (0 axioms removed, 0 theorems added).
- **Knowledge delta**: corrected a materially stale state record (6→1 axiom)
  and surfaced a previously-unrecorded **soundness** problem in the sole
  remaining axiom, with a concrete falsifying witness and a 3-option fix plan.
- This does **not** discharge or fix the axiom. It re-prioritises the
  problem: the next actionable step is a soundness fix (§3), not the old
  R1/R2 roadmap.
