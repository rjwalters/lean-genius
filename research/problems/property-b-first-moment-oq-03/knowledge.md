# Knowledge Base: property-b-first-moment-oq-03

Open question: sharpen the Property B lower bound to the **Radhakrishnan–Srinivasan**
`m(k) = Ω(2^k·√(k/log k))` (RS 2000) via the asymmetric/recoloring refinement of the
first moment argument. Parent `property-b-first-moment` (file `PropertyBFirstMoment.lean`)
proves Erdős' 1963 uniform bound `m(k) ≥ 2^(k-1)`.

---

## State of the parent / siblings (as of 2026-06-28)

- Parent `PropertyBFirstMoment.lean` (`ProbMethod.PropertyB`): Erdős 1963 uniform
  first-moment bound. Key reusable API: `Mono e c`, `card_mono` (exactly `2·2^(n-|e|)`
  colorings are monochromatic on a nonempty edge `e`), `exists_zero_of_sum_lt_card`
  (integer first moment principle), `card_const_on`. 0 sorries / 0 axioms.
- Sibling oq-01 → `PropertyBUpperBound.lean`: explicit non-2-colorable hypergraphs
  bracketing `m(k)` (upper bounds).
- Sibling oq-02 → `PropertyBFirstMomentRamsey.lean`: Erdős' 1947 Ramsey bound via the
  same template (edges of `K_n` as the 2-colored ground set).

## Session (2026-06-28, researcher-1): non-uniform first-moment sharpening

New file `PropertyBFirstMomentOQ03.lean` (122 lines, 3 theorems, **0 sorries / 0 axioms**,
`#print axioms` = propext/Classical.choice/Quot.sound only; the worked example uses
`decide`, NOT `native_decide`, so no `Lean.ofReduceBool`). Gallery entry
`src/data/proofs/property-b-first-moment-oq-03/` (meta.json + annotations.json) added.

Delivered the **sharp single-round first-moment criterion** — the honest, tractable part
of oq-03:

* `property_b_of_weighted_first_moment` — a finite family `E` of nonempty edges of
  *arbitrary sizes* is 2-colorable as soon as `2·∑_{e∈E} 2^(n-|e|) < 2^n`, equivalently
  the genuine Erdős criterion `∑_e 2^(1-|e|) < 1`. Proof = parent's first moment with
  `card_mono` summed over heterogeneous edge sizes (`card_filter` + `sum_comm` +
  `mul_sum` + `exists_zero_of_sum_lt_card`). Dropping uniformity is free because
  `card_mono` is already per-edge.
* `property_b_two_colorable_of_uniform` — recovers the parent's uniform theorem
  (`|e|=k`, `<2^(k-1)` edges) as a corollary; the weighted sum collapses to `|E|·2^(n-k)`.
  Confirms the refinement strictly extends the parent.
* `mixed_example_two_colorable` — `{{0,1},{0,1,2}}` over `Fin 3`: weighted sum `2+1=3`,
  `2·3=6<8`, certified 2-colorable though the uniform theorem can't be applied (mixed
  sizes). Hypotheses by `decide`.

### Why this is NOT the full oq-03 (honest scoping)

The single-round first moment is **sharp at `∑ 2^(1-|e|) < 1`** and provably cannot reach
RS `Ω(2^k·√(k/log k))`. The RS improvement needs a **random recoloring (alteration)**:
after the first uniform 2-coloring, independently recolor the vertices lying in surviving
monochromatic edges (in a fixed random vertex order, recolor with small probability `p`),
and bound `P[some edge still monochromatic]` by `m·2^(1-k)·(stuff) + m·k·p·(1-p)^(...)`,
optimized at `p ≈ (log k)/k` to give the `√(k/log k)` gain. This is a genuinely different
(two-round, order-dependent) probability model — NOT expressible by summing `card_mono`
over a single product sample space `V → Bool`.

### Roadmap / tractability verdict for RS (oq-03 remainder)

RS formalization is a **moonshot** in Lean 4.26.0:
- Needs a real-valued (or rational) probability model with a *recoloring* second stage
  and a vertex ordering — the current file's integer first-moment counting does not
  scale to it.
- Needs concentration / union-bound estimates with the `p ≈ log k / k` optimization and
  `√(k/log k)` asymptotics — heavy real-analysis bookkeeping.
- Recommended decomposition if pursued: (1) a rational two-stage "recolor-with-prob-`p`"
  expectation lemma for a single edge; (2) the union bound over `m` edges; (3) the
  `p = log k / k` optimization as a separate analytic lemma. Each is a multi-session
  effort. Until (1)–(3) exist, further single-round first-moment work adds nothing new
  beyond the criterion proved this session.

## Session (2026-06-28, researcher-4): asymmetry cannot beat Erdős (RS sub-question, NEGATIVE)

Addressed the **first follow-up open question** of the merged oq-03 (formalize the RS
recoloring sharpening) by settling its **asymmetry ingredient negatively**. The RS program
has two parts — (1) biasing/asymmetry of the random coloring, (2) the recoloring repair.
This session proves part (1) is **worthless on its own**, sharply isolating the recoloring
step as the sole remaining target. Published as new gallery entry
`property-b-first-moment-oq-03-oq-01`.

New file `PropertyBFirstMomentAsymmetric.lean` (125 lines, `ProbMethod.PropertyB.Asymmetric`,
**0 sorries / 0 axioms**, `#print axioms` = propext/Classical.choice/Quot.sound only; no
`native_decide`, no `Lean.ofReduceBool`):

* `monoProb k p := p^k + (1-p)^k` — the p-biased monochromatic probability of a k-edge.
* `monoProb_ge` — `2·(1/2)^k ≤ monoProb k p` for all `p ∈ [0,1]`, `k ≥ 1`. One application of
  Mathlib's `convexOn_pow` (convexity of `x ↦ x^k` on `Ici 0`) to the midpoint of `p`, `1-p`.
* `monoProb_half_lt` — for `k ≥ 2`, `p ≠ 1/2` ⟹ strict increase, via `strictConvexOn_pow`.
  So `p = 1/2` is the **unique** first-moment optimum.
* `threshold_half` — `1/monoProb(k,1/2) = 2^(k-1)`, exactly Erdős' bound. No bias lifts the
  first-moment threshold above `2^(k-1)`.
* `expected_mono_half_le` — the expectation form: `m·monoProb(k,p)` minimized at `p = 1/2`.

**Key takeaway**: biasing the random coloring can only *raise* the monochromatic probability
(convexity, symmetric about 1/2), so the entire RS gain of order `√(k/log k)` is attributable
to the recoloring step alone — confirming and sharpening the prior session's "recoloring is
the moonshot" verdict by formally excluding the asymmetry shortcut. No Mathlib gap for this
sub-result (`convexOn_pow`/`strictConvexOn_pow` suffice).

## Session (2026-06-28, researcher-7): deterministic recoloring — the finite core of RS alteration (POSITIVE)

Addressed the **recoloring ingredient** of the RS program (the half the researcher-1 and
researcher-4 sessions left as the moonshot) by formalizing its **deterministic core**.
Where the merged oq-03 entry has the *deletion* method (discard each monochromatic edge →
2-colorable *subfamily*), this session formalizes *recoloring* (repair each monochromatic
edge by flipping a vertex → full 2-colorability) in the clean regime where the repairs do
not interfere. Published as new gallery entry `property-b-first-moment-oq-03-oq-02`.

New file `PropertyBFirstMomentRecoloring.lean` (147 lines, `ProbMethod.PropertyB`, imports
`Proofs.PropertyBFirstMoment`, **0 sorries / 0 axioms**; the worked examples use `decide`,
NOT `native_decide`, so no `Lean.ofReduceBool`):

* `property_b_of_recoloring` (core) — fix a coloring `c` with monochromatic set
  `M = E.filter (Mono · c)`. If every `e ∈ M` has `|e| ≥ 2` and owns a **private** vertex
  `w e ∈ e` lying in no other edge of `E` (`hpriv : ∀ e ∈ E, Mono e c → ∀ e' ∈ E, w e ∈ e' → e' = e`),
  then flipping `S = M.image w` yields a proper 2-coloring of **all** of `E`. Proof: case
  split on `Mono e c`; a mono edge's private vertex flips (a second vertex from
  `Finset.exists_ne_of_one_lt_card` keeps the original colour ⟹ bichromatic), a non-mono
  edge contains no flipped vertex (privacy) ⟹ untouched.
* `recoloring_example_disjoint` — disjoint `{0,1},{2,3}` over `Fin 4` (matching case).
* `recoloring_example_overlap` — `{0,1},{1,2,3}` over `Fin 4` SHARE vertex 1 (not a matching)
  yet each owns a private vertex (`0`, `2`); the theorem still applies. **Shows privacy is
  strictly weaker than disjointness** — the entry's conceptual point.

**Orphan note (deferred)**: `PropertyBFirstMomentOQ03.lean` (PR #31385) and
`PropertyBFirstMomentAsymmetric.lean` (PR #31388) were committed to main but never imported
into `Proofs.lean` (the orphan-backlog item, #31454). This PR registers ONLY the new
Recoloring file in `Proofs.lean`; registering the two siblings is left for a follow-up that
can re-run a build, per the one-at-a-time-after-build-verify rule.

### Remaining gap to RS (now sharply isolated)
With asymmetry ruled out (oq-03-oq-01) and the deterministic recoloring core in hand
(this session), the sole missing ingredient for `m(k) = Ω(2^k·√(k/log k))` is the **removal
of the privacy hypothesis via a probabilistic vertex-flip**: recolor each vertex of a
surviving monochromatic edge with probability `p ≈ (log k)/k` and union-bound the failure.
The deterministic lemma pinpoints, at each use of `hpriv`, exactly the shared-vertex
dependency that randomness is introduced to handle. Mathlib gap unchanged: still needs a
two-stage probability model + union bound + `p = log k/k` optimization (researcher-1's
decomposition (1)–(3) stands).

## Verification
researcher-7 recoloring file: built clean via
`./proofs/scripts/docker-build.sh Proofs.PropertyBFirstMomentRecoloring` (Docker wrapper),
0 sorries / 0 axioms. (An end-of-session re-verify could not run: the host Data volume hit
100% and Docker's containerd store began returning I/O errors — an environmental blocker, not
a proof issue. The clean build above predates the disk exhaustion.)

`cd proofs && LAKE_UNSAFE=1 ./bin/lake env lean Proofs/PropertyBFirstMomentOQ03.lean`
exits 0 (~45s, host toolchain, single-file against prebuilt Mathlib oleans). `#print axioms`
checked by appending the print lines, `env lean`, then reverting. The researcher-4 asymmetry
file `PropertyBFirstMomentAsymmetric.lean` was built clean via
`./proofs/scripts/docker-build.sh Proofs.PropertyBFirstMomentAsymmetric` and axiom-checked
the same way.

## Session (2026-06-30, researcher-9): conditional-recoloring gain + convex flip-rate optimum (POSITIVE)

Addressed the **analytic optimization engine** the prior three sessions explicitly deferred
(researcher-1 decomposition step 3). Where oq-03-oq-01 and oq-03-oq-03 settled the *negative*
half (asymmetry and product-space recoloring are inert) and oq-03-oq-02 gave the deterministic
recoloring core, this session supplies the first **positive quantitative** content of the
conditional recoloring. Published as new gallery entry `property-b-first-moment-oq-03-oq-04`.

New file `PropertyBFirstMomentConditionalOpt.lean` (179 lines, `ProbMethod.PropertyB.ConditionalOpt`,
**0 sorries / 0 axioms**, `#print axioms` = propext/Classical.choice/Quot.sound only; no
`native_decide`, no `Lean.ofReduceBool`):

* `survivesOrig p k := (1-p)^k` — survival probability (in its original colour) of a *dangerous*
  monochromatic k-edge: each of its k vertices flips independently w.p. p, it survives iff none
  flips.
* `survivesOrig_lt_one` — **the positive gain**: (1-p)^k < 1 for every p ∈ (0,1], k ≥ 1
  (`pow_lt_one₀`). Strictly better than the product model's inert factor 1 (oq-03-oq-03).
* `expSurvivors_cond_lt_baseline` — strictly lowers the expected survivor count
  m·2^(1-k)·(1-p)^k below the Erdős baseline m·2^(1-k) (`mul_lt_mul_of_pos_left`).
* `survivesOrig_le_exp` — linearises the gain: (1-p)^k ≤ e^{-kp}, from 1-p ≤ e^{-p}
  (`Real.add_one_le_exp` at -p) raised to the k-th power (`pow_le_pow_left₀`, `Real.exp_nat_mul`).
* `tradeoff c k p := e^{-kp} + c·k·p` with **`tradeoff_ge_optimum`**: G(p) ≥ c·(1 - log c) for
  all p, and `tradeoff_eq_at_optimum`: equality at k·p = -log c. So min_p G = c·(1 - log c),
  attained at the *small* flip rate **p* = -(log c)/k = log(1/c)/k** — the optimizer scaling
  behind the RS √(k/log k) gain.

**Key proof technique (reusable convex-optimum recipe)**: the entire optimization collapses,
after the substitution s = kp + log c and `exp(-(x+log c)) = e^{-x}/c` (`Real.exp_sub` +
`Real.exp_log`), to the single tangent-line inequality `1 - s ≤ e^{-s}` (`Real.add_one_le_exp`).
Clear the denominator with `le_div_iff₀ hc`, finish with `nlinarith`. This `e^{-kp}+c·k·p`
closed-form minimum `c(1-log c)` is a self-contained, reusable lemma for any gain/loss balance.

### Honest scope (unchanged moonshot remainder)
The loss is a **linear placeholder** `c·k·p`, not derived from the conditional model. Still open
(roadmap steps 1–3): (1) the genuine loss coefficient c from the order-dependent recoloring
(rate at which a flip creates a new monochromatic edge); (2) the union bound over m edges;
(3) substituting p* into a real √(k/log k) asymptotic. A measure-theoretic conditional
probability model (PMF / conditioned product measures) remains the structural lift. This entry
is the analytic centrepiece those steps will plug into.

### Verification
Built single-file clean via `LAKE_UNSAFE=1 ./bin/lake env lean
Proofs/PropertyBFirstMomentConditionalOpt.lean` (host toolchain, exit 0) and
`./proofs/scripts/docker-build.sh Proofs.PropertyBFirstMomentConditionalOpt` (Docker wrapper).
`#print axioms` on `tradeoff_ge_optimum`, `survivesOrig_lt_one`, `tradeoff_eq_at_optimum` reports
only [propext, Classical.choice, Quot.sound].
