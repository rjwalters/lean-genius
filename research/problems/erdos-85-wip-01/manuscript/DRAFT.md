# Erdős Problem 85 at the Exact Boundary: a Machine-Collaborative Campaign
## Working draft — verdict-independent sections only

**Status**: DRAFT (Fable drafts, Sol audits — operator directives 1729/1810).
The headline theorem section (§8) and its interpretation are STUBBED until
the remaining certificate drop is complete and cold-audited. Nothing in
this document is for external distribution before operator read-through
(mandate 1318).

Authors/roles: two AI collaborators — **Fable** (runtime identity
`claude`; Anthropic Claude) and **Sol** (runtime identity `codex`;
OpenAI Codex) — working as adversarial peers in a shared persistent chat
room, with a human operator supplying compute policy, priorities, and
final review. Fable/Sol are the established public names from the
published transcript and cross-reference to the runtime identities in
the room log and git history. All mathematics is machine-checked in
Lean 4 (v4.31.0, pinned mathlib) or certified by DRAT-verified SAT
certificates stored on a durable volume.

---

## 1. Verification asymmetry

The campaign's engine is the asymmetry between *proposing* mathematics and
*verifying* it. Both collaborators propose freely — conjectures, census
kills, structural identities — and both produced documented wrong
conjectures (misfires include the |o| ≡ 3 (mod 5) congruence, an inverted
quota direction, a C7-block nonexistence claim refuted by an explicit
{i,i+1} circulant, and a "(4,4,4,4) DEAD" claim corrected within the hour
by its own author; room msgs 1808/1818). The system tolerates these
errors because nothing enters the record until it passes one of two
verifiers: cold elaboration under the pinned Lean toolchain, or DRAT
replay of a SAT certificate onto the durable volume — and because
intermediate tooling is itself subject to adversarial audit before its
outputs become evidence (see the domain-truncation incident below). The asymmetry is
what makes high-variance proposing *safe*: bold wrong ideas cost hours,
never correctness.

The featured case study is the rg-mask incident (msgs 1767–1773): after
the two-layer branch was declared closed, the independent verbatim
`#print axioms` audit FAILED — the pushed file did not elaborate under the
repo-pinned toolchain at all. At least ten source failures across four
classes (nonexistent mathlib constants, wrong disjointness names,
parser-scope bugs in large sums, a case-substitution error) sat inside
the critical terminal wrappers. Root cause: the author's check pipeline filtered
elaboration output through `rg`, and empty filtered output had been
misread as success. The mathematics was sound; the *verification claim*
was not. The repair took under an hour, the re-audit passed
([propext, Classical.choice, Quot.sound] only), and the closure claim was
retracted and restored in the same evening — with the independent-cold-
audit rule upgraded from convention to hard gate. A system that cannot
distinguish "the proof is right" from "the checker said yes" will
eventually publish the difference.

## 2. Adversarial diversity

Two models with different failure modes red-team each other in-room
before anything is formalized. The record shows the pattern working in
both directions: Sol caught Fable's quota-direction flip and supplied the
correct forward-divisibility route; Fable caught the residual-sector
contact term that closed n7/count9 after Sol's slack-4 analysis stalled
(msgs 1739–1747), and the audit gate caught the toolchain drift. Neither
agent audits its own claims as the system of record. The room protocol
enforces this socially: every substantive claim is posted with its
derivation sketch, and the counterpart's PASS/refutation is logged before
the Lean wrapper is written. Where both agents agreed and both were wrong
(the stale-cache incident that produced two false transport-parity
kernels), the cold-elaboration gate caught it instead — diversity plus a
mechanical verifier, not diversity alone.

The second featured case study is the domain-truncation incident
(msgs 1925–1929). Fable's constraint model for a solution-space
enumeration encoded a modular inequality on an integer lift with domain
[−11, 11] when the true lift ranges over [−22, 22] — a silent
truncation that produced a confidently wrong census (1,294 solutions,
63 symmetry orbits, all internally consistent, all passing Fable's own
validators). Sol's independent audit did not re-run the enumeration; it
checked a property the artifact should have had — closure of the
solution set under the claimed symmetry group — found a violation,
and produced a concrete valid solution missing from the record. The
corrected enumeration overflowed a 100,000-solution cap: the bug had
hidden more than 98% of the space, and the strategy built on the small
census was retired the same hour, before any fleet compute or
certificate claim consumed it. The lesson generalizes: validators
written by the same mind that wrote the generator inherit its blind
spots; independent audits should test invariants the generator never
considered.

The third case study is a single afternoon's cascade (msgs 2299–2328)
that shows the correction loop running at full speed in both
directions. A scouting pass over the formal file found an unconsumed
generic engine and sixty-two unconsumed arithmetic ledgers, all
instantiating one unstated law; formalizing the law's per-row version
took an hour and immediately strengthened the mechanical census — which
then killed five surviving cases, including, apparently, the very case
class two hundred solver-hours were grinding on. Twice in the next hour
the strengthening itself was red-teamed down: first a self-adjacency
term had been misattributed to the orphan ledger (the census was rerun
with the corrected budget), then the self-term's value was found to be
a two-valued dichotomy rather than a constant (the census was rerun
again, sector-split). Each correction shrank the claimed kill list —
from twelve, to seven, to three unconditional deaths — and the fourth
correction reopened even the central class kill: the self-adjacency
value, assumed two-valued from an odd-order theorem that did not apply
to the even-order components at hand, admits a third value that
exactly balances the identity, so the case class whose solver fleet
had been stopped turned out to be alive after all and the fleet's
target question reverted to open. A fifth revision closed the reopened hole
with a genuinely new finite obstruction — and a sixth reopened the
question once more from a different flank, when the aggregation work
revealed that every version of the strengthened census, and the
class-closure wrapper built on it, had silently assumed that
excess between the labeled components themselves vanishes, an
assumption the per-vertex degree budget flatly permits violating.
The formal theorems all survive — what fell, each time, was the claim
that their hypotheses describe every real configuration. Nothing was
retracted publicly because nothing overstated had been published:
each version's scope was stated conditionally, operational action was
gated on the audits, and the solver artifacts — certificates, exact
CNFs, manifests — had been kept durable precisely so that a reversed
conclusion costs a relaunch, not a reconstruction. The pattern to
notice is that the errors were found by the collaborators attacking
their own results within minutes of stating them — the census re-runs
cost seconds, the Lean re-checks minutes — so the cost of being wrong
in-channel stayed negligible while the cost of being wrong in public
would have been paid six times.

## 3. The structure–compute exchange rate

The campaign continuously trades structural insight against raw solving.
Documented exchange points:

- The h=1 49-lab SAT family: the v2 "defect ledger" encoding (derived
  analytically from exact product-counting identities) beat the base
  encoding 4692s → 972s like-for-like (4.8×) with 3–6× smaller proofs —
  a derivation-first speedup measured, not assumed.
- The d=16 s=4 branch: a SAT-feasible (12⁴) witness localized the
  obstruction that analysis then killed exactly (owner-bin collision),
  closing the branch as one cold-verified theorem.
- The s=2 branch: closed entirely analytically (orphan census, owner
  concentration, budget/excess pricing) after early SAT scouting showed
  the space was structured; total SAT time on the branch: zero.
- The zero-layer campaign (current): the H² = 12I + J − S − D identity
  compresses the 192-vertex orphan core to a 48-vertex point graph M;
  spectral necessary conditions were then shown *satisfiable* by explicit
  Cayley constructions (λ₂ = 3.25 < 5), proving the compression is a
  filter, not a terminal — and redirecting effort to the H-lift before
  any large SAT run was launched.

- The counterpoint that calibrates the rule: injecting an *implied* unit
  (a phase value already forced by gauge and row-distinctness) into a
  cube produced state-for-state identical solver traces — the solver's
  own parse-time propagation had already internalized it. Derived facts
  inside the solver's propagation horizon are free; only structure
  beyond that horizon (like the defect ledger) buys speed. The A/B was
  run deliberately, twin against parent, before the technique was
  adopted — and it was rejected on the evidence.

The exchange rate is asymmetric in an instructive way: an hour of exact
derivation has repeatedly saved days of solver time, while solver output
(witnesses, UNSAT cores) has repeatedly told the derivation where to dig.

## 4. Persistence and the shape of a long campaign

The campaign persists through context loss, machine reclamation, and
session restarts because its state lives outside any one context: the
room transcript (the argument of record), the git branches (the
mathematics of record), the durable volume (the certificates of record),
and memory checkpoints (the operational lessons). Spot-instance
reclamations destroyed worker fleets four times; the resumable
per-verdict queue design meant every restart lost only in-flight solves.
The rule that certificates only count once on the durable volume (rule 3)
was enforced even when it cost ~8h of recompute after a disk purge — the
alternative (trusting artifacts that exist only on a spot instance) is a
verification claim without a verifier.

## 5. Honest scoping

Every claim in this document is scoped to what its verifier actually
checked. The two-layer closure depends on foundational axioms only
([propext, Classical.choice, Quot.sound], audited twice independently).
The combined boundary reduction `degree_sixteen_remaining_zeroLayer`
additionally inherits exactly nine per-block axioms of the form
`<name>._native.native_decide.ax_1_1` (factorizationRangeOTT_block1–4,
normCertificateRangeOTT_block1–5), as listed verbatim by
`#print axioms` — the compiler-trust axioms that `native_decide`
generates for the s=4 terminal's computational certificates. They are
disclosed here and in the gallery metadata per the project's
axiom-integrity policy, which counts native-code trust as an assumption,
not a technicality. SAT verdicts are scoped
to their encodings: the byte-exact equivalence proof between the
generalized A-profile encoder and the audited BBBB encoder (clause-set
SHA1 identity on the overlap family) is what licenses treating fleet
verdicts as verdicts about the mathematical objects. Scout-lane results
(proofs-off portfolio runs) are never merged into the certified ledger.

## 6. The thin human role

The operator's interventions are few and load-bearing: compute policy
(volume sizes, fleet topology, spot budgets), priority calls (the
mandate ordering derivation → A/B → cube-and-conquer → SAT lanes; the
manuscript start), and the external gate (nothing publishes before human
read-through). The operator's recorded role in this campaign was
primarily operational — compute policy, prioritization, and external
review; every mathematical step in the record passed through machine
verification.
The interesting datum for the working-model argument is not that the
human role is small — it is that the campaign's correctness never
depended on it being large.

## 7. Why Erdős problems

Erdős boundary problems are ideal stress tests for machine-collaborative
mathematics: statements are elementary, the search spaces are enormous,
partial progress is precisely certifiable (exact values, descent rungs,
branch closures), and the literature furnishes sharp targets. Problem 85's
exact even boundary d(d−1)+3 offered a descent tower whose rungs are
individually machine-checkable theorems — a shape that rewards exactly
the propose/verify/persist loop described above.

---

## Silence is not success (a recurring failure class)

Three operationally distinct incidents in this campaign turn out to be
one failure: a checker whose silence was read as approval. In the
rg-mask incident, elaboration output was filtered through a pattern
matcher and an empty result — which also occurs when elaboration never
ran — was recorded as a pass. In the vacuous-gate incident, a
virtualization restart interrupted a build between deleting an old
compiled artifact and writing its replacement; the build system's
freshness metadata survived the interruption, so every subsequent
"verification" trusted the stale record and skipped the changed file
entirely — reporting thousands of successful jobs while elaborating
none of the mathematics under test, for a full day, across both
collaborators' gates. In the watcher-poll incident, a monitoring
query that failed under database contention returned an empty result
that the polling loop treated as "no news," blinding one collaborator
to three hours of the other's messages. In each case the fix is the
same shape: a checker must produce a positive artifact of having
checked — an olean newer than its source, a nonempty match on a
sentinel that must be present, a poll that distinguishes "no new
items" from "query failed" — and the absence of that artifact must be
treated as failure. The certification pipeline now enforces this
mechanically: gates run against ephemeral build state, verify the
target artifact's existence and freshness after the build, and void
any run whose window overlaps an engine restart.

## Methods (summary)

- **Room protocol**: persistent SQLite chat; claim → red-team → formalize
  → relay-merge → independent cold audit. Relay cadence: every push to
  the working branch is merged to the mirror branch by the counterpart.
- **Cold-audit rule**: "verified" means the file elaborates from source
  under the pinned toolchain (v4.31.0 + pinned mathlib) in an
  independent environment, unfiltered, with verbatim `#print axioms` on
  the public theorems. Adopted after the stale-cache incident; upgraded
  after the rg-mask incident.
- **Certificate factory**: pysat encoders with SHA1-tagged instances;
  kissat/cadical portfolios; DRAT verification; gzip + manifest on the
  durable volume; resumable per-verdict queues; janitor processes and
  200G root volumes after the deleted-open-file post-mortem (msg 1807).
- **Census tooling**: exhaustive B&B sweeps over partition/atom spaces
  with every constraint tied to a named Lean lemma (loads, budgets,
  balance integrality, the equal-LCM law, oriented-cover kernels).

## Completed unconditional results (as of this draft)

1. **f(48) = 8 descent rung and the strict gap** s(s−1)+4 ≤ d — core
   theorems and certificates verified; the top-level Lean wrapper
   assembling them is pending at time of writing, so this is labeled
   certificate-verified, not fully formalized.
2. **d=16, s=4 branch closed**: `false_of_degree_sixteen_fourLayer` —
   census 36/36 partitions, eliminations 36/36, single dispatcher.
3. **d=16, s=2 branch closed**: `false_of_degree_sixteen_twoLayer` —
   orphan alphabet reduction, owner concentration, count census kills
   (counts 2,3,4,7,12,14,19,24), count9 residual-contact terminal,
   count8 three-config pricing; axioms: foundational only.
4. **Boundary reduction**: `degree_sixteen_remaining_zeroLayer` — the
   exact d=16 boundary now has s=0 as its only open branch (axioms:
   foundational + 9 disclosed certificate axioms).
5. **Zero-layer structural package** (in progress, all cold-verified):
   D1–D3 design lemmas, exact load-12, Gram = 12I + M, tripartite M,
   oriented-cover kernels, equal-LCM law, A-atom elimination, cherry
   bounds; census: 57 partitions dead by arithmetic (formal engines
   named), survivor map under active reduction.
6. **Graph-facing partition deaths** (each a certified theorem, all
   foundational-pure): {8,2⁴}, {5,5,2³}, {12,2,2}, {10,2,2,2} (via the
   minimum-even-orphan parity interface after the residual census was
   *refuted* by formal countermodel — see §4), and {12,4} — the last
   closed by a new pipeline: equal-order quotient-3 phase rigidity
   (ambient commutator ⇒ circulant), Sidon-from-C4, class exclusions
   (defect ±1, child-cover mod 3), and a kernel-`decide` finite endpoint
   (no 3-set in Z₁₂ has ordered difference set {2,4,5,7,8,10}).

### The antipodal law and the collapse of s=0 (in progress)

The campaign's endgame arrived not as a bigger census but as a single
structural invariant. Every component of the second-order defect
structure is a labeled cycle; for a cycle of even order n, the
*antipodal* pairs (v, v + n/2) are never defect-adjacent, so the
exactly-one-common law applies to them with no escape — adjacency does
not exempt a pair from needing a third-vertex witness (an early
"antipodal matching" escape proposed in-room was refuted within the
hour by the global form of the law: a reminder that the red-team
discipline cuts both ways).

The invariant: a Chebyshev-style intertwiner identity forces
*antipodal covariance* on any block between labeled cycles — a witness
row for both antipodes at position x forces a second witness row at
x + n/2 — so a witness component of order r can see an antipodal pair
of a component of order 2h only if r divides h (formally:
`component_antipodal_commonSource_forces_order_dvd`, proved with no
affine or phase assumptions, uniformly over equal, larger, smaller,
and intra-component witnesses, any quotient). The only structures that
pass the filter are even-fiber covers — and the child component c₀ is
the unique mod-3 cover in the zero-layer economy, which orphans by
definition never touch.

Consequence: every orphan atom needs a leg with 2k | m, and the eight
remaining zero-layer partitions all fail the resulting economy filter —
five have no admissible atoms at all, three die by a single linear
combination of load equations (integer Farkas certificates, verified
independently of the solver that found them). The dual-track texture is
worth recording: {8,8} was killed twice in one afternoon, once by an
offset-tiling obstruction that reduced to a displacement-sum invariant
Σ 2sᵢ ≡ 2 mod 8 (a one-line `Equiv.sum_comp` argument replacing a
12-case finite enumeration), and once by the antipodal filter — two
independent proofs, both foundational-pure, neither trusting a solver.

## 8. Headline theorem — STUB

[Reserved pending the s=0 closure and the final drop certification:
statement, axiom audit, and interpretation. Per mandate 1318, this
section is written only after the seventh survivor verdict lands and the
freeze/tag + LRAT replay + hash verification complete.]
