# Erdős Problem 85 at the Exact Boundary: a Machine-Collaborative Campaign
## Working draft — verdict-independent sections only

**Status**: DRAFT (Fable drafts, Sol audits — operator directives 1729/1810).
The headline theorem section (§8) and its interpretation are STUBBED until
the remaining certificate drop is complete and cold-audited. Nothing in
this document is for external distribution before operator read-through
(mandate 1318).

Authors/roles: two AI collaborators ("Fable", "Sol") working as adversarial
peers in a shared persistent chat room, with a human operator supplying
compute policy, priorities, and final review. All mathematics is
machine-checked in Lean 4 (v4.31.0, pinned mathlib) or certified by
DRAT-verified SAT certificates stored on a durable volume.

---

## 1. Verification asymmetry

The campaign's engine is the asymmetry between *proposing* mathematics and
*verifying* it. Both collaborators propose freely — conjectures, census
kills, structural identities — and both are wrong at a substantial rate
(documented misfires include the |o| ≡ 3 (mod 5) congruence, an inverted
quota direction, a C7-block nonexistence claim refuted by an explicit
{i,i+1} circulant, and a "(4,4,4,4) DEAD" claim corrected within the hour
by its own author; room msgs 1808/1818). The system tolerates this error
rate because nothing enters the record until it passes one of two
verifiers: cold elaboration under the pinned Lean toolchain, or DRAT
replay of a SAT certificate onto the durable volume. The asymmetry is
what makes high-variance proposing *safe*: bold wrong ideas cost hours,
never correctness.

The featured case study is the rg-mask incident (msgs 1767–1773): after
the two-layer branch was declared closed, the independent verbatim
`#print axioms` audit FAILED — the pushed file did not elaborate under the
repo-pinned toolchain at all. Ten error sites (nonexistent mathlib
constants, name drift, parser-scope bugs) sat inside the critical
terminal wrappers. Root cause: the author's check pipeline filtered
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
additionally inherits exactly nine named `native_decide` certificate
axioms (factorizationRangeOTT_block1–4, normCertificateRangeOTT_block1–5)
from the s=4 terminal — disclosed here and in the gallery metadata per
the project's axiom-integrity policy, which treats `Lean.ofReduceBool`
as a countable assumption, not a technicality. SAT verdicts are scoped
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
read-through). No mathematical step in the campaign originated from the
operator; every mathematical step passed through machine verification.
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

1. **f(48) = 8 descent rung and the strict gap** s(s−1)+4 ≤ d
   (unconditional; wrapper pending at time of writing).
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

## 8. Headline theorem — STUB

[Reserved pending the s=0 closure and the final drop certification:
statement, axiom audit, and interpretation. Per mandate 1318, this
section is written only after the seventh survivor verdict lands and the
freeze/tag + LRAT replay + hash verification complete.]
