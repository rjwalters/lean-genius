# Current State

**Phase**: OBSERVE (S1 scaffold complete; no Lean changes yet)
**Since**: 2026-05-12T11:55:00Z
**Last Updated**: 2026-05-12 (Iteration 1, researcher-8)
**Iteration**: 1

## Iteration 1 (researcher-8, 2026-05-12) — S1 OBSERVE

**Outcome**: scaffold — created `problem.md`, `knowledge.md`,
`state.md`, and `src/data/research/problems/abel-ruffini-galois-extensions-oq-06.json`.
No Lean changes.

### What I added

Doc-only scaffolding for a fresh tier-B slug. The deliverable is:

- A precise framing of "primitive solvable permutation groups of prime
  degree" as Galois's classification: the only such groups are the
  affine groups $\mathrm{AGL}(1, p) = \mathbb{Z}/p\mathbb{Z} \rtimes
  (\mathbb{Z}/p\mathbb{Z})^\times$ of order $p(p-1)$.
- A tractability triage distinguishing the **forward direction**
  (define AGL, prove solvability + primitivity — feasible in 3-4
  sessions) from the **Galois direction** (every primitive solvable
  subgroup of $S_p$ embeds into AGL — requires substantial new
  Mathlib infrastructure for primitive-permutation-group structure
  theorems, possibly split into a sub-OQ).
- A survey of the Mathlib surface (`SemidirectProduct`, `IsSolvable`,
  `MulAction.IsPrimitive`, `Sylow`, `Equiv.Perm.cycleType`) and the
  parent / sibling reuse opportunities (OQ-04 Jordan-Hölder pattern;
  OQ-07 Burnside Sylow patterns).
- A concrete S2 plan: build
  `proofs/Proofs/AbelRuffiniGaloisExtensionsOQ06.lean`, define
  `affineHom : (ZMod p)ˣ →* MulAut (ZMod p)`,
  `AGL1Z (p : ℕ) [Fact p.Prime] := SemidirectProduct (ZMod p) (ZMod p)ˣ (affineHom p)`,
  and the order calculation $|\mathrm{AGL}(1, p)| = p(p-1)$.
  Defer solvability + faithfulness to S3 and primitivity to S4.

### Why not S2 in this session

S2 ORIENT requires verifying Mathlib's `SemidirectProduct` /
`IsPrimitive` API at the pinned v4.26.0 rev and choosing whether to
parameterize via Mathlib's `SemidirectProduct` (more general) or via an
explicit `prod` structure (more concrete). That decision is best made
as a focused S2 PR rather than bundled with the OBSERVE scaffold.
Additionally, this OQ has a *forward* / *Galois* split that should be
made explicit in the S2 plan — possibly via sub-OQ creation for the
Galois direction.

### Files added (S1)

- `research/problems/abel-ruffini-galois-extensions-oq-06/problem.md` —
  problem description with tractability triage, references (Galois
  1832, Rotman, Robinson, Cameron, Wielandt), and parent / sibling
  linkage
- `research/problems/abel-ruffini-galois-extensions-oq-06/knowledge.md` —
  Mathlib surface inventory, feasibility table, S2 plan, risk register
- `research/problems/abel-ruffini-galois-extensions-oq-06/state.md` —
  this file
- `src/data/research/problems/abel-ruffini-galois-extensions-oq-06.json` —
  phase OBSERVE, iter 1, references, knowledge surface

### Next action (S2 ORIENT)

Create `proofs/Proofs/AbelRuffiniGaloisExtensionsOQ06.lean` with:

1. Imports: parent + `Mathlib.GroupTheory.SemidirectProduct` +
   `Mathlib.GroupTheory.GroupAction.Basic`. (+ `.Primitive` if it
   exists at v4.26.0.)
2. `def affineHom (p : ℕ) [Fact p.Prime] : (ZMod p)ˣ →* MulAut (ZMod p)`
   sending `u ↦ MulAut.conj (multiplicationByU u)` or the appropriate
   `MulAut.toEquiv` form. The key is that `(ZMod p)ˣ` acts on the
   additive group `ZMod p` by multiplication.
3. `def AGL1Z (p : ℕ) [Fact p.Prime] := SemidirectProduct (ZMod p) (ZMod p)ˣ (affineHom p)`.
4. `theorem AGL1Z_card : Nat.card (AGL1Z p) = p * (p - 1)` — one-line
   via `Nat.card_semidirectProduct` (or unroll `Fintype.card_prod` if
   the semidirect product's Fintype instance gives a product structure
   on the underlying set).
5. `def AGL1Z.toPerm : AGL1Z p →* Equiv.Perm (ZMod p)` — the natural
   permutation action $(a, u) \cdot x = a + u \cdot x$.
6. Stubs (sorried for S3) for `IsSolvable (AGL1Z p)` and
   `Function.Injective (AGL1Z.toPerm)`.

Estimated S2 ACT size: ~80 lines, 0 sorries on the definitions and
order calculation, 2 sorries on the S3 stubs.

### Blockers

None for the forward direction (S2-S4). The Galois direction (S5+)
will require:

- Either a substantial new infrastructure block in Lean (primitive
  permutation group structure theorem, ~300-500 lines), OR
- Splitting OQ-06 into `abel-ruffini-galois-extensions-oq-06` (forward
  direction, this slug) and a new sub-OQ
  `abel-ruffini-galois-extensions-oq-06-galois-direction`.

Decision deferred to S5 once the forward direction is in place.

### Race-safety note

This slug was added by the seeker on 2026-05-12T09:56:28Z. As of S1
submission, 0 open PRs, 0 remote branches, 0 prior research/problems
artifacts. The race window for fresh tier-B slugs is 5-30 minutes per
memory pattern; this S1 was written outside that window for the
seeker-add event, but may still race with parallel S1 sessions on the
same slug. Pre-push probe will re-verify immediately before push.
