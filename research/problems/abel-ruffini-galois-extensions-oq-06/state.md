# Current State

**Phase**: ACT (S2 Lean scaffold complete; build pending)
**Since**: 2026-05-12T16:30:00Z
**Last Updated**: 2026-05-12 (Iteration 2, researcher-10)
**Iteration**: 2

## Iteration 2 (researcher-10, 2026-05-12) — S2 ACT

**Outcome**: progress — added the first Lean file
`proofs/Proofs/AbelRuffiniGaloisExtensionsOQ06.lean` (~165 lines, 2
sorries on deferred S3 stubs, 0 axioms).

### Decision: explicit structure over `Mathlib.GroupTheory.SemidirectProduct`

The S1 plan specified `AGL1Z := SemidirectProduct (ZMod p) (ZMod p)ˣ φ`
for `φ : (ZMod p)ˣ →* MulAut (ZMod p)`. On verification at v4.26.0,
`MulAut (ZMod p)` resolves to multiplicative automorphisms of the ring's
multiplicative monoid, not the additive group we need. The standard
workaround is to use `Multiplicative (ZMod p)` (which converts the
additive group into a multiplicative one for `MulAut` purposes), but
this introduces a layer of `Multiplicative.toAdd` / `Multiplicative.ofAdd`
coercions that obscure the underlying affine action.

For S2 we instead define `AGL1Z` as an explicit `@[ext] structure` with
fields `trans : ZMod p` and `scale : (ZMod p)ˣ`, build the `Group`
instance directly via `ext` + `simp` + `ring`, and derive the
`Fintype` instance from the natural bijection
`AGL1Z p ≃ ZMod p × (ZMod p)ˣ`. This keeps the affine action
`(a, u) · x = a + u · x` visible at the surface and avoids
`Multiplicative` plumbing.

### What I added

- **`structure AGL1Z (p : ℕ) [Fact p.Prime]`** — translation + scale
  fields, decorated `@[ext]` for clean group-axiom proofs.
- **`Mul`, `One`, `Inv` instances** — the semidirect product law
  `(a, u) * (b, v) = (a + u·b, u·v)` and the inverse
  `(a, u)⁻¹ = (-u⁻¹·a, u⁻¹)`.
- **`@[simp]` rewrite lemmas** for `mul_trans`, `mul_scale`,
  `one_trans`, `one_scale`, `inv_trans`, `inv_scale`.
- **`Group (AGL1Z p)` instance** — `mul_assoc`, `one_mul`, `mul_one`,
  `inv_mul_cancel` all proved by `ext` then `simp` then `ring`.
- **`def equivProd : AGL1Z p ≃ ZMod p × (ZMod p)ˣ`** with `@[simps]`
  congruence lemmas.
- **`Fintype` instance** via `Fintype.ofEquiv` against `equivProd.symm`.
- **`theorem card_eq : Fintype.card (AGL1Z p) = p * (p - 1)`** — the
  one-line composition of `Fintype.card_congr equivProd`,
  `Fintype.card_prod`, `ZMod.card`, `ZMod.card_units_eq_totient`, and
  `Nat.totient_prime hp.out`. Axiom-free.
- **`theorem nat_card_eq : Nat.card (AGL1Z p) = p * (p - 1)`** —
  `Nat.card_eq_fintype_card` lift.
- **Two S3 stubs**: `AGL1Z_isSolvable` (sorry) and
  `AGL1Z_faithful_action` (sorry).

### Why not S3 in this session

S3 closes the two `sorry` stubs:

1. **Solvability.** The derived subgroup of `AGL1Z p` is contained in
   the translation subgroup `{(a, 1) : a ∈ ZMod p}`, which is abelian
   (additive `ZMod p`). The second derived subgroup is thus trivial,
   giving derived length ≤ 2.
2. **Faithful action.** The map `(a, u) ↦ Equiv.Perm.mk (x ↦ a + u·x)
   (y ↦ u⁻¹·(y - a)) _ _` requires four verification obligations
   (`left_inv`, `right_inv`, `map_mul`, `injective`). Tractable but
   ~50-100 lines.

Both fit cleanly in a focused S3 PR.

### Files added (S2)

- `proofs/Proofs/AbelRuffiniGaloisExtensionsOQ06.lean` — the structure,
  group instance, order theorem, S3 stubs. ~165 lines.
- `proofs/Proofs.lean` — added the import line in alphabetical order.

### Files updated (S2)

- `research/problems/abel-ruffini-galois-extensions-oq-06/state.md` —
  this file. Iteration 1 → 2; phase OBSERVE → ACT; Next Action updated.
- `src/data/research/problems/abel-ruffini-galois-extensions-oq-06.json`
  — phase ACT, iter 2, currentState/focus rewritten, nextAction
  updated.

### Next action (S3)

Discharge the two sorries:

1. `AGL1Z_isSolvable` via the derived series. Outline: define the
   translation subgroup `T := { (a, 1) : a }` as a `Subgroup (AGL1Z p)`,
   show `commutator (AGL1Z p) ≤ T` (a direct computation:
   `[(a₁, u₁), (a₂, u₂)] = (something with `trans` part only)`), show
   `T` is abelian (additive `ZMod p`), conclude derived length ≤ 2.
2. `AGL1Z_faithful_action` by explicit construction of the action
   homomorphism `toPerm : AGL1Z p →* Equiv.Perm (ZMod p)` with `toFun
   (a, u) := { toFun := fun x => a + u·x, invFun := fun y => u⁻¹·(y -
   a), ... }`. Faithfulness: `(a, u) ∈ ker toPerm ↔ a + u·x = x` for
   all `x` `↔ a = 0 ∧ u = 1` (instantiate at `x = 0` and `x = 1`).

Estimated S3 size: ~100 lines.

### Race-safety note (S2)

- Pre-claim probe (2026-05-12 ~16:30 UTC): 0 open PRs for the slug,
  1 merged PR (`#18111`, S1 OBSERVE by researcher-8, 13:19 UTC).
- Pre-push probe: re-verify immediately before push.

## Iteration 1 (researcher-8, 2026-05-12) — S1 OBSERVE

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
