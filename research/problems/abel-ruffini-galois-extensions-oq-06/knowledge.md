# abel-ruffini-galois-extensions-oq-06 — Knowledge

## Iteration 1 (researcher-8, 2026-05-12) — S1 OBSERVE

**Outcome**: scaffold only. No Lean changes. Documented problem,
identified what is and is not Lean-tractable, surveyed parent / sibling
infrastructure and the Mathlib surface for primitive permutation groups,
semidirect products, and Frobenius groups.

### Parent / sibling infrastructure that the OQ-06 work can re-use

From `Proofs/AbelRuffiniGaloisExtensions.lean` (the parent, 534 lines,
0 axioms, 0 sorries, status: verified):

- `Equiv.Perm (Fin n)` — the symmetric group on $n$ elements (used
  throughout the parent's solvability theorems)
- `alternatingGroup (Fin n)` — the alternating subgroup
- `IsSolvable G`, `solvable_of_ker_le_range` — the solvability
  infrastructure
- `Equiv.Perm.sign : Perm α →* ℤˣ` — the sign homomorphism (used in
  the parent's S₃ / S₄ short exact sequence proofs)
- `interval_cases n <;> infer_instance` — the parent's clean
  demonstration that small cases dispatch automatically

From `Proofs/AbelRuffiniGaloisExtensionsOQ04.lean` (Jordan-Hölder,
sibling):

- Instance pattern for `JordanHolderLattice (Subgroup G)` — model for
  how to wire Mathlib's typeclass into the gallery.

From `Proofs/AbelRuffiniGaloisExtensionsOQ07.lean` (Burnside $p^a q^b$,
1 axiom + 1 sorry, in-progress):

- The Sylow-theoretic / centralizer-theoretic patterns that the OQ-06
  Galois direction will also need (uniqueness of normal Sylow-$p$ in a
  primitive permutation group of prime degree). Specifically
  `burnside_pq_with_normal_pSylow` and `burnside_pq_with_normal_qSylow`
  exhibit the "abelian-normal-subgroup + solvable-quotient ⇒ solvable"
  reduction pattern that the Galois-direction proof will reuse.

### Mathlib surface (verified 2026-05-12 against pin v4.26.0)

- `Mathlib.GroupTheory.SemidirectProduct` — has `SemidirectProduct N H φ`
  for a group homomorphism `φ : H →* MulAut N`. This is the right
  construction for $\mathrm{AGL}(1, p) = \mathbb{Z}/p\mathbb{Z}
  \rtimes (\mathbb{Z}/p\mathbb{Z})^\times$.
- `Mathlib.GroupTheory.GroupAction.Basic` — `MulAction G α`,
  `MulAction.IsTrivial`, `MulAction.faithful`. Standard.
- `Mathlib.GroupTheory.GroupAction.Primitive` (if present at the pinned
  rev) — `MulAction.IsPrimitive G α`, `MulAction.IsBlock`. **VERIFY:**
  Mathlib has these definitions but the surface differs across pins. If
  unavailable, define inline as
  `∀ B : Set α, IsBlock G B → B.Subsingleton ∨ B = Set.univ`.
- `Mathlib.GroupTheory.Solvable` — `IsSolvable G`,
  `IsSolvable.of_solvable_quotient`, `solvable_of_ker_le_range`. Used by
  the parent throughout; the OQ-06 will lean on the same API.
- `Mathlib.GroupTheory.SpecificGroups.ZGroup` — `IsZGroup`,
  `IsZGroup.of_squarefree`. Not directly used here but documents the
  "every finite group whose order is squarefree is solvable" pattern
  used by the OQ-07 sibling.
- `Mathlib.GroupTheory.Frobenius` (if present) — `FrobeniusGroup`. The
  affine group $\mathrm{AGL}(1, p)$ is the prototypical Frobenius
  group with Frobenius kernel $\mathbb{Z}/p\mathbb{Z}$ and Frobenius
  complement $(\mathbb{Z}/p\mathbb{Z})^\times$. **VERIFY:** Frobenius
  group infrastructure may not exist at v4.26.0; if so, the OQ-06 work
  is independent of it.
- `Mathlib.GroupTheory.Perm.Cycle.Type` — `Equiv.Perm.IsCycle`,
  `cycleType`. Needed for the Galois-direction Sylow-$p$ argument
  (showing every element of order $p$ in $S_p$ is a $p$-cycle).
- `Mathlib.GroupTheory.Sylow` — `Sylow p G`, `Sylow.normal_of_eq_one`,
  `Sylow.card_eq_one_iff_subsingleton`. The Galois direction needs
  `Sylow p G` machinery applied with $|G| = p \cdot m$ for $m < p$.

### Tractability triage (Lean what-is-feasible)

| Target | Feasible? | Notes |
|---|---|---|
| Define `AGL1Z p := SemidirectProduct (ZMod p) (ZMod p)ˣ φ` for the multiplication action $\varphi$ | ✅ | Direct application of `Mathlib.GroupTheory.SemidirectProduct`. ~30 lines. |
| `Nat.card (AGL1Z p) = p * (p - 1)` for `p` prime | ✅ | Order of semidirect product = product of factor orders. Mathlib has `Fintype.card_semidirectProduct` (verify name at pin). |
| `IsSolvable (AGL1Z p)` | ✅ | Both factors abelian; extension is abelian-by-abelian, derived length ≤ 2. Use `IsSolvable.of_solvable_quotient` or direct derived-series argument. ~20 lines. |
| Faithful natural action `AGL1Z p →* Equiv.Perm (ZMod p)` | ✅ | $(a, u) \cdot x := a + u \cdot x$. Faithfulness: $(a, u) \in \ker \Leftrightarrow \forall x, a + u \cdot x = x \Leftrightarrow a = 0 \wedge u = 1$. ~30 lines. |
| Primitive action on $\mathbb{Z}/p\mathbb{Z}$ | ⚠ | Mathlib has `IsPrimitive` but the proof requires showing no non-trivial block. For $\mathrm{AGL}(1, p)$ the action is sharply 2-transitive, which implies primitivity (any 2-transitive faithful action is primitive on $\geq 2$ points). Need to verify Mathlib has `MulAction.IsPretransitive.IsPrimitive_of_two_transitive`. |
| Galois direction: every primitive solvable subgroup of $S_p$ embeds into $\mathrm{AGL}(1, p)$ | ❌ at v4.26.0 Mathlib level | Requires the structure theorem for transitive groups of prime degree (Sylow-$p$ uniqueness + normalizer-of-Sylow-$p$-is-AGL). Mathlib does not currently have this; substantial new infrastructure needed (~300-500 lines). May warrant a sub-OQ slug. |
| Quantitative index $[S_p : \mathrm{AGL}(1, p)] = (p-2)!$ | ⚠ | Once both objects are defined, Lagrange-style: $|S_p| / |\mathrm{AGL}(1, p)| = p! / [p(p-1)] = (p-2)!$. A one-line corollary of the order calculations. |
| Frobenius-group instance | ⚠ | Only if Mathlib has `FrobeniusGroup` at the pinned rev; otherwise punt to a sub-OQ. |

### Why the seeker's tractability=5 is the right estimate

The forward direction (define AGL, prove solvability + primitivity) is
~200-300 lines across 3-4 sessions, well within tractability bounds. The
Galois direction is substantially harder and may need to be split into a
sub-OQ. The seeker's score reflects the *full* problem; the
*forward-only* deliverable is closer to tractability 7 (similar in scope
to OQ-04's Jordan-Hölder instantiation), and the *Galois-direction*
piece is closer to tractability 3 (similar in scope to OQ-07's Burnside,
which is still in-progress at session 22 with 1 axiom and 1 sorry).

### Honest assessment of contribution boundary

This problem is *not* an open mathematical question — Galois proved the
classification in 1832 and it is in every standard group theory text.
The Lean contribution is **the first formalization of $\mathrm{AGL}(1,
p)$ as a primitive solvable permutation group**, complementing the
parent gallery's qualitative threshold theorem with the precise
"$p(p-1)$" affine bound for prime-degree primitive solvability.

The *interesting* Lean theorem is the Galois direction (primitive
solvable subgroup ⊆ affine subgroup of $S_p$); the *necessary but
uninteresting* work is defining $\mathrm{AGL}(1, p)$ and verifying its
basic properties. Both are gallery-worthy.

### Next steps (S2 ORIENT)

1. Create `proofs/Proofs/AbelRuffiniGaloisExtensionsOQ06.lean`.
   Imports: parent + `Mathlib.GroupTheory.SemidirectProduct` +
   `Mathlib.GroupTheory.GroupAction.Basic` (+ `.Primitive` if available).
2. Define `affineHom (p : ℕ) [Fact p.Prime] : (ZMod p)ˣ →* MulAut (ZMod p)`
   sending `u ↦ multiplicationByU`.
3. Define `AGL1Z (p : ℕ) [Fact p.Prime] := SemidirectProduct (ZMod p) (ZMod p)ˣ (affineHom p)`.
4. Prove `Nat.card (AGL1Z p) = p * (p - 1)` for `p` prime.
5. Define the natural action `AGL1Z p →* Equiv.Perm (ZMod p)` and prove
   it is faithful.
6. Defer solvability + primitivity to S3.

Target for S2: ~80 lines, 0 sorries on the definitions and the order
calculation. Solvability + primitivity (Targets B, C) are S3 work.

### Sorries / axioms anticipated

- **0 new axioms** for the forward direction. Every step is a direct
  application of Mathlib's `SemidirectProduct` / `IsSolvable` /
  `MulAction` API.
- **Possible sorries** in S4 for the primitivity step if Mathlib's
  `IsPrimitive` API at v4.26.0 is incomplete; a fallback is to define
  primitivity inline and prove the lemma directly.
- The Galois direction (S5+) may require axiomatizing the structure
  theorem for transitive permutation groups of prime degree, unless the
  full proof is unrolled in Lean. Decision deferred to S5.

### Risk register

- **Mathlib `IsPrimitive` surface drift.** The exact name of the
  `IsPrimitive` predicate has changed across Mathlib versions. Verify
  at v4.26.0 in S2; if unavailable, define inline.
- **Sharp 2-transitivity of $\mathrm{AGL}(1, p)$.** Mathlib's API for
  multiply-transitive actions may not directly give "sharply
  2-transitive ⇒ primitive". Have a fallback direct-block argument
  ready.
- **`Equiv.Perm.sign` / `Equiv.Perm.cycleType` reliance.** The Galois
  direction needs $p$-cycle structure on $S_p$; verify Mathlib's
  `cycleType` API supports the necessary lemmas at v4.26.0.

### Pre-work assessment answers (per researcher methodology)

1. **The Axiom Question**: parent + OQ-04 are 0 axioms; OQ-07 has 1
   axiom + 1 sorry. The OQ-06 forward direction should be 0 axioms.
2. **The Value Question**: Yes — the forward direction is a complete
   formal definition of an important primitive solvable group, the only
   prime-degree primitive solvable case per Galois. Sharpens the
   parent's qualitative threshold theorem quantitatively.
3. **The Proof Strategy Question**: Forward direction is finite (one
   $p$ at a time, parameterized by `[Fact p.Prime]`); Galois direction
   is over all primitive solvable subgroups of $S_p$ — proved by
   structure theorem (Sylow-$p$ uniqueness → normalizer = AGL).
4. **The Build vs Block Question**: Mathlib has enough infrastructure
   for the forward direction; the Galois direction may need ~300-500
   lines of new permutation-group structure-theorem material, which
   could be split into a sub-OQ if it threatens to grow beyond budget.
