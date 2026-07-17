import Proofs.TractatusQuantifiers

/-
# Tractatus N-operator (TLP 5.5, 5.502, 5.52)

Wittgenstein's N-operator is joint denial: `N(ξ̄)` says that every
proposition among `ξ̄` is false (TLP 5.502). TLP 5.5 claims every
truth-function arises from successive N-applications; TLP 5.52 claims
quantifiers do too: `∀x.fx = N(∼fx̄)` and `∃x.fx = ∼N(fx̄)`, where the
bar ranges over all instances. For finite domains this is
unproblematic; for infinite domains, Geach (1981) and Soames (1983)
object that a finitary syntactic operation cannot take infinitely many
arguments.

This file settles both directions:

- `NOp_eval` / `NOpFO_eval` — the defining semantics of joint denial.
- `NOp_pair_eval` — binary N is NOR (the dual Sheffer stroke).
- `neg_via_NOp`, `conj_via_NOp` — {¬, ∧} from N alone (TLP 5.5, 5.512).
- `forall_as_NOpFO`, `exists_as_NOpFO` — TLP 5.52 holds for any
  completely enumerated (finite) domain.
- `no_finite_NOp_for_forall` — the Geach–Soames critique as a theorem:
  over an infinite domain, NO single N-application over finitely many
  instances of the elementary family expresses the universal
  quantifier.

## Attribution

The theorem statements in this file were authored by us (they discharge
Future Work item 1 of paper v6). The proofs were produced by Harmonic's
Aristotle automated theorem prover (https://aristotle.harmonic.fun),
project `c15df233-5928-4d8d-8870-14d9cbb56a53`, 2026-07-12, from the
sorried statements; statements are unchanged from submission. All
proofs were re-verified against this repository's pinned toolchain.
Axiom footprint: `propext`, `Classical.choice`, `Quot.sound` only.
-/

namespace Tractatus

-- ═══════════════════════════════════════════════════════════════
-- SECTION 1: The N-operator (TLP 5.502): joint denial
-- ═══════════════════════════════════════════════════════════════

/-- Wittgenstein's N-operator over a nonempty argument list, encoded as
    head + tail: `NOp p ps` says "`p` is false and every member of `ps`
    is false". -/
def NOp (p : Proposition S) (ps : List (Proposition S)) : Proposition S :=
  ps.foldl (fun acc q => Proposition.conj acc (Proposition.neg q))
    (Proposition.neg p)

/-- First-order N-operator, same shape. -/
def NOpFO (p : FOProp S D) (ps : List (FOProp S D)) : FOProp S D :=
  ps.foldl (fun acc q => FOProp.conjFO acc (FOProp.negFO q))
    (FOProp.negFO p)

-- ═══════════════════════════════════════════════════════════════
-- SECTION 2: Defining semantics of joint denial
-- ═══════════════════════════════════════════════════════════════

/-- `N(ξ̄)` is true exactly when every argument is false (TLP 5.502). -/
theorem NOp_eval (p : Proposition S) (ps : List (Proposition S))
    (w : World S) :
    (NOp p ps).eval w ↔ ∀ q ∈ p :: ps, ¬ q.eval w := by
  unfold NOp
  induction' ps using List.reverseRecOn with ps ih <;> simp_all +decide [Proposition.eval]
  grind

/-- First-order analogue of `NOp_eval`. -/
theorem NOpFO_eval (p : FOProp S D) (ps : List (FOProp S D))
    (w : World S) :
    (NOpFO p ps).eval w ↔ ∀ q ∈ p :: ps, ¬ q.eval w := by
  induction ps using List.reverseRecOn generalizing p
  · aesop
  · simp_all +decide [NOpFO]
    simp_all +decide [FOProp.eval, and_assoc]
    grind

-- ═══════════════════════════════════════════════════════════════
-- SECTION 3: N generalizes NOR and suffices for {¬, ∧} (TLP 5.5)
-- ═══════════════════════════════════════════════════════════════

/-- Binary N is NOR: `N(p, q)` is true iff neither `p` nor `q` is. -/
theorem NOp_pair_eval (p q : Proposition S) (w : World S) :
    (NOp p [q]).eval w ↔ ¬ (p.eval w ∨ q.eval w) := by
  simp +decide [NOp_eval, not_or]

/-- Unary N is negation (TLP 5.512): `¬p = N(p)`. -/
theorem neg_via_NOp (p : Proposition S) (w : World S) :
    (NOp p []).eval w ↔ (Proposition.neg p).eval w := by
  rfl

/-- Conjunction from N alone: `p ∧ q = N(N(p), N(q))` (classical). -/
theorem conj_via_NOp (p q : Proposition S) (w : World S) :
    (NOp (NOp p []) [NOp q []]).eval w ↔
      (Proposition.conj p q).eval w := by
  simp +decide [NOp, Proposition.eval]

-- ═══════════════════════════════════════════════════════════════
-- SECTION 4: TLP 5.52 for finite domains
-- ═══════════════════════════════════════════════════════════════

/-- TLP 5.52, universal half: over a completely enumerated domain
    `d :: ds`, the universal quantifier is the N-operator applied to the
    negated instances: `∀x.fx = N(∼f d, ∼f d₁, …)`. -/
theorem forall_as_NOpFO (f : D → FOProp S D)
    (d : D) (ds : List D) (hcomplete : ∀ x : D, x ∈ d :: ds)
    (w : World S) :
    (FOProp.forall_ f).eval w ↔
      (NOpFO (FOProp.negFO (f d))
        (ds.map (fun x => FOProp.negFO (f x)))).eval w := by
  convert (NOpFO_eval _ _ _) |> Iff.symm using 1
  simp +decide [FOProp.eval]
  grind

/-- TLP 5.52, existential half: `∃x.fx = ∼N(f d, f d₁, …)`. -/
theorem exists_as_NOpFO (f : D → FOProp S D)
    (d : D) (ds : List D) (hcomplete : ∀ x : D, x ∈ d :: ds)
    (w : World S) :
    (FOProp.exists_ f).eval w ↔
      (FOProp.negFO (NOpFO (f d) (ds.map f))).eval w := by
  simp +decide [FOProp.eval, NOpFO]
  -- Rewrite the folded conjunction of negated instances.
  have h_foldl : ∀ (l : List (FOProp S D)),
      (List.foldl (fun acc q => acc.conjFO q.negFO) (f d).negFO l).eval w ↔
        (∀ q ∈ l, ¬ (q.eval w)) ∧ ¬ ((f d).eval w) := by
    intro l
    induction' l using List.reverseRecOn with l ih
    · simp [FOProp.eval]
    · simp_all +decide [FOProp.eval]
      grind
  grind

-- ═══════════════════════════════════════════════════════════════
-- SECTION 5: The Geach–Soames failure for infinite domains
-- ═══════════════════════════════════════════════════════════════

/-- The infinite-domain obstruction (Geach 1981, Soames 1983), formal
    core: over an infinite domain `D` (with atoms `S = D`), no single
    N-application over finitely many instances of the elementary family
    `x ↦ elementary x` has the same truth conditions as the universal
    quantifier. Witness world: `fun s => s ∈ d :: ds`. -/
theorem no_finite_NOp_for_forall {D : Type} [Infinite D]
    (d : D) (ds : List D) :
    ¬ (∀ w : World D,
        (FOProp.forall_
          (fun x => (FOProp.lift (Proposition.elementary x) : FOProp D D))).eval w ↔
        (NOpFO
          (FOProp.negFO (FOProp.lift (Proposition.elementary d) : FOProp D D))
          (ds.map (fun x =>
            FOProp.negFO (FOProp.lift (Proposition.elementary x))))).eval w) := by
  push_neg
  by_cases h : ∃ x : D, x ∉ d :: ds
  · refine ⟨fun s => s ∈ d :: ds, ?_⟩
    simp_all +decide [NOpFO_eval]
    refine Or.inr ⟨?_, ?_, ?_⟩ <;> simp_all +decide [FOProp.eval]
    · exact h.imp fun x hx => by unfold Proposition.eval; aesop
    · exact Or.inl rfl
    · exact fun x hx => Or.inr hx
  · exact False.elim <| h <|
      by simpa using List.finite_toSet (d :: ds) |> Set.Finite.exists_notMem

end Tractatus
