import Mathlib.Tactic

/-
# The Back-and-Forth Exhaustion Engine

A child result of `schroeder-bernstein-oq-03` (Myhill's isomorphism theorem, the
computable analogue of Schröder–Bernstein). The parent file constructs a
computable permutation of `ℕ` from a pair of computable one-one reductions by a
priority (back-and-forth) construction. That construction has three logically
separable ingredients, spelled out in the parent's proof sketch of
`myhill_isomorphism`:

  (a) each stage terminates — a fresh domain/range point can always be placed;
  (b) domain/range exhaustion — every element is eventually covered;
  (c) computability — the limit permutation is computable.

The parent file already discharges (a) as two *augment steps*
(`augment_domain_step`, `augment_range_step`): from a finite partial matching `L`
with a fresh domain (resp. range) anchor, they produce an extended matching that
covers the anchor and is monotone on both domain and range while preserving the
construction invariants. What remains open in the parent is only the computable
read-off of the limit, ingredient (c).

This file isolates ingredient **(b)** as a clean, fully machine-checked, purely
order-theoretic fact that stands on its own and is completely independent of the
computability machinery:

> **Back-and-forth exhaustion.** Suppose states extend along a preorder `ext`,
> two coverage predicates `dcov`/`rcov` are monotone under `ext`, and from *any*
> state one can always extend to cover a given domain point (`dstep`) and a given
> range point (`rstep`). Then there is a monotone chain `c : ℕ → S` starting at
> `s₀` such that every `n` is covered — in both domain and range — from stage
> `n + 1` onward.

Instantiating `dstep`/`rstep` with the parent's two augment steps reduces the
open construction to ingredient (c) alone: the interleaving scheduler here shows
the back-and-forth process *reaches* every natural number, so the limit is a
total bijection of `ℕ`; the only remaining task is to read that limit off
computably.

The engine is stated with all hypotheses as explicit universally quantified
arguments (no structure fields, no `axiom`, no `sorry`, no `native_decide`): it
is `0`-axiom in the counted sense (only the ambient `Classical.choice` is used,
to pick the witnesses supplied by `dstep`/`rstep`).

## References

* J. Myhill, *Creative sets*, Z. Math. Logik Grundlagen Math. 1 (1955), 97–108.
* H. Rogers, *Theory of Recursive Functions and Effective Computability*, §7.4
  (the back-and-forth / priority construction of a recursive permutation).
* The "back-and-forth" method: G. Cantor's proof that any two countable dense
  linear orders without endpoints are isomorphic is the classical archetype of
  this exhaustion scheduler.
-/

namespace BackAndForthExhaustion

/-- **Back-and-forth exhaustion engine.**

    `S` is a type of *states* (think: finite partial matchings). States extend
    along a preorder `ext` (`ext_refl`, `ext_trans`). Two coverage predicates
    `dcov`/`rcov` (think: "`n` is in the domain / range of the matching") are
    monotone under extension (`dcov_mono`, `rcov_mono`). The two *step*
    hypotheses say a fresh domain point (`dstep`) or range point (`rstep`) can
    always be covered by a single extension.

    The conclusion produces a monotone chain `c` from `s₀` in which every `n` is
    covered — in both domain and range — at stage `n + 1`, and hence, by
    monotonicity, at every later stage. This is exactly the "domain/range
    exhaustion" step of the Rogers §7.4 priority construction, abstracted away
    from the concrete matchings and the computability read-off. -/
theorem exhaustion
    {S : Type*} (s₀ : S)
    (ext : S → S → Prop)
    (ext_refl : ∀ s, ext s s)
    (ext_trans : ∀ {a b d : S}, ext a b → ext b d → ext a d)
    (dcov rcov : S → ℕ → Prop)
    (dcov_mono : ∀ {s s' : S} {n : ℕ}, ext s s' → dcov s n → dcov s' n)
    (rcov_mono : ∀ {s s' : S} {n : ℕ}, ext s s' → rcov s n → rcov s' n)
    (dstep : ∀ (s : S) (n : ℕ), ∃ s', ext s s' ∧ dcov s' n)
    (rstep : ∀ (s : S) (n : ℕ), ∃ s', ext s s' ∧ rcov s' n) :
    ∃ c : ℕ → S,
      c 0 = s₀ ∧
      (∀ k, ext (c k) (c (k + 1))) ∧
      (∀ j k, j ≤ k → ext (c j) (c k)) ∧
      (∀ n, dcov (c (n + 1)) n ∧ rcov (c (n + 1)) n) ∧
      (∀ n k, n < k → dcov (c k) n ∧ rcov (c k) n) := by
  classical
  -- Witness choosers for the two step hypotheses.
  set chD : S → ℕ → S := fun s n => (dstep s n).choose with hchD_def
  have chD_ext : ∀ (s : S) (n : ℕ), ext s (chD s n) := fun s n => (dstep s n).choose_spec.1
  have chD_cov : ∀ (s : S) (n : ℕ), dcov (chD s n) n := fun s n => (dstep s n).choose_spec.2
  set chR : S → ℕ → S := fun s n => (rstep s n).choose with hchR_def
  have chR_ext : ∀ (s : S) (n : ℕ), ext s (chR s n) := fun s n => (rstep s n).choose_spec.1
  have chR_cov : ∀ (s : S) (n : ℕ), rcov (chR s n) n := fun s n => (rstep s n).choose_spec.2
  -- The chain: at stage `n + 1` cover domain point `n` (via `chD`), then range
  -- point `n` (via `chR`). Covering both at one stage keeps the argument free of
  -- parity bookkeeping.
  set c : ℕ → S := fun k => Nat.rec s₀ (fun n s => chR (chD s n) n) k with hc_def
  have hc0 : c 0 = s₀ := rfl
  have hcsucc : ∀ n, c (n + 1) = chR (chD (c n) n) n := fun _ => rfl
  -- One-step extension.
  have hext1 : ∀ k, ext (c k) (c (k + 1)) := by
    intro k
    rw [hcsucc k]
    exact ext_trans (chD_ext (c k) k) (chR_ext (chD (c k) k) k)
  -- Chain monotonicity: `ext (c j) (c k)` for `j ≤ k`.
  have hextle : ∀ j k, j ≤ k → ext (c j) (c k) := by
    intro j k hjk
    induction hjk with
    | refl => exact ext_refl _
    | step _ IH => exact ext_trans IH (hext1 _)
  -- First coverage: at stage `n + 1`, both domain point `n` and range point `n`
  -- are covered.
  have hcov1 : ∀ n, dcov (c (n + 1)) n ∧ rcov (c (n + 1)) n := by
    intro n
    rw [hcsucc n]
    refine ⟨?_, chR_cov (chD (c n) n) n⟩
    -- `dcov (chD (c n) n) n` holds; the trailing range step only extends the
    -- state, so `dcov_mono` transports domain coverage across it.
    exact dcov_mono (chR_ext (chD (c n) n) n) (chD_cov (c n) n)
  -- Persistent coverage / exhaustion: once covered at stage `n + 1`, `n` stays
  -- covered at every later stage `k > n`.
  have hcov : ∀ n k, n < k → dcov (c k) n ∧ rcov (c k) n := by
    intro n k hnk
    have hle : n + 1 ≤ k := hnk
    have hmono : ext (c (n + 1)) (c k) := hextle (n + 1) k hle
    exact ⟨dcov_mono hmono (hcov1 n).1, rcov_mono hmono (hcov1 n).2⟩
  exact ⟨c, hc0, hext1, hextle, hcov1, hcov⟩

/-- **Eventual coverage.** Repackaging of `exhaustion`: every `n` is covered in
    both domain and range from some stage `K` (namely `K = n + 1`) on. This is
    the form the priority construction consumes — "the partial bijection is
    defined at `n` from stage `n + 1` on and never retracted" — so its pointwise
    limit is a total function of `ℕ`. -/
theorem exhaustion_eventually
    {S : Type*} (s₀ : S)
    (ext : S → S → Prop)
    (ext_refl : ∀ s, ext s s)
    (ext_trans : ∀ {a b d : S}, ext a b → ext b d → ext a d)
    (dcov rcov : S → ℕ → Prop)
    (dcov_mono : ∀ {s s' : S} {n : ℕ}, ext s s' → dcov s n → dcov s' n)
    (rcov_mono : ∀ {s s' : S} {n : ℕ}, ext s s' → rcov s n → rcov s' n)
    (dstep : ∀ (s : S) (n : ℕ), ∃ s', ext s s' ∧ dcov s' n)
    (rstep : ∀ (s : S) (n : ℕ), ∃ s', ext s s' ∧ rcov s' n) :
    ∃ c : ℕ → S,
      c 0 = s₀ ∧
      (∀ k, ext (c k) (c (k + 1))) ∧
      ∀ n, ∃ K, ∀ k, K ≤ k → dcov (c k) n ∧ rcov (c k) n := by
  obtain ⟨c, hc0, hext1, _hextle, hcov1, _hcov⟩ :=
    exhaustion s₀ ext ext_refl ext_trans dcov rcov dcov_mono rcov_mono dstep rstep
  refine ⟨c, hc0, hext1, ?_⟩
  intro n
  refine ⟨n + 1, ?_⟩
  intro k hk
  rcases Nat.eq_or_lt_of_le hk with h | h
  · subst h; exact hcov1 n
  · exact _hcov n k (by omega)

/-!
## Non-vacuity: the engine really exhausts `ℕ`

To confirm the hypotheses are satisfiable and the conclusion is not vacuous, we
instantiate the engine with the simplest honest scenario: states are finite lists
of "already covered" naturals, extension is `l ⊆ l'` (sublist-as-subset,
monotone), coverage is membership, and each step simply prepends the requested
element. The engine then yields a chain of finite sets whose union is all of `ℕ`
— i.e. it recovers the enumerability of `ℕ` as a special case, witnessing that
the back-and-forth scheduler genuinely reaches every natural number.
-/

/-- Non-vacuity witness: the exhaustion engine, instantiated with `S = List ℕ`,
    `ext = ⊆`, coverage `= membership`, and prepend-steps, produces a chain of
    finite lists in which every `n : ℕ` is a member from some stage on. This is a
    concrete, fully-verified instance showing the abstract hypotheses are
    satisfiable and the exhaustion conclusion has content. -/
theorem nat_exhausted :
    ∃ c : ℕ → List ℕ,
      c 0 = [] ∧
      (∀ k, c k ⊆ c (k + 1)) ∧
      ∀ n, ∃ K, ∀ k, K ≤ k → n ∈ c k := by
  obtain ⟨c, hc0, hext1, hev⟩ :=
    exhaustion_eventually
      (S := List ℕ) []
      (fun l l' => l ⊆ l')
      (fun _ => List.Subset.refl _)
      (fun h₁ h₂ => List.Subset.trans h₁ h₂)
      (fun l n => n ∈ l) (fun l n => n ∈ l)
      (fun h hn => h hn) (fun h hn => h hn)
      (fun l n => ⟨n :: l, List.subset_cons_self _ _, List.mem_cons_self⟩)
      (fun l n => ⟨n :: l, List.subset_cons_self _ _, List.mem_cons_self⟩)
  refine ⟨c, hc0, hext1, ?_⟩
  intro n
  obtain ⟨K, hK⟩ := hev n
  exact ⟨K, fun k hk => (hK k hk).1⟩

end BackAndForthExhaustion
