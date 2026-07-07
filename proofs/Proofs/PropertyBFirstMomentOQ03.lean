/-
  OQ-03: Non-uniform sharpening of the first-moment Property B criterion

  Parent `PropertyBFirstMoment.lean` proves Erdős 1963 for *uniform* hypergraphs:
  a `k`-uniform family with `< 2^(k-1)` edges has Property B (is 2-colorable).
  That bound only uses the edge *count*. This file sharpens the same first-moment
  argument to **arbitrary edge sizes**: the genuine Erdős criterion

      ∑_{e ∈ E} 2^(1-|e|) < 1   ⟹   E has Property B,

  stated over the natural numbers (no division) as `2 · ∑_{e} 2^(n-|e|) < 2^n`,
  where `n = |V|`. Large edges contribute geometrically less, so a family with
  many large edges and few small ones is 2-colorable even when its raw edge count
  far exceeds `2^(k-1)` for the smallest edge size `k`. The uniform theorem is the
  special case `|e| = k` (proved here as a corollary, confirming the refinement is
  faithful).

  This is the **sharp form of the first-moment lower bound**. It is NOT the
  Radhakrishnan–Srinivasan bound `m(k) = Ω(2^k · √(k/log k))` that OQ-03 ultimately
  targets: that extra `√(k/log k)` factor requires a *random recoloring* (alteration)
  argument — a second round that repairs the monochromatic edges left by the first —
  which is beyond the single-round first moment formalized here. See the knowledge
  base for the recoloring roadmap and tractability assessment.

  Status: 0 sorries, 0 axioms.
-/
import Proofs.PropertyBFirstMoment

namespace ProbMethod.PropertyB

open Finset BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **Non-uniform first-moment criterion for Property B.** A finite edge family `E`
of nonempty edges (each of size `≤ n = |V|`) is 2-colorable as soon as the weighted
edge sum satisfies `2 · ∑_{e ∈ E} 2^(n - |e|) < 2^n` — equivalently `∑_e 2^(1-|e|) < 1`.

The proof is the parent's first moment over the `2^n` uniform 2-colorings, now without
the uniformity assumption: the total `(coloring, monochromatic edge)` incidence count is
`∑_{e} 2 · 2^(n-|e|)` (each edge `e` is monochromatic under exactly `2 · 2^(n-|e|)`
colorings, by `card_mono`), and when that is `< 2^n` the first moment principle
(`exists_zero_of_sum_lt_card`) hands back a coloring with no monochromatic edge. -/
theorem property_b_of_weighted_first_moment
    (E : Finset (Finset V))
    (hne : ∀ e ∈ E, e.Nonempty)
    (hsmall : 2 * ∑ e ∈ E, 2 ^ (Fintype.card V - e.card) < 2 ^ Fintype.card V) :
    ∃ c : V → Bool, ∀ e ∈ E, ¬ Mono e c := by
  -- ∑_c (#monochromatic edges under c) = ∑_e 2·2^(n-|e|)
  have hsum :
      (∑ c : V → Bool, (E.filter (fun e => Mono e c)).card)
        = ∑ e ∈ E, 2 * 2 ^ (Fintype.card V - e.card) := by
    simp_rw [Finset.card_filter]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl ?_
    intro e he
    rw [← Finset.card_filter, card_mono e (hne e he)]
  have hcard : (univ : Finset (V → Bool)).card = 2 ^ Fintype.card V := by
    rw [Finset.card_univ, Fintype.card_fun, Fintype.card_bool]
  -- strict inequality: incidence sum < number of colorings
  have hlt :
      (∑ c : V → Bool, (E.filter (fun e => Mono e c)).card)
        < (univ : Finset (V → Bool)).card := by
    rw [hsum, hcard, ← Finset.mul_sum]
    exact hsmall
  -- first moment principle yields a coloring with zero monochromatic edges
  obtain ⟨c, -, hc⟩ := exists_zero_of_sum_lt_card hlt
  refine ⟨c, ?_⟩
  have hempty : E.filter (fun e => Mono e c) = ∅ := Finset.card_eq_zero.mp hc
  intro e he
  exact (Finset.filter_eq_empty_iff.mp hempty) he

/-- **The uniform Erdős bound is the special case.** Re-deriving `property_b_two_colorable`
(`k`-uniform, `< 2^(k-1)` edges) from the non-uniform criterion: with every `|e| = k` the
weighted sum collapses to `|E| · 2^(n-k)`, and `|E| < 2^(k-1)` is exactly
`2 · |E| · 2^(n-k) < 2^n`. This confirms the refinement faithfully extends the parent. -/
theorem property_b_two_colorable_of_uniform
    (E : Finset (Finset V)) (k : ℕ) (hk : 1 ≤ k)
    (huniform : ∀ e ∈ E, e.card = k)
    (hsmall : E.card < 2 ^ (k - 1)) :
    ∃ c : V → Bool, ∀ e ∈ E, ¬ Mono e c := by
  rcases E.eq_empty_or_nonempty with hE | hE
  · exact ⟨fun _ => true, by simp [hE]⟩
  obtain ⟨e₀, he₀⟩ := hE
  have hkn : k ≤ Fintype.card V := by
    have hle : e₀.card ≤ Fintype.card V := by
      rw [← Finset.card_univ]; exact Finset.card_le_card (Finset.subset_univ e₀)
    rw [huniform e₀ he₀] at hle; exact hle
  apply property_b_of_weighted_first_moment E
  · intro e he; exact Finset.card_pos.mp (by rw [huniform e he]; omega)
  · -- 2 · ∑_e 2^(n-k) = 2 · |E| · 2^(n-k) < 2^n
    have hsumc : (∑ e ∈ E, 2 ^ (Fintype.card V - e.card))
        = E.card * 2 ^ (Fintype.card V - k) := by
      rw [Finset.sum_congr rfl (fun e he => by rw [huniform e he]),
        Finset.sum_const, smul_eq_mul]
    rw [hsumc]
    have e1 : (2 : ℕ) ^ Fintype.card V = 2 ^ k * 2 ^ (Fintype.card V - k) := by
      rw [← pow_add]; congr 1; omega
    have ekey : E.card * 2 < 2 ^ k := by
      have e2 : (2 : ℕ) ^ k = 2 * 2 ^ (k - 1) := by
        conv_lhs => rw [show k = 1 + (k - 1) by omega]
        rw [pow_add, pow_one]
      rw [e2]; omega
    calc 2 * (E.card * 2 ^ (Fintype.card V - k))
          = (E.card * 2) * 2 ^ (Fintype.card V - k) := by ring
      _ < 2 ^ k * 2 ^ (Fintype.card V - k) :=
          (Nat.mul_lt_mul_right (pow_pos (by norm_num) _)).mpr ekey
      _ = 2 ^ Fintype.card V := e1.symm

/-- **Worked example where non-uniformity is essential.** Over `V = Fin 3` the family
`{{0,1}, {0,1,2}}` mixes a size-2 and a size-3 edge. The weighted sum is
`2^(3-2) + 2^(3-3) = 2 + 1 = 3`, and `2 · 3 = 6 < 8 = 2^3`, so the criterion certifies a
proper 2-coloring. (The uniform theorem does not apply directly — the edges have different
sizes.) -/
theorem mixed_example_two_colorable :
    ∃ c : Fin 3 → Bool, ∀ e ∈ ({{0, 1}, {0, 1, 2}} : Finset (Finset (Fin 3))),
      ¬ Mono e c := by
  apply property_b_of_weighted_first_moment
  · decide
  · decide

-- ═══════════════════════════════════════════════════
-- Quantitative first moment: a coloring with few monochromatic edges
-- ═══════════════════════════════════════════════════

/-
  The parent's `exists_zero_of_sum_lt_card` is the *strict-threshold* form of the
  first moment: when the incidence sum drops below the number of colorings, a
  *perfect* coloring (zero monochromatic edges) exists. The averaging principle
  below is its complementary, quantitative cousin: it bounds the *minimum* number
  of monochromatic edges by the *average*, so it stays informative when the strict
  criterion just fails. This is the genuine precursor to the Radhakrishnan–Srinivasan
  alteration argument — that argument first secures a coloring with *few* bad edges,
  then repairs them by recoloring; the lemmas here formalize the "few bad edges"
  half, leaving only the (analytic, multi-session) recoloring half for RS.
-/

/-- **Averaging principle (minimum ≤ mean) over `ℕ`.** If a nonnegative integer
statistic `f` on a nonempty finite set sums to at most `|s| · t`, some element
takes value `≤ t`. The `t = 0` case is `exists_zero_of_sum_lt_card` strengthened
to nonstrict; positive `t` is the surplus form the alteration method consumes. -/
theorem exists_le_of_sum_le_card_mul {α : Type*} {s : Finset α} {f : α → ℕ} {t : ℕ}
    (hne : s.Nonempty) (hle : (∑ a ∈ s, f a) ≤ s.card * t) : ∃ a ∈ s, f a ≤ t := by
  by_contra h
  push_neg at h
  have h1 : ∀ a ∈ s, t + 1 ≤ f a := fun a ha => h a ha
  have hge : s.card * (t + 1) ≤ ∑ a ∈ s, f a := by
    calc s.card * (t + 1) = ∑ _a ∈ s, (t + 1) := by
            rw [Finset.sum_const, smul_eq_mul]
      _ ≤ ∑ a ∈ s, f a := Finset.sum_le_sum h1
  have hpos : 1 ≤ s.card := Finset.card_pos.mpr hne
  have hcomb : s.card * (t + 1) ≤ s.card * t := le_trans hge hle
  rw [Nat.mul_succ] at hcomb
  omega

/-- **Quantitative first moment for Property B.** Some 2-coloring leaves at most `t`
monochromatic edges, whenever the total `(coloring, monochromatic edge)` incidence
`∑_{e} 2·2^(n-|e|)` is at most `2^n · t`. (Incidence `= ∑_c #{monochromatic edges
under c}`, by `card_mono`, so its average over the `2^n` colorings is the displayed
bound; the minimum is `≤` the average.)

The `t = 0` regime recovers the existence of a *proper* coloring; the value of the
statement is the regime where the strict criterion `property_b_of_weighted_first_moment`
*fails* (incidence `≥ 2^n`) yet the family still admits a coloring with a controlled
number `t ≥ 1` of defects — the input to a recoloring/alteration repair. -/
theorem exists_coloring_few_mono
    (E : Finset (Finset V)) (hne : ∀ e ∈ E, e.Nonempty) (t : ℕ)
    (hbound : (∑ e ∈ E, 2 * 2 ^ (Fintype.card V - e.card)) ≤ 2 ^ Fintype.card V * t) :
    ∃ c : V → Bool, (E.filter (fun e => Mono e c)).card ≤ t := by
  -- ∑_c (#monochromatic edges under c) = ∑_e 2·2^(n-|e|)  (same count as the criterion)
  have hsum :
      (∑ c : V → Bool, (E.filter (fun e => Mono e c)).card)
        = ∑ e ∈ E, 2 * 2 ^ (Fintype.card V - e.card) := by
    simp_rw [Finset.card_filter]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl ?_
    intro e he
    rw [← Finset.card_filter, card_mono e (hne e he)]
  have hcard : (univ : Finset (V → Bool)).card = 2 ^ Fintype.card V := by
    rw [Finset.card_univ, Fintype.card_fun, Fintype.card_bool]
  have hUne : (univ : Finset (V → Bool)).Nonempty := by
    rw [← Finset.card_pos, hcard]; positivity
  have hle :
      (∑ c : V → Bool, (E.filter (fun e => Mono e c)).card)
        ≤ (univ : Finset (V → Bool)).card * t := by
    rw [hsum, hcard]; exact hbound
  obtain ⟨c, -, hc⟩ := exists_le_of_sum_le_card_mul hUne hle
  exact ⟨c, hc⟩

/-- **Uniform quantitative bound.** A `k`-uniform family of `|E|` edges admits a
2-coloring with at most `t` monochromatic edges whenever `|E| ≤ 2^(k-1) · t`. The
strict criterion's threshold is the `t = 1` boundary `|E| < 2^(k-1) ⟹ 0`; this
extends one notch past it: `|E| ≤ 2^(k-1) · t ⟹ ≤ t` defects. -/
theorem exists_coloring_few_mono_uniform
    (E : Finset (Finset V)) (k t : ℕ) (hk : 1 ≤ k)
    (huniform : ∀ e ∈ E, e.card = k) (hne : ∀ e ∈ E, e.Nonempty)
    (hkn : k ≤ Fintype.card V)
    (hcard : E.card ≤ 2 ^ (k - 1) * t) :
    ∃ c : V → Bool, (E.filter (fun e => Mono e c)).card ≤ t := by
  apply exists_coloring_few_mono E hne t
  -- ∑_e 2·2^(n-k) = 2·|E|·2^(n-k) ≤ 2^k·t·2^(n-k) = 2^n·t
  have hsumc : (∑ e ∈ E, 2 * 2 ^ (Fintype.card V - e.card))
      = 2 * E.card * 2 ^ (Fintype.card V - k) := by
    rw [Finset.sum_congr rfl (fun e he => by rw [huniform e he]),
      Finset.sum_const, smul_eq_mul]; ring
  have e1 : (2 : ℕ) ^ Fintype.card V = 2 ^ k * 2 ^ (Fintype.card V - k) := by
    rw [← pow_add]; congr 1; omega
  have e2 : (2 : ℕ) ^ k = 2 * 2 ^ (k - 1) := by
    conv_lhs => rw [show k = 1 + (k - 1) by omega]
    rw [pow_add, pow_one]
  rw [hsumc, e1]
  calc 2 * E.card * 2 ^ (Fintype.card V - k)
        ≤ 2 * (2 ^ (k - 1) * t) * 2 ^ (Fintype.card V - k) := by gcongr
    _ = 2 ^ k * 2 ^ (Fintype.card V - k) * t := by rw [e2]; ring

/-- **Worked example: bounded defect on a non-2-colorable family.** The triangle
`K₃ = {{0,1}, {0,2}, {1,2}}` over `Fin 3` is *not* 2-colorable (it has no Property B),
so the strict criterion certifies nothing. Yet incidence `= 3 · 2·2^(3-2) = 12 ≤ 16 = 2³·2`,
so `exists_coloring_few_mono` (with `t = 2`) guarantees a 2-coloring leaving at most `2`
monochromatic edges — quantitative control exactly where the criterion is silent. -/
theorem triangle_few_mono :
    ∃ c : Fin 3 → Bool,
      (({{0, 1}, {0, 2}, {1, 2}} : Finset (Finset (Fin 3))).filter
        (fun e => Mono e c)).card ≤ 2 := by
  apply exists_coloring_few_mono _ _ 2
  · decide
  · decide

-- ═══════════════════════════════════════════════════
-- Deletion (alteration) method: a 2-colorable subfamily after removing few edges
-- ═══════════════════════════════════════════════════

/-
  The quantitative first moment above secures a coloring with *few* monochromatic
  edges; the deletion method turns that into a genuine 2-colorable hypergraph by
  *removing* those few bad edges. This is the elementary, integer sibling of the
  Radhakrishnan–Srinivasan *recoloring* alteration: RS repairs the bad edges by
  flipping vertices (gaining the `√(k/log k)` factor); the deletion method simply
  discards them (gaining nothing asymptotically, but giving a clean, fully finite
  2-colorability statement — "every family has a 2-colorable subfamily missing at
  most `t = ⌈incidence / 2^n⌉` edges"). It is the standard "delete one edge per
  monochromatic edge" argument, and it is the conceptual bridge from the counting
  lemmas to a real alteration.
-/

/-- Helper: a coloring `c` leaving `≤ t` monochromatic edges of `E` exhibits a
2-colorable subfamily `E \ D` obtained by deleting the `≤ t` monochromatic edges
`D = {e ∈ E | Mono e c}`. The *same* coloring `c` properly 2-colors `E \ D`, because
every retained edge is, by construction, not monochromatic under `c`. -/
private theorem subfamily_of_few_mono
    (E : Finset (Finset V)) (c : V → Bool) (t : ℕ)
    (hc : (E.filter (fun e => Mono e c)).card ≤ t) :
    ∃ D ⊆ E, D.card ≤ t ∧ ∃ c' : V → Bool, ∀ e ∈ E \ D, ¬ Mono e c' := by
  refine ⟨E.filter (fun e => Mono e c), Finset.filter_subset _ _, hc, c, ?_⟩
  intro e he
  rw [Finset.mem_sdiff] at he
  obtain ⟨heE, heD⟩ := he
  rw [Finset.mem_filter] at heD
  push_neg at heD
  exact heD heE

/-- **Deletion method for Property B.** Every finite family `E` of nonempty edges
has a 2-colorable subfamily obtained by deleting at most `t` edges, whenever the
incidence total `∑_{e} 2·2^(n-|e|)` is at most `2^n · t`. (Take the coloring with
`≤ t` monochromatic edges from `exists_coloring_few_mono` and delete exactly those.)

The strict criterion `property_b_of_weighted_first_moment` is the `t = 0` boundary:
incidence `< 2^n` deletes nothing. For `t ≥ 1` this stays informative past that
threshold — the family need not be 2-colorable, yet all but `≤ t` of its edges are
simultaneously 2-colorable. This is the deletion (alteration) form, the elementary
sibling of the Radhakrishnan–Srinivasan recoloring repair. -/
theorem exists_two_colorable_subfamily
    (E : Finset (Finset V)) (hne : ∀ e ∈ E, e.Nonempty) (t : ℕ)
    (hbound : (∑ e ∈ E, 2 * 2 ^ (Fintype.card V - e.card)) ≤ 2 ^ Fintype.card V * t) :
    ∃ D ⊆ E, D.card ≤ t ∧ ∃ c : V → Bool, ∀ e ∈ E \ D, ¬ Mono e c := by
  obtain ⟨c, hc⟩ := exists_coloring_few_mono E hne t hbound
  exact subfamily_of_few_mono E c t hc

/-- **Uniform deletion bound.** A `k`-uniform family of `|E|` edges has a 2-colorable
subfamily after deleting at most `t` edges whenever `|E| ≤ 2^(k-1) · t`. Equivalently,
a `k`-uniform hypergraph on `m` edges always retains a 2-colorable subfamily of at least
`m - ⌈m / 2^(k-1)⌉` edges — the standard deletion-method consequence of the first moment
`m · 2^(1-k)` expected monochromatic edges. -/
theorem exists_two_colorable_subfamily_uniform
    (E : Finset (Finset V)) (k t : ℕ) (hk : 1 ≤ k)
    (huniform : ∀ e ∈ E, e.card = k) (hne : ∀ e ∈ E, e.Nonempty)
    (hkn : k ≤ Fintype.card V)
    (hcard : E.card ≤ 2 ^ (k - 1) * t) :
    ∃ D ⊆ E, D.card ≤ t ∧ ∃ c : V → Bool, ∀ e ∈ E \ D, ¬ Mono e c := by
  obtain ⟨c, hc⟩ := exists_coloring_few_mono_uniform E k t hk huniform hne hkn hcard
  exact subfamily_of_few_mono E c t hc

/-- **Worked example: bipartite subgraph of `K₄` by deletion.** The complete graph
`K₄ = {{0,1},{0,2},{0,3},{1,2},{1,3},{2,3}}` (a 2-uniform family over `Fin 4`) is not
bipartite — it contains triangles, so it has no Property B. Its incidence total is
`6 · 2·2^(4-2) = 48 = 2^4 · 3`, so the deletion bound (`t = 3`) produces a 2-coloring
(a vertex bipartition) under which at most `3` of the `6` edges are removed, i.e. a
bipartite subgraph on `≥ 3` edges — a finite Max-Cut-flavored instance of the method.
(The first moment is loose here: deleting `2` edges already yields the bipartite `K_{2,2}`;
the averaging certifies only `≤ 3`.) -/
theorem k4_bipartite_subfamily :
    ∃ D ⊆ ({{0, 1}, {0, 2}, {0, 3}, {1, 2}, {1, 3}, {2, 3}} :
        Finset (Finset (Fin 4))),
      D.card ≤ 3 ∧ ∃ c : Fin 4 → Bool,
        ∀ e ∈ ({{0, 1}, {0, 2}, {0, 3}, {1, 2}, {1, 3}, {2, 3}} :
            Finset (Finset (Fin 4))) \ D, ¬ Mono e c := by
  apply exists_two_colorable_subfamily _ _ 3
  · decide
  · decide

-- ═══════════════════════════════════════════════════
-- Sharpness: the strict inequality `< 2^n` (i.e. `∑ 2^(1-|e|) < 1`) is best possible
-- ═══════════════════════════════════════════════════

/-
  The criterion `property_b_of_weighted_first_moment` requires the *strict* inequality
  `2·∑ 2^(n-|e|) < 2^n`, equivalently `∑ 2^(1-|e|) < 1`. The lemmas below witness that
  this threshold is sharp: the inequality cannot be relaxed to `≤` (and the constant `1`
  cannot be increased). A single *singleton* edge `{v}` is monochromatic under every
  coloring — a one-element set is trivially monochromatic — so the family `{{v}}` has no
  proper 2-coloring, yet its incidence total `2·2^(n-1)` sits *exactly* on the boundary
  `2^n` (i.e. `∑ 2^(1-|e|) = 1`). This is the elementary boundary obstruction; it confirms
  the "sharp at `∑ 2^(1-|e|) < 1`" framing of OQ-03 is a theorem, not merely an assertion.
-/

omit [Fintype V] [DecidableEq V] in
/-- A singleton edge `{v}` is monochromatic under *every* coloring: a one-element set is
trivially monochromatic (its single vertex agrees with itself). -/
theorem mono_singleton (v : V) (c : V → Bool) : Mono ({v} : Finset V) c :=
  ⟨c v, by intro x hx; rw [Finset.mem_singleton] at hx; rw [hx]⟩

omit [DecidableEq V] in
/-- **Sharpness of the strict first-moment criterion.** For any nonempty `V` (witnessed by
a vertex `v`), the boundary family `{{v}}` of a single singleton edge
* consists of nonempty edges,
* has incidence total *exactly* `2^n` — i.e. it saturates the criterion's bound with
  equality, `2·∑_{e} 2^(n-|e|) = 2^n` (equivalently `∑_e 2^(1-|e|) = 1`), and
* has **no** proper 2-coloring (the singleton is monochromatic under every coloring).

Hence the strict `< 2^n` in `property_b_of_weighted_first_moment` cannot be relaxed to
`≤ 2^n`: the criterion is sharp exactly at `∑ 2^(1-|e|) < 1`. -/
theorem weighted_criterion_sharp (v : V) :
    (∀ e ∈ ({{v}} : Finset (Finset V)), e.Nonempty) ∧
    2 * ∑ e ∈ ({{v}} : Finset (Finset V)), 2 ^ (Fintype.card V - e.card)
      = 2 ^ Fintype.card V ∧
    ¬ ∃ c : V → Bool, ∀ e ∈ ({{v}} : Finset (Finset V)), ¬ Mono e c := by
  refine ⟨?_, ?_, ?_⟩
  · -- the only edge is `{v}`, which is nonempty
    intro e he
    rw [Finset.mem_singleton] at he; subst he
    exact Finset.singleton_nonempty v
  · -- incidence `= 2·2^(n-1) = 2^n`, using `n = |V| ≥ 1`
    have hn : 1 ≤ Fintype.card V := Fintype.card_pos_iff.mpr ⟨v⟩
    rw [Finset.sum_singleton, Finset.card_singleton, ← pow_succ']
    congr 1
    omega
  · -- a proper coloring would have to make `{v}` non-monochromatic — impossible
    rintro ⟨c, hc⟩
    exact hc {v} (Finset.mem_singleton_self ({v} : Finset V)) (mono_singleton v c)

/-- **Concrete boundary witness over `Fin 1`.** The family `{{0}}` over `V = Fin 1` has
incidence total `2·2^(1-1) = 2 = 2^1` (equality, *not* `< 2^1`) and no proper 2-coloring,
so the strict inequality of the criterion is sharp at the smallest possible scale. -/
theorem boundary_singleton_fin1 :
    2 * ∑ e ∈ ({{0}} : Finset (Finset (Fin 1))), 2 ^ (Fintype.card (Fin 1) - e.card)
      = 2 ^ Fintype.card (Fin 1) ∧
    ¬ ∃ c : Fin 1 → Bool, ∀ e ∈ ({{0}} : Finset (Finset (Fin 1))), ¬ Mono e c :=
  ⟨(weighted_criterion_sharp (0 : Fin 1)).2.1, (weighted_criterion_sharp (0 : Fin 1)).2.2⟩

/-! ### Extremal upper side: the Fano plane is not 2-colorable.

The criterion above is a *lower-bound* engine: any `3`-uniform family with fewer than
`2^(3-1) = 4` edges (indeed any family meeting the weighted bound) has Property B. The
opposite, extremal question asks how *few* edges a non-2-colorable `3`-uniform hypergraph
can have — the Erdős–Hajnal number `m(3)`. The **Fano plane** `PG(2,2)`, the unique
Steiner triple system `S(2,3,7)` on `7` points, is a `3`-uniform hypergraph with `7` edges
and **no** proper 2-coloring, so `m(3) ≤ 7`. Together with the count lower bound this
brackets the count threshold at `k = 3` into `4 ≤ m(3) ≤ 7`. Each fact is checked by the
kernel (`decide`), so the witness is axiom-free (no `native_decide`). -/

/-- The seven lines of the Fano plane `PG(2,2)` on the point set `Fin 7`
    (the unique Steiner triple system `S(2,3,7)`). -/
def fanoPlane : Finset (Finset (Fin 7)) :=
  {{0, 1, 2}, {0, 3, 4}, {0, 5, 6}, {1, 3, 5}, {1, 4, 6}, {2, 3, 6}, {2, 4, 5}}

/-- The Fano plane is `3`-uniform: every line has exactly three points. -/
theorem fano_three_uniform : ∀ e ∈ fanoPlane, e.card = 3 := by
  set_option maxRecDepth 4000 in decide

/-- The Fano plane has exactly seven edges. -/
theorem fano_card_eq_seven : fanoPlane.card = 7 := by decide

/-- **The Fano plane is not 2-colorable.** Every 2-coloring of its seven points leaves
some line monochromatic, so this `7`-edge `3`-uniform hypergraph fails Property B. It is
the extremal upper witness `m(3) ≤ 7`, complementing the first-moment lower bound
`m(3) ≥ 2^(3-1) = 4` (`property_b_two_colorable_of_uniform`). -/
theorem fano_not_two_colorable :
    ¬ ∃ c : Fin 7 → Bool, ∀ e ∈ fanoPlane, ¬ Mono e c := by
  set_option maxRecDepth 4000 in decide

-- ============================================================
-- Converse direction: the weighted lower bound on non-2-colorable families
-- ============================================================
--
-- `property_b_of_weighted_first_moment` is the *sufficient* direction: a small
-- weighted sum forces 2-colorability. Its contrapositive is the *necessary*
-- direction — the genuine Erdős lower bound `m(k) ≥ 2^(k-1)` in exact weighted
-- form. The bridge is the precise first-moment identity, which we first expose as
-- a standalone result (it was previously only computed inline).

/-- **Exact first moment (total monochromatic incidence).** Summed over all `2^n`
colorings `c : V → Bool`, the total number of monochromatic edges of a family `E` of
nonempty edges is *exactly*

    `∑_c #{ e ∈ E : e monochromatic under c } = 2 · ∑_{e ∈ E} 2^(n - |e|)`,

`n = |V|`. Every Property B first-moment bound is read off this identity: the
sufficient criterion divides it by `2^n` and asks the average to be `< 1`, the lower
bound below asks each summand to be `≥ 1`. -/
theorem total_mono_incidence_eq (E : Finset (Finset V)) (hne : ∀ e ∈ E, e.Nonempty) :
    (∑ c : V → Bool, (E.filter (fun e => Mono e c)).card)
      = 2 * ∑ e ∈ E, 2 ^ (Fintype.card V - e.card) := by
  rw [Finset.mul_sum]
  simp_rw [Finset.card_filter]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl ?_
  intro e he
  rw [← Finset.card_filter, card_mono e (hne e he)]

/-- **Weighted lower bound for non-2-colorable families (the converse).** If a family
`E` of nonempty edges has *no* proper 2-coloring, then its weighted sum saturates the
criterion's threshold:

    `2^n ≤ 2 · ∑_{e ∈ E} 2^(n - |e|)`,   i.e.   `∑_{e ∈ E} 2^(1 - |e|) ≥ 1`.

This is the exact necessary condition behind Erdős' `m(k) ≥ 2^(k-1)`: a non-2-colorable
family cannot be "first-moment small". Proof: every one of the `2^n` colorings leaves at
least one monochromatic edge, so the total incidence is `≥ 2^n`; combine with the exact
identity `total_mono_incidence_eq`. -/
theorem weighted_lower_bound_of_not_property_b (E : Finset (Finset V))
    (hne : ∀ e ∈ E, e.Nonempty)
    (hnc : ¬ ∃ c : V → Bool, ∀ e ∈ E, ¬ Mono e c) :
    2 ^ Fintype.card V ≤ 2 * ∑ e ∈ E, 2 ^ (Fintype.card V - e.card) := by
  rw [← total_mono_incidence_eq E hne]
  -- every coloring leaves at least one monochromatic edge
  have hpos : ∀ c : V → Bool, 1 ≤ (E.filter (fun e => Mono e c)).card := by
    intro c
    rw [Nat.one_le_iff_ne_zero, Ne, Finset.card_eq_zero, ← Ne,
        ← Finset.nonempty_iff_ne_empty]
    push_neg at hnc
    obtain ⟨e, he, hmono⟩ := hnc c
    exact ⟨e, Finset.mem_filter.mpr ⟨he, hmono⟩⟩
  have hcard : (univ : Finset (V → Bool)).card = 2 ^ Fintype.card V := by
    rw [Finset.card_univ, Fintype.card_fun, Fintype.card_bool]
  calc 2 ^ Fintype.card V
      = ∑ _c : V → Bool, 1 := by rw [Finset.sum_const, smul_eq_mul, mul_one, hcard]
    _ ≤ ∑ c : V → Bool, (E.filter (fun e => Mono e c)).card :=
        Finset.sum_le_sum (fun c _ => hpos c)

/-- **Erdős' uniform lower bound `m(k) ≥ 2^(k-1)`.** A `k`-uniform family `E` (with
`1 ≤ k ≤ n`) that has no proper 2-coloring must contain at least `2^(k-1)` edges. This is
the exact converse of `property_b_two_colorable_of_uniform`: together they pin the
first-moment threshold for uniform hypergraphs at `2^(k-1)` edges. -/
theorem uniform_lower_bound_of_not_property_b (E : Finset (Finset V)) {k : ℕ}
    (hk : k ≤ Fintype.card V)
    (huniform : ∀ e ∈ E, e.card = k)
    (hne : ∀ e ∈ E, e.Nonempty)
    (hnc : ¬ ∃ c : V → Bool, ∀ e ∈ E, ¬ Mono e c) :
    2 ^ (k - 1) ≤ E.card := by
  -- a non-2-colorable family is nonempty, so `k ≥ 1`
  obtain ⟨e0, he0⟩ : E.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    rintro rfl
    exact hnc ⟨fun _ => true, by simp⟩
  have hk1 : 1 ≤ k := by rw [← huniform e0 he0]; exact (hne e0 he0).card_pos
  -- the weighted converse, with the uniform weighted sum collapsed to `|E|·2^(n-k)`
  have hwb := weighted_lower_bound_of_not_property_b E hne hnc
  have hsum : ∑ e ∈ E, 2 ^ (Fintype.card V - e.card)
      = E.card * 2 ^ (Fintype.card V - k) := by
    rw [Finset.sum_congr rfl (fun e he => by rw [huniform e he]),
        Finset.sum_const, smul_eq_mul]
  rw [hsum] at hwb
  -- write `n = k + m` and cancel the common factor `2^(m+1)`
  obtain ⟨m, hm⟩ : ∃ m, Fintype.card V = k + m := ⟨Fintype.card V - k, by omega⟩
  rw [hm, Nat.add_sub_cancel_left] at hwb
  have key : 2 ^ (k - 1) * 2 ^ (m + 1) ≤ E.card * 2 ^ (m + 1) := by
    calc 2 ^ (k - 1) * 2 ^ (m + 1)
        = 2 ^ (k + m) := by rw [← pow_add]; congr 1; omega
      _ ≤ 2 * (E.card * 2 ^ m) := hwb
      _ = E.card * 2 ^ (m + 1) := by rw [pow_succ]; ring
  exact Nat.le_of_mul_le_mul_right key (by positivity)

end ProbMethod.PropertyB

-- Axiom audit: foundational axioms only; no `Lean.ofReduceBool`, no `sorryAx`.
#print axioms ProbMethod.PropertyB.total_mono_incidence_eq
#print axioms ProbMethod.PropertyB.weighted_lower_bound_of_not_property_b
#print axioms ProbMethod.PropertyB.uniform_lower_bound_of_not_property_b
