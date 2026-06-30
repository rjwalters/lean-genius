/-
  OQ-03: Deterministic recoloring (the finite core of the alteration method)

  Parent `PropertyBFirstMoment.lean` proves Erdős 1963 (a `k`-uniform family
  with `< 2^(k-1)` edges is 2-colorable) via the first moment. Its sibling
  `PropertyBFirstMomentOQ03.lean` carries that further to the *deletion* method:
  from a coloring with few monochromatic edges, **discard** those edges to expose
  a 2-colorable subfamily. Deletion throws edges away.

  This file formalizes the complementary, harder half — **recoloring** — in its
  clean deterministic regime: rather than deleting a monochromatic edge, *repair*
  it by flipping a single vertex. This is the deterministic core of the
  Radhakrishnan–Srinivasan alteration that OQ-03 ultimately targets. RS recolors
  *probabilistically* precisely because, in general, the monochromatic edges share
  vertices, so flipping one edge's vertex can break another edge. The deterministic
  statement isolates the case where that dependency is absent: each monochromatic
  edge owns a **private** vertex — one lying in no other edge of the family. Then
  flipping the private vertices repairs every bad edge and disturbs nothing else,
  giving *full* 2-colorability (not merely a subfamily, as deletion gives).

  Note the privacy hypothesis is strictly weaker than "the monochromatic edges are
  a matching": an edge needs only *one* private vertex, and may otherwise overlap
  other edges arbitrarily (see `recoloring_example_overlap`). The remaining gap to
  RS is exactly the removal of this privacy hypothesis via randomness — the
  multi-session analytic step the knowledge base scopes.

  Status: 0 sorries, 0 axioms. No `native_decide`.
-/
import Proofs.PropertyBFirstMoment

namespace ProbMethod.PropertyB

open Finset BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **Deterministic recoloring repairs Property B.** Fix a coloring `c` and let
its monochromatic edges be `M = {e ∈ E | Mono e c}`. Suppose a vertex selector
`w : Finset V → V` assigns to each monochromatic edge `e` a vertex `w e ∈ e` that
is **private** to `e` (belongs to no other edge of `E`), and every monochromatic
edge has at least two vertices. Then `E` has Property B.

The repaired coloring `c'` flips exactly the private vertices `{w e | e ∈ M}`:

* A monochromatic edge `e` was constant (say colour `b`). It has a second vertex
  `u ≠ w e` (size `≥ 2`); `u` is not a private vertex of any edge (else privacy
  would force that edge to be `e` and `u = w e`), so `u` keeps colour `b` while
  `w e` flips to `!b` — `e` is now bichromatic.
* A non-monochromatic edge contains *no* private vertex (privacy would force the
  owning edge to coincide with it, making it monochromatic), so `c'` agrees with
  `c` on it and it stays non-monochromatic.

This is the deterministic alteration: flip a private vertex per bad edge. -/
theorem property_b_of_recoloring
    (E : Finset (Finset V)) (c : V → Bool) (w : Finset V → V)
    (hmem : ∀ e ∈ E, Mono e c → w e ∈ e)
    (hcard : ∀ e ∈ E, Mono e c → 2 ≤ e.card)
    (hpriv : ∀ e ∈ E, Mono e c → ∀ e' ∈ E, w e ∈ e' → e' = e) :
    ∃ c' : V → Bool, ∀ e ∈ E, ¬ Mono e c' := by
  classical
  -- monochromatic edges, and their private vertices
  set M := E.filter (fun e => Mono e c) with hMdef
  set S := M.image w with hSdef
  have memM : ∀ e, e ∈ M ↔ e ∈ E ∧ Mono e c := by
    intro e; rw [hMdef, mem_filter]
  have memS : ∀ x, x ∈ S ↔ ∃ e ∈ M, w e = x := by
    intro x; rw [hSdef, mem_image]
  -- repaired coloring: flip exactly the private vertices
  refine ⟨fun x => if x ∈ S then !c x else c x, ?_⟩
  set c' : V → Bool := fun x => if x ∈ S then !c x else c x with hc'def
  intro e he
  by_cases hmono : Mono e c
  · -- monochromatic edge: flipping its private vertex makes it bichromatic
    have heM : e ∈ M := (memM e).mpr ⟨he, hmono⟩
    obtain ⟨b, hb⟩ := hmono
    have hwe : w e ∈ e := hmem e he ⟨b, hb⟩
    have hweS : w e ∈ S := by rw [memS]; exact ⟨e, heM, rfl⟩
    -- a second, unflipped vertex of `e`
    have h1lt : 1 < e.card := by have := hcard e he ⟨b, hb⟩; omega
    obtain ⟨u, hue, hune⟩ := Finset.exists_ne_of_one_lt_card h1lt (w e)
    have huS : u ∉ S := by
      rw [memS]
      rintro ⟨e'', he''M, hwe''⟩
      have he''E : e'' ∈ E := ((memM e'').mp he''M).1
      have he''mono : Mono e'' c := ((memM e'').mp he''M).2
      have hueE : w e'' ∈ e := by rw [hwe'']; exact hue
      have heq : e = e'' := hpriv e'' he''E he''mono e he hueE
      apply hune
      rw [← hwe'', heq]
    -- evaluate `c'` at the flipped and unflipped vertices
    have e1 : c' (w e) = !c (w e) := by simp [hc'def, hweS]
    have e2 : c' u = c u := by simp [hc'def, huS]
    have cwe_b : c (w e) = b := hb (w e) hwe
    have cu_b : c u = b := hb u hue
    -- `e` cannot be monochromatic under `c'`
    rintro ⟨b', hb'⟩
    have hwe' : c' (w e) = b' := hb' (w e) hwe
    have hu' : c' u = b' := hb' u hue
    rw [e1, cwe_b] at hwe'
    rw [e2, cu_b] at hu'
    rw [← hu'] at hwe'
    exact absurd hwe' (by cases b <;> decide)
  · -- non-monochromatic edge: it contains no flipped vertex, so it is untouched
    rintro ⟨b', hb'⟩
    apply hmono
    refine ⟨b', ?_⟩
    intro x hx
    have hxS : x ∉ S := by
      rw [memS]
      rintro ⟨e'', he''M, hwe''⟩
      have he''E : e'' ∈ E := ((memM e'').mp he''M).1
      have he''mono : Mono e'' c := ((memM e'').mp he''M).2
      have hxe : w e'' ∈ e := by rw [hwe'']; exact hx
      have heq : e = e'' := hpriv e'' he''E he''mono e he hxe
      exact hmono (by rw [heq]; exact he''mono)
    have hcx : c' x = c x := by simp [hc'def, hxS]
    rw [← hcx]; exact hb' x hx

/-- **Worked example — disjoint monochromatic edges.** Over `V = Fin 4` the
all-true colouring makes both `{0,1}` and `{2,3}` monochromatic. They are disjoint,
so vertices `0` and `2` are private; flipping them (`w` below) yields a proper
2-colouring. This is the matching case of the deterministic alteration. -/
theorem recoloring_example_disjoint :
    ∃ c' : Fin 4 → Bool,
      ∀ e ∈ ({{0, 1}, {2, 3}} : Finset (Finset (Fin 4))), ¬ Mono e c' := by
  apply property_b_of_recoloring _ (fun _ => true)
    (fun e => if (0 : Fin 4) ∈ e then 0 else 2)
  · decide
  · decide
  · decide

/-- **Worked example — overlapping monochromatic edges via private vertices.**
Over `V = Fin 4`, under the all-true colouring both `{0,1}` and `{1,2,3}` are
monochromatic and they *share* vertex `1`, so they are not a matching — yet each
still owns a private vertex (`0` for `{0,1}`, `2` for `{1,2,3}`). The recoloring
theorem applies, flipping `0` and `2` to a proper 2-colouring. This shows the
privacy hypothesis is genuinely weaker than disjointness. -/
theorem recoloring_example_overlap :
    ∃ c' : Fin 4 → Bool,
      ∀ e ∈ ({{0, 1}, {1, 2, 3}} : Finset (Finset (Fin 4))), ¬ Mono e c' := by
  apply property_b_of_recoloring _ (fun _ => true)
    (fun e => if (0 : Fin 4) ∈ e then 0 else 2)
  · decide
  · decide
  · decide

end ProbMethod.PropertyB
