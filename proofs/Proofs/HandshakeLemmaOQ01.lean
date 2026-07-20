import Mathlib

/-!
# Minimal edge/degree deficiency from the handshake parity obstruction

## Open question (`handshake-lemma-oq-01`)

The parent entry (`HandshakeLemma.lean`) proves the handshake lemma
`∑_v deg(v) = 2·|E|` and its parity corollary that the number of odd-degree
vertices is even. Its first open question asks to **quantify the parity
obstruction**: for `d`-regular graphs on `n` vertices with `d` odd and `n` odd
(which cannot exist), what is the *minimal deficiency* — how far must any actual
graph fall short of the regular ideal, and is that floor attained?

## What this entry proves

Fix a target degree `d`. For a finite simple graph `G` on `n = |V|` vertices
whose every vertex has degree `≤ d`, define the **degree deficiency**

  `deficiency G d = ∑_v (d − deg v) = n·d − ∑_v deg v = n·d − 2·|E|`.

Because `∑_v deg v = 2·|E|` is always even, the deficiency has the **same parity
as `n·d`**. Hence:

* `deficiency_eq` — the deficiency equals `n·d − 2·|E|` (assuming `deg ≤ d`).
* `deficiency_parity` — `deficiency G d ≡ n·d  (mod 2)`.
* `deficiency_odd` / `one_le_deficiency` — when `n·d` is **odd**, the deficiency is
  odd, hence `≥ 1`: a `d`-regular graph is impossible and *any* graph with
  `deg ≤ d` misses the ideal degree sum by at least `1`.
* `edge_upper_bound` — equivalently `2·|E| ≤ n·d − 1`: the edge count cannot reach
  the regular ideal `n·d/2`; this is the **minimal edge deficiency**.
* `not_isRegularOfDegree_of_odd_mul` — the clean impossibility corollary: no
  `d`-regular graph on `n` vertices exists once `n·d` is odd (in particular when
  both `n` and `d` are odd).

## Sharpness

The floor `1` is attained: `deficiency_floor_attained` exhibits the empty graph on
one vertex with `d = 1`, where `n·d = 1` is odd and the deficiency is exactly `1`.
So the lower bound `one_le_deficiency` cannot be improved.

Everything is sorry-free and axiom-free; the sharpness witness uses kernel
`decide`, not `native_decide`, so no extra trust assumptions are introduced.
-/

namespace HandshakeLemmaOQ01

open Finset SimpleGraph

variable {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- **Degree deficiency toward `d`-regularity.**
`deficiency G d = ∑_v (d − deg v)`, the total shortfall of the vertex degrees
from the target degree `d`. When `deg v ≤ d` for all `v` this is `n·d − 2|E|`. -/
def deficiency (d : ℕ) : ℕ := ∑ v, (d - G.degree v)

/-- The degree sum is even — the handshake identity `∑ deg = 2|E|`. -/
theorem even_sum_degrees : Even (∑ v, G.degree v) := by
  rw [G.sum_degrees_eq_twice_card_edges]; exact even_two_mul _

/-- **Deficiency as an ideal shortfall.** If every vertex has degree at most `d`
then `deficiency G d = n·d − ∑_v deg v = n·d − 2|E|`. -/
theorem deficiency_eq (d : ℕ) (hbound : ∀ v, G.degree v ≤ d) :
    deficiency G d = Fintype.card V * d - ∑ v, G.degree v := by
  unfold deficiency
  rw [Finset.sum_tsub_distrib _ (fun v _ => hbound v), Finset.sum_const, Finset.card_univ,
    smul_eq_mul]

/-- The deficiency has the same parity as `n·d`: it differs from `n·d` by the even
number `∑_v deg v = 2|E|`. -/
theorem deficiency_parity (d : ℕ) (hbound : ∀ v, G.degree v ≤ d) :
    deficiency G d % 2 = (Fintype.card V * d) % 2 := by
  obtain ⟨m, hm⟩ := even_sum_degrees G
  have hle : ∑ v, G.degree v ≤ Fintype.card V * d := by
    calc ∑ v, G.degree v ≤ ∑ _v : V, d := Finset.sum_le_sum (fun v _ => hbound v)
      _ = Fintype.card V * d := by rw [Finset.sum_const, Finset.card_univ, smul_eq_mul]
  rw [deficiency_eq G d hbound]
  omega

/-- **The parity obstruction, quantitative form.** If `n·d` is odd then the degree
deficiency is odd. -/
theorem deficiency_odd (d : ℕ) (hbound : ∀ v, G.degree v ≤ d)
    (hodd : Odd (Fintype.card V * d)) : Odd (deficiency G d) := by
  rw [Nat.odd_iff] at hodd ⊢
  rw [deficiency_parity G d hbound, hodd]

/-- **Minimal deficiency `≥ 1`.** When `n·d` is odd, *every* graph with `deg ≤ d`
has degree deficiency at least `1`; there is no `d`-regular graph. -/
theorem one_le_deficiency (d : ℕ) (hbound : ∀ v, G.degree v ≤ d)
    (hodd : Odd (Fintype.card V * d)) : 1 ≤ deficiency G d := by
  obtain ⟨k, hk⟩ := deficiency_odd G d hbound hodd
  omega

/-- **Minimal edge deficiency.** When `n·d` is odd, the number of edges satisfies
`2·|E| ≤ n·d − 1`: the edge count cannot reach the regular ideal `n·d / 2`. -/
theorem edge_upper_bound (d : ℕ) (hbound : ∀ v, G.degree v ≤ d)
    (hodd : Odd (Fintype.card V * d)) :
    2 * G.edgeFinset.card ≤ Fintype.card V * d - 1 := by
  have hdef := one_le_deficiency G d hbound hodd
  rw [deficiency_eq G d hbound, G.sum_degrees_eq_twice_card_edges] at hdef
  have hle : 2 * G.edgeFinset.card ≤ Fintype.card V * d := by
    rw [← G.sum_degrees_eq_twice_card_edges]
    calc ∑ v, G.degree v ≤ ∑ _v : V, d := Finset.sum_le_sum (fun v _ => hbound v)
      _ = Fintype.card V * d := by rw [Finset.sum_const, Finset.card_univ, smul_eq_mul]
  omega

/-- **Impossibility corollary.** No `d`-regular graph on `n` vertices exists when
`n·d` is odd — in particular when both `n` and `d` are odd. -/
theorem not_isRegularOfDegree_of_odd_mul (d : ℕ) (hodd : Odd (Fintype.card V * d)) :
    ¬ G.IsRegularOfDegree d := by
  intro hreg
  -- A `d`-regular graph has `∑ deg = n·d`, which would be odd, contradicting handshake parity.
  have hsum : ∑ v, G.degree v = Fintype.card V * d := by
    simp only [hreg.degree_eq, Finset.sum_const, Finset.card_univ, smul_eq_mul]
  have heven : Even (Fintype.card V * d) := hsum ▸ even_sum_degrees G
  obtain ⟨a, ha⟩ := hodd
  obtain ⟨b, hb⟩ := heven
  omega

/-- **The impossibility for `n` and `d` both odd** (the headline case). -/
theorem not_isRegularOfDegree_of_odd_odd (d : ℕ) (hn : Odd (Fintype.card V))
    (hd : Odd d) : ¬ G.IsRegularOfDegree d :=
  not_isRegularOfDegree_of_odd_mul G d (hn.mul hd)

/-- **Even companion of the parity dichotomy.** When `n·d` is even the degree
deficiency is even. Together with `deficiency_odd` this pins the parity of the
deficiency to that of `n·d` in both cases. -/
theorem deficiency_even_of_even (d : ℕ) (hbound : ∀ v, G.degree v ≤ d)
    (heven : Even (Fintype.card V * d)) : Even (deficiency G d) := by
  rw [Nat.even_iff] at heven ⊢
  rw [deficiency_parity G d hbound, heven]

/-- **A strictly-deficient vertex exists.** When `n·d` is odd, not only is the graph
non-regular, but some concrete vertex witnesses the shortfall: `∃ v, deg v < d`.
(If every vertex reached the target `d`, the graph would be `d`-regular, forcing
the impossible `deficiency = 0`.) This is the vertex-level refinement of
`not_isRegularOfDegree_of_odd_mul`. -/
theorem exists_degree_lt_of_odd (d : ℕ) (hbound : ∀ v, G.degree v ≤ d)
    (hodd : Odd (Fintype.card V * d)) : ∃ v, G.degree v < d := by
  by_contra h
  push_neg at h
  have hdef0 : deficiency G d = 0 := by
    unfold deficiency
    refine Finset.sum_eq_zero (fun v _ => ?_)
    have : G.degree v = d := le_antisymm (hbound v) (h v)
    omega
  have := one_le_deficiency G d hbound hodd
  omega

/-- **The below-target vertices are counted by the deficiency.** The number of
vertices whose degree strictly undershoots `d` is at most `deficiency G d` — each
such vertex contributes at least `1` to the shortfall sum `∑_v (d − deg v)`. In the
odd case this again yields a strictly-deficient vertex (the count is `≥ 1`), and it
quantifies how many vertices can miss the target. -/
theorem card_degree_lt_le_deficiency (d : ℕ) :
    (Finset.univ.filter (fun v => G.degree v < d)).card ≤ deficiency G d := by
  unfold deficiency
  rw [Finset.card_eq_sum_ones]
  calc ∑ _v ∈ Finset.univ.filter (fun v => G.degree v < d), 1
      ≤ ∑ v ∈ Finset.univ.filter (fun v => G.degree v < d), (d - G.degree v) := by
        refine Finset.sum_le_sum (fun v hv => ?_)
        rw [Finset.mem_filter] at hv
        omega
    _ ≤ ∑ v, (d - G.degree v) :=
        Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)

/-- **Sharpness: the floor `1` is attained.** The empty graph on a single vertex,
with target degree `d = 1`, has `n·d = 1` odd and degree deficiency exactly `1`.
So the lower bound `one_le_deficiency` cannot be improved. -/
theorem deficiency_floor_attained :
    deficiency (⊥ : SimpleGraph (Fin 1)) 1 = 1 := by decide

/-- The witness graph indeed has `n·d = 1` odd and every degree `≤ 1`. -/
example : Odd (Fintype.card (Fin 1) * 1) := by decide
example : ∀ v, (⊥ : SimpleGraph (Fin 1)).degree v ≤ 1 := by decide

/-! ## General (non-constant) degree targets

Open question 3 of this entry: extend the deficiency to a *prescribed*, possibly
non-constant target degree `d : V → ℕ`. The shortfall `∑_v (d v − deg v)` has the
same parity as the target sum `∑_v d v`, because it still differs from it only by
the even degree sum `2|E|`. Hence when `∑_v d v` is odd no graph can realise the
target degree sequence `d` exactly — the classical "a degree sequence with odd sum
is not graphical" necessary condition, of which the constant-`d`, `n·d`-odd
obstruction above (`not_isRegularOfDegree_of_odd_mul`) is the special case. -/

/-- **Deficiency toward a prescribed degree target `d : V → ℕ`.**
`deficiencyFun G d = ∑_v (d v − deg v)`, the total shortfall of the vertex degrees
from their individual targets `d v`. Specialises to `deficiency G d` at a constant
target. -/
def deficiencyFun (d : V → ℕ) : ℕ := ∑ v, (d v - G.degree v)

/-- The constant target `d v = d` recovers the scalar `deficiency G d`. -/
theorem deficiencyFun_const (d : ℕ) :
    deficiencyFun G (fun _ => d) = deficiency G d := rfl

/-- **Deficiency as an ideal shortfall, target-function form.** If every vertex has
degree at most its target `d v` then
`deficiencyFun G d = (∑_v d v) − ∑_v deg v = (∑_v d v) − 2|E|`. -/
theorem deficiencyFun_eq (d : V → ℕ) (hbound : ∀ v, G.degree v ≤ d v) :
    deficiencyFun G d = (∑ v, d v) - ∑ v, G.degree v := by
  unfold deficiencyFun
  rw [Finset.sum_tsub_distrib _ (fun v _ => hbound v)]

/-- The target-function deficiency has the same parity as the target sum `∑_v d v`:
it differs from it by the even degree sum `∑_v deg v = 2|E|`. -/
theorem deficiencyFun_parity (d : V → ℕ) (hbound : ∀ v, G.degree v ≤ d v) :
    deficiencyFun G d % 2 = (∑ v, d v) % 2 := by
  obtain ⟨m, hm⟩ := even_sum_degrees G
  have hle : ∑ v, G.degree v ≤ ∑ v, d v := Finset.sum_le_sum (fun v _ => hbound v)
  rw [deficiencyFun_eq G d hbound]
  omega

/-- **Odd target sum ⇒ odd deficiency.** If `∑_v d v` is odd then the target-function
deficiency is odd (the non-constant analogue of `deficiency_odd`). -/
theorem deficiencyFun_odd (d : V → ℕ) (hbound : ∀ v, G.degree v ≤ d v)
    (hodd : Odd (∑ v, d v)) : Odd (deficiencyFun G d) := by
  rw [Nat.odd_iff] at hodd ⊢
  rw [deficiencyFun_parity G d hbound, hodd]

/-- **Minimal deficiency `≥ 1` for a prescribed target.** When `∑_v d v` is odd,
every graph with `deg ≤ d` pointwise has target deficiency at least `1`: the degree
sequence cannot be met. -/
theorem one_le_deficiencyFun (d : V → ℕ) (hbound : ∀ v, G.degree v ≤ d v)
    (hodd : Odd (∑ v, d v)) : 1 ≤ deficiencyFun G d := by
  obtain ⟨k, hk⟩ := deficiencyFun_odd G d hbound hodd
  omega

/-- **Odd-sum degree sequences are not graphical.** No graph realises a prescribed
degree target `d : V → ℕ` exactly (`deg v = d v` for every `v`) when the target sum
`∑_v d v` is odd. This is the classical parity necessary condition for a degree
sequence to be graphical; it subsumes `not_isRegularOfDegree_of_odd_mul` (the
constant target `d v = d`, whose sum is `n·d`). Unlike the deficiency bounds it needs
no `deg ≤ d` hypothesis — exact realisation already forces the sums equal. -/
theorem not_forall_degree_eq_of_odd_sum (d : V → ℕ) (hodd : Odd (∑ v, d v)) :
    ¬ (∀ v, G.degree v = d v) := by
  intro hreg
  have hsum : ∑ v, G.degree v = ∑ v, d v := Finset.sum_congr rfl (fun v _ => hreg v)
  have heven : Even (∑ v, d v) := hsum ▸ even_sum_degrees G
  obtain ⟨a, ha⟩ := hodd
  obtain ⟨b, hb⟩ := heven
  omega

end HandshakeLemmaOQ01
