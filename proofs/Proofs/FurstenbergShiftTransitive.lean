/-
# Furstenberg Correspondence OQ-01 (incomplete-01) → OQ-01: An Explicit Transitive Point

## What This File Contains

The parent file `FurstenbergShiftChaos` proves the shift `T : {0,1}^ℕ → {0,1}^ℕ`,
`T(x)(n) = x(n+1)` is **chaotic in the sense of Devaney**.  Its topological-transitivity
condition is stated in the *mixing* form: for **each pair** of nonempty open sets `U, V`
there is *some* point of `U` whose orbit later enters `V` (witnessed by an ad-hoc `bridge`
point depending on `U` and `V`).

This file proves the genuinely stronger **Birkhoff transitivity** statement, which the
parent listed as its first next step: there is a *single* point `z` whose entire forward
orbit `{T^t z : t ∈ ℕ}` is **dense** in Cantor space.  Such a point is called a
*transitive point*, and the underlying sequence a *universal* or *disjunctive* sequence —
one in which **every finite word occurs as a factor**.

The construction is completely explicit and constructive:

* `enum : ℕ → List Bool` is a surjective enumeration of all finite binary words
  (via `Encodable`).
* `z` is the infinite concatenation `block 0 ++ block 1 ++ block 2 ++ …`, where
  `block k = enum k ++ [false]` (the one-bit pad makes every block nonempty so the
  `n`-th bit of `z` is always read from a long-enough finite prefix).
* Because `enum` is surjective, every word `w` equals `enum k` for some `k`, and `w`
  appears in `z` starting at the offset where block `k` begins.  Hence `z` is disjunctive,
  and its orbit meets every nonempty open set, i.e. is dense.

The headline results are `disjunctive`, `dense_orbit`, and `exists_transitive_point`.
Everything is proved with **0 axioms and 0 sorries**.

## Why this is more than the parent's mixing condition

Mixing gives, *separately for every target*, a tailor-made starting point.  A transitive
point is a *uniform* witness: one orbit that is dense, simultaneously approximating every
configuration.  By the Birkhoff transitivity theorem the two notions coincide on a
perfect Polish space like Cantor space, but exhibiting the explicit universal sequence is
the constructive content — and it is exactly the symbolic object (a disjunctive / "rich"
sequence) underlying normality and the topological route to recurrence.

## References

- G. D. Birkhoff, *Dynamical Systems* (1927) — transitive points.
- R. L. Devaney, *An Introduction to Chaotic Dynamical Systems* (1989).
- H. Furstenberg, *Recurrence in Ergodic Theory and Combinatorial Number Theory* (1981).
-/
import Mathlib
import Proofs.FurstenbergShiftChaos

namespace FurstenbergShiftTransitive

open Set Topology Function FurstenbergShiftChaos

/-! ═══════════════════════════════════════════════════════════════════════════════
PART I: A SURJECTIVE ENUMERATION OF ALL FINITE WORDS
═══════════════════════════════════════════════════════════════════════════════ -/

/-- A surjective enumeration of all finite binary words, via `Encodable (List Bool)`. -/
def enum (k : ℕ) : List Bool := (Encodable.decode (α := List Bool) k).getD []

/-- Every finite word is hit by `enum`. -/
theorem enum_surjective (w : List Bool) : ∃ k, enum k = w :=
  ⟨Encodable.encode w, by simp [enum, Encodable.encodek]⟩

/-! ═══════════════════════════════════════════════════════════════════════════════
PART II: THE UNIVERSAL (DISJUNCTIVE) SEQUENCE
═══════════════════════════════════════════════════════════════════════════════ -/

/-- The `k`-th padded block: the `k`-th word followed by one separator bit.  Padding makes
    every block nonempty (length ≥ 1) without disturbing occurrences of the actual words. -/
def block (k : ℕ) : List Bool := enum k ++ [false]

theorem block_length (k : ℕ) : (block k).length = (enum k).length + 1 := by
  simp [block]

/-- The length-`k` initial concatenation `block 0 ++ block 1 ++ … ++ block (k-1)`. -/
def concatPrefix : ℕ → List Bool
  | 0 => []
  | k + 1 => concatPrefix k ++ block k

theorem concatPrefix_succ (k : ℕ) :
    concatPrefix (k + 1) = concatPrefix k ++ block k := rfl

/-- Offset at which block `k` begins in the infinite concatenation. -/
def offset (k : ℕ) : ℕ := (concatPrefix k).length

theorem offset_succ (k : ℕ) : offset (k + 1) = offset k + (enum k).length + 1 := by
  unfold offset
  rw [concatPrefix_succ, List.length_append, block_length]
  omega

/-- Every block has length ≥ 1, so the offsets are at least the index. -/
theorem le_offset (k : ℕ) : k ≤ offset k := by
  induction k with
  | zero => simp [offset, concatPrefix]
  | succ k ih => rw [offset_succ]; omega

/-- The finite concatenations are nested: a longer one extends a shorter one. -/
theorem concatPrefix_add (a d : ℕ) :
    ∃ t, concatPrefix (a + d) = concatPrefix a ++ t := by
  induction d with
  | zero => exact ⟨[], by simp⟩
  | succ d ih =>
    obtain ⟨t, ht⟩ := ih
    refine ⟨t ++ block (a + d), ?_⟩
    rw [show a + (d + 1) = (a + d) + 1 from by omega, concatPrefix_succ, ht,
      List.append_assoc]

theorem concatPrefix_prefix {a b : ℕ} (h : a ≤ b) :
    ∃ t, concatPrefix b = concatPrefix a ++ t := by
  obtain ⟨d, rfl⟩ := Nat.le.dest h
  exact concatPrefix_add a d

/-- **Prefix stability.** The bit at any index that is already realized in two finite
    concatenations is the same in both — concatenations agree wherever both are defined. -/
theorem getD_concatPrefix_stable {a b n : ℕ} (ha : n < offset a) (hb : n < offset b) :
    (concatPrefix a).getD n false = (concatPrefix b).getD n false := by
  rcases le_total a b with hab | hab
  · obtain ⟨t, ht⟩ := concatPrefix_prefix hab
    rw [ht, List.getD_append _ _ _ _ ha]
  · obtain ⟨t, ht⟩ := concatPrefix_prefix hab
    rw [ht, List.getD_append _ _ _ _ hb]

/-- The universal sequence: the infinite concatenation `block 0 block 1 block 2 …`.
    Bit `n` is read off from the finite prefix `concatPrefix (n+1)`, which is long enough
    because every block has length ≥ 1. -/
def z : Cantor := fun n => (concatPrefix (n + 1)).getD n false

theorem lt_offset_succ (n : ℕ) : n < offset (n + 1) :=
  lt_of_lt_of_le (Nat.lt_succ_self n) (le_offset (n + 1))

/-- Reading bit `n` of `z` from any sufficiently long finite prefix gives the same value. -/
theorem z_eq (n N : ℕ) (h : n < offset N) : z n = (concatPrefix N).getD n false := by
  rw [z]
  exact getD_concatPrefix_stable (lt_offset_succ n) h

/-- **Occurrence lemma.** The word `enum k` appears in `z` starting at `offset k`. -/
theorem occ (k j : ℕ) (hj : j < (enum k).length) :
    z (offset k + j) = (enum k).getD j false := by
  have hlt : offset k + j < offset (k + 1) := by rw [offset_succ]; omega
  have hle : (concatPrefix k).length ≤ offset k + j := Nat.le_add_right _ _
  rw [z_eq _ (k + 1) hlt, concatPrefix_succ, List.getD_append_right _ _ _ _ hle]
  have hidx : offset k + j - (concatPrefix k).length = j := by
    show offset k + j - offset k = j
    omega
  rw [hidx, block]
  exact List.getD_append (enum k) [false] false j hj

/-! ═══════════════════════════════════════════════════════════════════════════════
PART III: `z` IS DISJUNCTIVE, AND ITS ORBIT IS DENSE
═══════════════════════════════════════════════════════════════════════════════ -/

/-- **`z` is disjunctive.** Every finite word occurs as a factor of `z`: there is a
    starting position `t` at which `z` reads off `w`. -/
theorem disjunctive (w : List Bool) :
    ∃ t, ∀ i, i < w.length → z (t + i) = w.getD i false := by
  obtain ⟨k, hk⟩ := enum_surjective w
  refine ⟨offset k, fun i hi => ?_⟩
  have hilen : i < (enum k).length := by rw [hk]; exact hi
  rw [occ k i hilen, hk]

/-- For every nonempty open set, some forward iterate of `z` lands in it. -/
theorem orbit_mem (U : Set Cantor) (hU : IsOpen U) (hUne : U.Nonempty) :
    ∃ t, shift^[t] z ∈ U := by
  obtain ⟨y, hy⟩ := hUne
  obtain ⟨m, hsub⟩ := exists_cyl_subset hU hy
  obtain ⟨k, hk⟩ := enum_surjective (prefixWord y m)
  refine ⟨offset k, hsub ((mem_Cyl_prefixWord_iff _ y m).mpr ?_)⟩
  intro i hi
  have hilen : i < (enum k).length := by rw [hk, prefixWord_length]; exact hi
  rw [shift_iterate, Nat.add_comm i (offset k), occ k i hilen, hk,
    prefixWord_getD y m i hi]

/-- **An explicit transitive point.** The forward orbit of the disjunctive sequence `z`
    is dense in Cantor space.  This is the Birkhoff transitivity strengthening of the
    parent's mixing condition: a *single* universal point, not a target-dependent one. -/
theorem dense_orbit : Dense (Set.range (fun t : ℕ => shift^[t] z)) := by
  rw [dense_iff_inter_open]
  intro U hU hUne
  obtain ⟨t, ht⟩ := orbit_mem U hU hUne
  exact ⟨shift^[t] z, ht, t, rfl⟩

/-- **Existence of a transitive point.** The shift on Cantor space has a point whose
    forward orbit is dense — exhibited explicitly as the universal sequence `z`. -/
theorem exists_transitive_point :
    ∃ x : Cantor, Dense (Set.range (fun t : ℕ => shift^[t] x)) :=
  ⟨z, dense_orbit⟩

-- Axiom audit: should report only `propext`, `Classical.choice`, `Quot.sound`.
#print axioms exists_transitive_point

end FurstenbergShiftTransitive
