import Mathlib

/-!
# Four-leaf chord coordinates and the pivot-pairing gauge

The simple shadow of the exceptional Baer interface is Eulerian on four
leaves.  Relative to the star spanning tree at leaf `0`, its three chord
coordinates determine all tree edges.  Its edge augmentation is the parity
of those three chords.

Changing a degree-four pivot pairing adds a Hamilton four-cycle.  The two
independent Hamilton shifts generate exactly the equal-parity fibers of the
three chord coordinates.  Consequently the augmentation `omega_Q` is the
sole pairing-gauge invariant.  This formalizes `(73rnz_bg)--(73rnz_bj)`.
-/

namespace Erdos85

/-- The three non-tree edges `12`, `13`, and `23` of the four-leaf complete
graph. -/
structure FourLeafChordVector where
  c12 : ZMod 2
  c13 : ZMod 2
  c23 : ZMod 2
deriving DecidableEq

@[ext]
theorem FourLeafChordVector.extensionality
    {q r : FourLeafChordVector}
    (h12 : q.c12 = r.c12) (h13 : q.c13 = r.c13) (h23 : q.c23 = r.c23) :
    q = r := by
  cases q
  cases r
  simp_all

/-- The full six edge coordinates of a four-leaf shadow. -/
structure FourLeafEdgeVector where
  e01 : ZMod 2
  e02 : ZMod 2
  e03 : ZMod 2
  e12 : ZMod 2
  e13 : ZMod 2
  e23 : ZMod 2
deriving DecidableEq

/-- Chord parity, the eventual pairing-invariant holonomy bit. -/
def FourLeafChordVector.parity (q : FourLeafChordVector) : ZMod 2 :=
  q.c12 + q.c13 + q.c23

/-- Eulerian reconstruction relative to the star tree
`{01,02,03}`. -/
def FourLeafChordVector.reconstruct (q : FourLeafChordVector) :
    FourLeafEdgeVector where
  e01 := q.c12 + q.c13
  e02 := q.c12 + q.c23
  e03 := q.c13 + q.c23
  e12 := q.c12
  e13 := q.c13
  e23 := q.c23

/-- Mod-two edge augmentation of the full shadow. -/
def FourLeafEdgeVector.augmentation (E : FourLeafEdgeVector) : ZMod 2 :=
  E.e01 + E.e02 + E.e03 + E.e12 + E.e13 + E.e23

/-- The four vertex-boundary equations defining an Eulerian shadow. -/
def FourLeafEdgeVector.IsEulerian (E : FourLeafEdgeVector) : Prop :=
  E.e01 + E.e02 + E.e03 = 0 ∧
  E.e01 + E.e12 + E.e13 = 0 ∧
  E.e02 + E.e12 + E.e23 = 0 ∧
  E.e03 + E.e13 + E.e23 = 0

private theorem f2_self_add (x : ZMod 2) : x + x = 0 := by
  have hchar : (2 : ZMod 2) = 0 := by decide
  rw [← two_mul, hchar, zero_mul]

private theorem f2_eq_add_of_add_add_eq_zero
    {x a b : ZMod 2} (h : x + a + b = 0) : x = a + b := by
  calc
    x = x + (a + a) + (b + b) := by simp [f2_self_add]
    _ = (x + a + b) + a + b := by ac_rfl
    _ = 0 + a + b := by rw [h]
    _ = a + b := by simp

/-- The three chord coordinates uniquely reconstruct every Eulerian
four-leaf shadow. -/
theorem FourLeafEdgeVector.eq_reconstruct_chords_of_isEulerian
    (E : FourLeafEdgeVector) (hE : E.IsEulerian) :
    E = FourLeafChordVector.reconstruct
      { c12 := E.e12, c13 := E.e13, c23 := E.e23 } := by
  rcases hE with ⟨_h0, h1, h2, h3⟩
  have he01 : E.e01 = E.e12 + E.e13 :=
    f2_eq_add_of_add_add_eq_zero h1
  have he02 : E.e02 = E.e12 + E.e23 :=
    f2_eq_add_of_add_add_eq_zero h2
  have he03 : E.e03 = E.e13 + E.e23 :=
    f2_eq_add_of_add_add_eq_zero h3
  cases E
  simp_all [FourLeafChordVector.reconstruct]

/-- For an Eulerian four-leaf shadow, total edge augmentation is exactly
the parity of the three chord coordinates. -/
theorem FourLeafChordVector.augmentation_reconstruct (q : FourLeafChordVector) :
    (q.reconstruct).augmentation = q.parity := by
  simp only [FourLeafChordVector.reconstruct, FourLeafEdgeVector.augmentation,
    FourLeafChordVector.parity]
  calc
    (q.c12 + q.c13) + (q.c12 + q.c23) + (q.c13 + q.c23) +
        q.c12 + q.c13 + q.c23 =
      q.c12 + (q.c12 + q.c12) +
        q.c13 + (q.c13 + q.c13) +
          q.c23 + (q.c23 + q.c23) := by ac_rfl
    _ = q.c12 + 0 + q.c13 + 0 + q.c23 + 0 := by
      rw [f2_self_add, f2_self_add, f2_self_add]
    _ = q.c12 + q.c13 + q.c23 := by simp

/-- The two independent Hamilton-cycle pairing shifts on chord
coordinates. -/
def FourLeafChordVector.gaugeShift
    (q : FourLeafChordVector) (a b : ZMod 2) : FourLeafChordVector where
  c12 := q.c12 + a + b
  c13 := q.c13 + a
  c23 := q.c23 + b

/-- Hamilton-cycle gauge changes preserve chord parity. -/
theorem FourLeafChordVector.parity_gaugeShift
    (q : FourLeafChordVector) (a b : ZMod 2) :
    (q.gaugeShift a b).parity = q.parity := by
  simp only [FourLeafChordVector.gaugeShift, FourLeafChordVector.parity]
  calc
    (q.c12 + a + b) + (q.c13 + a) + (q.c23 + b) =
      (q.c12 + q.c13 + q.c23) + (a + a) + (b + b) := by ac_rfl
    _ = (q.c12 + q.c13 + q.c23) + 0 + 0 := by
      rw [f2_self_add, f2_self_add]
    _ = q.c12 + q.c13 + q.c23 := by simp

/-- **Hamilton gauge orbit classification (`73rnz_bh--bj`).**  Two chord
vectors differ by pivot-pairing Hamilton cycles exactly when they have the
same parity. -/
theorem FourLeafChordVector.exists_gaugeShift_eq_iff_parity_eq
    (q r : FourLeafChordVector) :
    (∃ a b : ZMod 2, q.gaugeShift a b = r) ↔ q.parity = r.parity := by
  constructor
  · rintro ⟨a, b, rfl⟩
    exact (q.parity_gaugeShift a b).symm
  · intro hpar
    let a := q.c13 + r.c13
    let b := q.c23 + r.c23
    refine ⟨a, b, ?_⟩
    apply FourLeafChordVector.extensionality
    · simp only [FourLeafChordVector.gaugeShift, a, b]
      calc
        q.c12 + (q.c13 + r.c13) + (q.c23 + r.c23) =
          (q.c12 + q.c13 + q.c23) + (r.c13 + r.c23) := by ac_rfl
        _ = (r.c12 + r.c13 + r.c23) + (r.c13 + r.c23) := by
          exact congrArg (fun x => x + (r.c13 + r.c23)) hpar
        _ = r.c12 + (r.c13 + r.c13) + (r.c23 + r.c23) := by ac_rfl
        _ = r.c12 + 0 + 0 := by rw [f2_self_add, f2_self_add]
        _ = r.c12 := by simp
    · simp only [FourLeafChordVector.gaugeShift, a]
      calc
        q.c13 + (q.c13 + r.c13) = (q.c13 + q.c13) + r.c13 := by ac_rfl
        _ = 0 + r.c13 := by rw [f2_self_add]
        _ = r.c13 := zero_add _
    · simp only [FourLeafChordVector.gaugeShift, b]
      calc
        q.c23 + (q.c23 + r.c23) = (q.c23 + q.c23) + r.c23 := by ac_rfl
        _ = 0 + r.c23 := by rw [f2_self_add]
        _ = r.c23 := zero_add _

/-- Any quantity invariant under both pivot-pairing shifts is constant on,
and only needs to be defined on, the two parity fibers.  This is the precise
sense in which `omega_Q` is the sole surviving gauge class. -/
theorem FourLeafChordVector.invariant_eq_of_parity_eq
    {X : Type*} (f : FourLeafChordVector → X)
    (hinvariant : ∀ q a b, f (q.gaugeShift a b) = f q)
    {q r : FourLeafChordVector} (hpar : q.parity = r.parity) :
    f q = f r := by
  obtain ⟨a, b, hab⟩ :=
    (q.exists_gaugeShift_eq_iff_parity_eq r).2 hpar
  calc
    f q = f (q.gaugeShift a b) := (hinvariant q a b).symm
    _ = f r := by rw [hab]

end Erdos85

#print axioms Erdos85.FourLeafEdgeVector.eq_reconstruct_chords_of_isEulerian
#print axioms Erdos85.FourLeafChordVector.augmentation_reconstruct
#print axioms Erdos85.FourLeafChordVector.exists_gaugeShift_eq_iff_parity_eq
#print axioms Erdos85.FourLeafChordVector.invariant_eq_of_parity_eq
