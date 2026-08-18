import Proofs.Erdos85ThirtyTwoQuotient

/-!
# Finite signing obstructions at parameters `(16,6,2,2)`

This file checks the propositional parity certificates behind the last finite
step at order 32.  A quotient containing a `K₄` is impossible to sign by three
four-cycle equations.  The Shrikhande-type local configuration has an
11-equation certificate.
-/

namespace Erdos85

open SimpleGraph

set_option maxHeartbeats 10000000

/-- Three negative four-cycles on a `K₄` are inconsistent. -/
theorem not_isNegativeSignedSRG1622_of_k4
    {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj]
    (s : V → V → Prop)
    {a b c d : V}
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d)
    (Aab : H.Adj a b) (Aac : H.Adj a c) (Aad : H.Adj a d)
    (Abc : H.Adj b c) (Abd : H.Adj b d) (Acd : H.Adj c d) :
    ¬ IsNegativeSignedSRG1622 H s := by
  rintro ⟨_, _, _, hsym, hneg⟩
  have eab := hneg hab hcd Aac Abc.symm Aad Abd.symm
  have eac := hneg hac hbd Aab Abc Aad Acd.symm
  have ead := hneg had hbc Aab Abd Aac Acd
  simp only [hsym] at eab eac ead
  simp only [Xor] at eab eac ead
  grind

/-- The eleven endpoint/common-neighbor quadruples in the Shrikhande signing
certificate.  An entry `(x,y,u,v)` represents the negative four-cycle with
endpoints `x,y` and common neighbors `u,v`. -/
def shrikhandeNegativeCertificate : List (Fin 11 × Fin 11 × Fin 11 × Fin 11) :=
  [(0,1,2,5), (0,9,1,4), (0,6,1,2), (0,7,4,3), (0,10,3,5),
   (1,9,6,8), (1,6,9,2), (1,10,5,8), (9,3,4,7), (9,10,7,8),
   (4,10,3,7)]

/-- Edge condition needed by a certificate quadruple. -/
def SupportsNegativeQuadruple {V : Type*} (H : SimpleGraph V)
    (f : Fin 11 → V) (t : Fin 11 × Fin 11 × Fin 11 × Fin 11) : Prop :=
  H.Adj (f t.1) (f t.2.2.1) ∧
  H.Adj (f t.2.2.1) (f t.2.1) ∧
  H.Adj (f t.1) (f t.2.2.2) ∧
  H.Adj (f t.2.2.2) (f t.2.1)

/-- The eleven Shrikhande parity equations are jointly inconsistent. -/
theorem not_isNegativeSignedSRG1622_of_shrikhandeCertificate
    {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj]
    (s : V → V → Prop)
    (f : Fin 11 → V) (hinj : Function.Injective f)
    (hsupport : ∀ t ∈ shrikhandeNegativeCertificate,
      SupportsNegativeQuadruple H f t) :
    ¬ IsNegativeSignedSRG1622 H s := by
  rintro ⟨_, _, _, hsym, hneg⟩
  have neg (x y u v : Fin 11)
      (hxy : x ≠ y) (huv : u ≠ v)
      (hs : SupportsNegativeQuadruple H f (x, y, u, v)) :
      Xor ((s (f x) (f u) ↔ s (f u) (f y)))
        (s (f x) (f v) ↔ s (f v) (f y)) := by
    exact hneg (hinj.ne hxy) (hinj.ne huv) hs.1 hs.2.1 hs.2.2.1 hs.2.2.2
  have e0 := neg 0 1 2 5 (by decide) (by decide)
    (hsupport (0,1,2,5) (by native_decide))
  have e1 := neg 0 9 1 4 (by decide) (by decide)
    (hsupport (0,9,1,4) (by native_decide))
  have e2 := neg 0 6 1 2 (by decide) (by decide)
    (hsupport (0,6,1,2) (by native_decide))
  have e3 := neg 0 7 4 3 (by decide) (by decide)
    (hsupport (0,7,4,3) (by native_decide))
  have e4 := neg 0 10 3 5 (by decide) (by decide)
    (hsupport (0,10,3,5) (by native_decide))
  have e5 := neg 1 9 6 8 (by decide) (by decide)
    (hsupport (1,9,6,8) (by native_decide))
  have e6 := neg 1 6 9 2 (by decide) (by decide)
    (hsupport (1,6,9,2) (by native_decide))
  have e7 := neg 1 10 5 8 (by decide) (by decide)
    (hsupport (1,10,5,8) (by native_decide))
  have e8 := neg 9 3 4 7 (by decide) (by decide)
    (hsupport (9,3,4,7) (by native_decide))
  have e9 := neg 9 10 7 8 (by decide) (by decide)
    (hsupport (9,10,7,8) (by native_decide))
  have e10 := neg 4 10 3 7 (by decide) (by decide)
    (hsupport (4,10,3,7) (by native_decide))
  simp only [hsym] at e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10
  simp only [Xor] at e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10
  clear neg hneg hsym hsupport hinj
  grind (splits := 100)

/-- A graph contains the complete four-vertex obstruction. -/
def HasK4 {V : Type*} (H : SimpleGraph V) : Prop :=
  ∃ a b c d : V,
    a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d ∧
    H.Adj a b ∧ H.Adj a c ∧ H.Adj a d ∧
    H.Adj b c ∧ H.Adj b d ∧ H.Adj c d

/-- A graph contains the eleven named vertices supporting the Shrikhande
parity certificate. -/
def HasShrikhandeNegativeCertificate {V : Type*} (H : SimpleGraph V) : Prop :=
  ∃ f : Fin 11 → V, Function.Injective f ∧
    ∀ t ∈ shrikhandeNegativeCertificate, SupportsNegativeQuadruple H f t

/-- The purely graph-theoretic classification statement left after extracting
the two finite parity obstructions. -/
def SRG1622CertificateDichotomy : Prop :=
  ∀ (V : Type) [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj],
    Fintype.card V = 16 →
    (∀ x : V, H.degree x = 6) →
    (∀ x y : V, x ≠ y →
      (H.neighborFinset x ∩ H.neighborFinset y).card = 2) →
    HasK4 H ∨ HasShrikhandeNegativeCertificate H

/-- The certificate dichotomy proves the finite non-signing statement needed
for the exact order-32 result. -/
theorem noNegativeSigning1622_of_certificateDichotomy
    (hdichotomy : SRG1622CertificateDichotomy) :
    NoNegativeSigning1622 := by
  intro V _ _ H _ s hsign
  rcases hsign with ⟨hcard, hreg, hcommon, hsym, hneg⟩
  have hshape := hdichotomy V H hcard hreg hcommon
  rcases hshape with hk4 | hshr
  · rcases hk4 with ⟨a, b, c, d, hab, hac, had, hbc, hbd, hcd,
      Aab, Aac, Aad, Abc, Abd, Acd⟩
    exact not_isNegativeSignedSRG1622_of_k4 H s hab hac had hbc hbd hcd
      Aab Aac Aad Abc Abd Acd ⟨hcard, hreg, hcommon, hsym, hneg⟩
  · rcases hshr with ⟨f, hinj, hsupport⟩
    exact not_isNegativeSignedSRG1622_of_shrikhandeCertificate H s f hinj hsupport
      ⟨hcard, hreg, hcommon, hsym, hneg⟩

end Erdos85
