import Proofs.Erdos85ThreeHighCrossRelabeling
import Proofs.Erdos85ThreeBlockOrbitCertificate
import Proofs.Erdos85ThreeHighTriangleTables

namespace Erdos85
attribute [local irreducible] threeHighCrossDomain

theorem threeHighCrossDomain_U_c4
    (U : Fin 15 → Fin 15 → Bool) (R : Fin 8 → Fin 8 → Bool)
    (cross : ThreeHighCross) (hc : cross ∈ threeHighCrossDomain U R) :
    encodedC4Free U = true := by
  have hinj : Function.Injective threeHighEmptyUIndex := by
    intro x y h
    apply Fin.ext
    simpa only [threeHighEmptyUIndex,Fin.val_castAdd] using
      congrArg (fun a : Fin 24 => a.val) h
  have h := encodedC4Free_comap_injective (threeHighEmptyAdj U R cross)
    threeHighEmptyUIndex hinj ((mem_threeHighCrossDomain_iff U R cross).mp hc).1
  simpa only [threeHighEmptyAdj,threeHighEmptySplit_u] using h

/-- A checked cycle-or-orbit certificate into excluded representatives rules out
all cross completions. The cycle branch needs no separate C4-free hypothesis. -/
theorem ThreeBlockOrbitCertificate.no_cross {n : Nat}
    (U : Fin 15 → Fin 15 → Bool) (reps : Fin n → Fin 15 → Fin 15 → Bool)
    (cert : ThreeBlockOrbitCertificate n) (hcert : cert.Valid U reps)
    (R : Fin 8 → Fin 8 → Bool)
    (hreps : ∀ i (cross : ThreeHighCross), cross ∉ threeHighCrossDomain (reps i) R)
    (cross : ThreeHighCross) : cross ∉ threeHighCrossDomain U R := by
  intro hc
  obtain ⟨i,p,sw,hU⟩ := cert.covered U reps hcert (threeHighCrossDomain_U_c4 U R cross hc)
  exact threeHighCrossDomain_no_cross_of_relabel U (reps i) R
    (threeBlockOrbitLabel p sw) hU (hreps i) cross hc

theorem threeHighFullTriangleOrbit_no_cross
    (U : Fin 15 → Fin 15 → Bool) (cert : ThreeBlockOrbitCertificate 4)
    (hcert : cert.Valid U threeHighFullTriangleTableAdj)
    (R : Fin 8 → Fin 8 → Bool) (cross : ThreeHighCross) :
    cross ∉ threeHighCrossDomain U R :=
  cert.no_cross U threeHighFullTriangleTableAdj hcert R
    (fun i c => threeHighFullTriangleTable_no_cross i R c) cross

theorem threeHighDeficientTriangleOrbit_no_cross
    (U : Fin 15 → Fin 15 → Bool) (cert : ThreeBlockOrbitCertificate 35)
    (hcert : cert.Valid U threeHighDeficientTriangleTableAdj)
    (R : Fin 8 → Fin 8 → Bool) (cross : ThreeHighCross) :
    cross ∉ threeHighCrossDomain U R :=
  cert.no_cross U threeHighDeficientTriangleTableAdj hcert R
    (fun i c => threeHighDeficientTriangleTable_no_cross i R c) cross

end Erdos85
#print axioms Erdos85.threeHighCrossDomain_U_c4
#print axioms Erdos85.ThreeBlockOrbitCertificate.no_cross
#print axioms Erdos85.threeHighFullTriangleOrbit_no_cross
#print axioms Erdos85.threeHighDeficientTriangleOrbit_no_cross
