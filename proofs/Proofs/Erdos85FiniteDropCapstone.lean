import Proofs.Erdos85FiniteDropCore

/-!
# Erdős 85 finite-drop capstone slot

Before certificate completion this module re-exports only the conditional core.
The reviewed final generator replaces this file with the unconditional H1/H3/
H5/H7 certificate assembly. All reusable consumers import the core directly,
so that replacement cannot create an import cycle.
-/
