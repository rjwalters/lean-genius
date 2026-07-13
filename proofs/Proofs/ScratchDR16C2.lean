import Mathlib

open Polynomial

set_option trace.Meta.synthInstance true in
example : Normal ℚ ((X : ℚ[X]) ^ 4 - C 2).SplittingField := inferInstance
