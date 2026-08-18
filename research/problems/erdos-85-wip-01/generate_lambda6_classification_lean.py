#!/usr/bin/env python3
"""Generate the Lean bit-vector completeness certificate for the lambda-six census."""

from __future__ import annotations

import argparse
import itertools
from pathlib import Path

import z3


N = 16


def cycle_matrix(parts: tuple[int, ...]) -> list[list[int]]:
    matrix = [[0] * N for _ in range(N)]
    start = 0
    for length in parts:
        for index in range(length):
            u, v = start + index, start + (index + 1) % length
            matrix[u][v] = matrix[v][u] = 1
        start += length
    return matrix


def square(matrix: list[list[int]]) -> list[list[int]]:
    return [[sum(matrix[u][w] * matrix[w][v] for w in range(N))
             for v in range(N)] for u in range(N)]


def bit_matrix(matrix: list[list[int]], *, support: bool = False) -> int:
    value = 0
    for u in range(N):
        for v in range(N):
            entry = matrix[u][v] != 0 if support else matrix[u][v] == 1
            if entry:
                value |= 1 << (16 * u + v)
    return value


def enumerate_r(parts: tuple[int, ...]) -> tuple[int, int, list[int]]:
    h = cycle_matrix(parts)
    h2 = square(h)
    pairs = list(itertools.combinations(range(N), 2))
    variables = {pair: z3.Bool(f"r_{parts}_{pair}") for pair in pairs}

    def r(u: int, v: int) -> z3.BoolRef:
        if u == v:
            return z3.BoolVal(False)
        return variables[min(u, v), max(u, v)]

    solver = z3.Solver()
    for u, v in pairs:
        if h2[u][v]:
            solver.add(z3.Not(r(u, v)))
    for u in range(N):
        solver.add(z3.PbEq([(r(u, v), 1) for v in range(N) if u != v], 6))
    for u in range(N):
        for v in range(N):
            solver.add(
                z3.Sum([z3.If(r(u, w), h[w][v], 0) for w in range(N)])
                == z3.Sum([z3.If(r(w, v), h[u][w], 0) for w in range(N)])
            )

    models: list[int] = []
    while solver.check() == z3.sat:
        model = solver.model()
        bits = {pair: z3.is_true(model.eval(variable, model_completion=True))
                for pair, variable in variables.items()}
        value = 0
        for (u, v), present in bits.items():
            if present:
                value |= 1 << (16 * u + v)
                value |= 1 << (16 * v + u)
        models.append(value)
        solver.add(z3.Or([
            z3.Not(variables[pair]) if present else variables[pair]
            for pair, present in bits.items()
        ]))
    return bit_matrix(h), bit_matrix(h2, support=True), sorted(models)


def hex256(value: int) -> str:
    return f"0x{value:064x}"


def emit_models(name: str, models: list[int]) -> str:
    rows = [f"  {hex256(value)}" for value in models]
    return f"def {name} : List (BitVec 256) := [\n" + ",\n".join(rows) + "\n]\n"


def generate() -> str:
    h106, h2_106, models106 = enumerate_r((10, 6))
    h5533, h2_5533, models5533 = enumerate_r((5, 5, 3, 3))
    assert len(models106) == 144 and len(models5533) == 360
    return f'''import Proofs.Erdos85SignedSRGBridge

/-! # Kernel-checked completeness of the lambda-six labeled R census -/

namespace Erdos85

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

def lambdaSixAdmissibleR (h h2 r : BitVec 256) : Prop :=
  (∀ x : Fin 16, bitAdj256 r x x = false) ∧
  (∀ x y : Fin 16, bitAdj256 r x y = bitAdj256 r y x) ∧
  (∀ x : Fin 16, (row256 r x).cpop = 6) ∧
  (∀ x y : Fin 16, bitAdj256 r x y = true → bitAdj256 h2 x y = false) ∧
  (∀ x y : Fin 16,
    ((row256 r x) &&& (row256 h y)).cpop =
      ((row256 h x) &&& (row256 r y)).cpop)

def lambdaSixTenSixH256 : BitVec 256 := {hex256(h106)}
def lambdaSixTenSixH2Support256 : BitVec 256 := {hex256(h2_106)}
def lambdaSixFiveFiveThreeThreeH256 : BitVec 256 := {hex256(h5533)}
def lambdaSixFiveFiveThreeThreeH2Support256 : BitVec 256 := {hex256(h2_5533)}

{emit_models("lambdaSixTenSixRModels", models106)}
{emit_models("lambdaSixFiveFiveThreeThreeRModels", models5533)}

theorem lambdaSixTenSixRModels_complete : ∀ r : BitVec 256,
    lambdaSixAdmissibleR lambdaSixTenSixH256 lambdaSixTenSixH2Support256 r →
      r ∈ lambdaSixTenSixRModels := by
  simp only [lambdaSixAdmissibleR, lambdaSixTenSixH256,
    lambdaSixTenSixH2Support256, lambdaSixTenSixRModels, bitAdj256, row256]
  simp (config := {{ maxSteps := 100000000 }}) [Fin.forall_fin_succ]
  bv_decide (config := {{ timeout := 600 }})

theorem lambdaSixFiveFiveThreeThreeRModels_complete : ∀ r : BitVec 256,
    lambdaSixAdmissibleR lambdaSixFiveFiveThreeThreeH256
      lambdaSixFiveFiveThreeThreeH2Support256 r →
      r ∈ lambdaSixFiveFiveThreeThreeRModels := by
  simp only [lambdaSixAdmissibleR, lambdaSixFiveFiveThreeThreeH256,
    lambdaSixFiveFiveThreeThreeH2Support256,
    lambdaSixFiveFiveThreeThreeRModels, bitAdj256, row256]
  simp (config := {{ maxSteps := 100000000 }}) [Fin.forall_fin_succ]
  bv_decide (config := {{ timeout := 600 }})

end Erdos85
'''


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("output", type=Path)
    args = parser.parse_args()
    args.output.write_text(generate())


if __name__ == "__main__":
    main()
