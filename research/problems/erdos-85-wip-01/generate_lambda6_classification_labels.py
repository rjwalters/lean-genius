#!/usr/bin/env python3
"""Generate checked relabeling tables for the lambda-six labeled census."""

from __future__ import annotations

import argparse
from pathlib import Path

import networkx as nx

from generate_lambda6_classification_lean import N, enumerate_r, square, cycle_matrix


def edges_of_mask(mask: int) -> list[tuple[int, int]]:
    return [(u, v) for u in range(N) for v in range(u + 1, N)
            if (mask >> (16 * u + v)) & 1]


def defect_mask(h2_support: int, r: int) -> int:
    return ((1 << 256) - 1) ^ (h2_support | r)


def graph_of_mask(mask: int) -> nx.Graph:
    graph = nx.Graph()
    graph.add_nodes_from(range(N))
    graph.add_edges_from(edges_of_mask(mask))
    return graph


def triangle_count(graph: nx.Graph) -> int:
    return sum(nx.triangles(graph).values()) // 3


def labels_for(parts: tuple[int, ...]):
    _, h2_support, models = enumerate_r(parts)
    defects = [defect_mask(h2_support, r) for r in models]
    graphs = [graph_of_mask(d) for d in defects]
    representatives: dict[int, tuple[int, nx.Graph]] = {}
    for d, graph in zip(defects, graphs):
        triangles = triangle_count(graph)
        tag = 0 if nx.is_bipartite(graph) else 1 if triangles == 30 else 2
        representatives.setdefault(tag, (d, graph))
    assert set(representatives) == {0, 1, 2}

    labels = []
    for graph in graphs:
        triangles = triangle_count(graph)
        tag = 0 if nx.is_bipartite(graph) else 1 if triangles == 30 else 2
        target = representatives[tag][1]
        matcher = nx.algorithms.isomorphism.GraphMatcher(graph, target)
        assert matcher.is_isomorphic()
        permutation = tuple(matcher.mapping[index] for index in range(N))
        assert sorted(permutation) == list(range(N))
        labels.append((tag, permutation))
    return representatives, labels


def hex256(value: int) -> str:
    return f"0x{value:064x}"


def emit_labels(name: str, labels) -> str:
    rows = []
    for tag, permutation in labels:
        vector = ", ".join(map(str, permutation))
        rows.append(f"  ({tag}, ![{vector}])")
    return f"def {name} : Fin {len(labels)} → (Fin 3 × (Fin 16 → Fin 16)) := ![\n" + ",\n".join(rows) + "\n]\n"


def generate() -> str:
    reps106, labels106 = labels_for((10, 6))
    reps5533, labels5533 = labels_for((5, 5, 3, 3))
    return f'''import Proofs.Erdos85LambdaSixClassificationSAT

/-! # Checked class labels for the lambda-six labeled census -/

namespace Erdos85

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

def lambdaSixForcedDefect (h2 r : BitVec 256) : BitVec 256 :=
  ~~~(h2 ||| r)

def lambdaSixRelabelsTo
    (d target : BitVec 256) (p : Fin 16 → Fin 16) : Prop :=
  (∀ x y : Fin 16, p x = p y → x = y) ∧
  ∀ x y : Fin 16, bitAdj256 d x y = bitAdj256 target (p x) (p y)

instance lambdaSixRelabelsTo_decidable
    (d target : BitVec 256) (p : Fin 16 → Fin 16) :
    Decidable (lambdaSixRelabelsTo d target p) := by
  unfold lambdaSixRelabelsTo
  infer_instance

def lambdaSixRelabelsToBool
    (d target : BitVec 256) (p : Fin 16 → Fin 16) : Bool :=
  (List.ofFn p).Nodup &&
  (List.ofFn fun x : Fin 16 =>
    (List.ofFn fun y : Fin 16 =>
      bitAdj256 d x y == bitAdj256 target (p x) (p y)).all id).all id

def lambdaSixTenSixBipartiteD : BitVec 256 := {hex256(reps106[0][0])}
def lambdaSixFiveFiveThreeThreeBipartiteD : BitVec 256 := {hex256(reps5533[0][0])}

def lambdaSixTenSixDTarget : Fin 3 → BitVec 256 := ![
  lambdaSixTenSixBipartiteD,
  {hex256(reps106[1][0])},
  {hex256(reps106[2][0])}
]

def lambdaSixFiveFiveThreeThreeDTarget : Fin 3 → BitVec 256 := ![
  lambdaSixFiveFiveThreeThreeBipartiteD,
  {hex256(reps5533[1][0])},
  {hex256(reps5533[2][0])}
]

{emit_labels("lambdaSixTenSixRModelLabels", labels106)}
{emit_labels("lambdaSixFiveFiveThreeThreeRModelLabels", labels5533)}

def lambdaSixTenSixRModelLabelsCheck : Bool :=
  (List.ofFn fun i : Fin 144 =>
    let label := lambdaSixTenSixRModelLabels i
    lambdaSixRelabelsToBool
      (lambdaSixForcedDefect lambdaSixTenSixH2Support256
        (lambdaSixTenSixRModels.getD i.val 0))
      (lambdaSixTenSixDTarget label.1) label.2).all id

def lambdaSixFiveFiveThreeThreeRModelLabelsCheck : Bool :=
  (List.ofFn fun i : Fin 360 =>
    let label := lambdaSixFiveFiveThreeThreeRModelLabels i
    lambdaSixRelabelsToBool
      (lambdaSixForcedDefect lambdaSixFiveFiveThreeThreeH2Support256
        (lambdaSixFiveFiveThreeThreeRModels.getD i.val 0))
      (lambdaSixFiveFiveThreeThreeDTarget label.1) label.2).all id

theorem lambdaSixTenSixRModelLabels_correct :
    lambdaSixTenSixRModelLabelsCheck = true := by
  decide

theorem lambdaSixFiveFiveThreeThreeRModelLabels_correct :
    lambdaSixFiveFiveThreeThreeRModelLabelsCheck = true := by
  decide

end Erdos85
'''


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("output", type=Path)
    args = parser.parse_args()
    args.output.write_text(generate())


if __name__ == "__main__":
    main()
