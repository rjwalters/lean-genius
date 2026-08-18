#!/usr/bin/env python3
"""Generate the Lean bit-vector completeness certificate for the 16-cycle census."""

from __future__ import annotations

import argparse
from pathlib import Path

from generate_lambda6_classification_lean import emit_models, enumerate_r, hex256


def generate() -> str:
    h, h2, models = enumerate_r((16,))
    assert len(models) == 392
    return f'''import Proofs.Erdos85LambdaSixClassificationSAT

/-! # Kernel-checked completeness of the Hamilton 16-cycle labeled R census -/

namespace Erdos85

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

def sixteenCycleH256 : BitVec 256 := {hex256(h)}
def sixteenCycleH2Support256 : BitVec 256 := {hex256(h2)}

{emit_models("sixteenCycleRModels", models)}

theorem sixteenCycleRModels_complete : ∀ r : BitVec 256,
    lambdaSixAdmissibleR sixteenCycleH256 sixteenCycleH2Support256 r →
      r ∈ sixteenCycleRModels := by
  simp only [lambdaSixAdmissibleR, sixteenCycleH256,
    sixteenCycleH2Support256, sixteenCycleRModels, bitAdj256, row256]
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
