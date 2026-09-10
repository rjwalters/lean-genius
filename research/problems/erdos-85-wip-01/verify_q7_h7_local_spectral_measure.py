"""Exact local spectral-measure relaxation check; no matrix or graph assertion."""
from fractions import Fraction as F
import json
from pathlib import Path

base = Path(__file__).parent
witness = json.loads((base / "q7_h7_local_spectral_measure.json").read_text())
global_measure = json.loads((base / "q7_h7_fifth_moment_measure.json").read_text())
nodes = list(map(F, witness["nodes"]))
assert nodes == list(map(F, global_measure["nodes"]))
# Diagonals of the residual spectral projector and powers 1, 2, 4.
m0 = [F(9, 10), F(208, 245), F(369, 490)]
m1 = [-F(3, 10), -F(11, 70), -F(9, 70)]
m2 = [F(28, 5), F(51, 10), F(22, 5)]
m4 = [F(399, 10), F(349, 10), F(291, 10)]
q3 = [F(77, 10), F(26, 5), F(33, 10)]
r_offset = [F(434, 5), F(603, 10), F(186, 5)]
ex = [0, 0, 1, 3, 4, 6]
census = [0, 0, 0]
columns = [F(0)] * len(nodes)
triangles = 0
mixed = F(0)
seen = set()
for group in witness["groups"]:
    t, tau, count = group["t"], group["tau"], group["count"]
    assert (t, tau, group["local_R"]) not in seen
    seen.add((t, tau, group["local_R"]))
    assert 0 <= t <= 2 and int(t == 0) <= tau <= 3 - t
    assert isinstance(count, int) and count >= 0
    weights = list(map(F, group["weights"]))
    assert len(weights) == len(nodes) and all(v >= 0 for v in weights)
    moments = [sum(v * x**k for v, x in zip(weights, nodes)) for k in range(6)]
    target = [m0[t], m1[t], m2[t], 2 * tau - q3[t], m4[t]]
    assert moments[:5] == [count * v for v in target]
    local_r = moments[5] + count * (r_offset[t] - 24 * tau)
    assert local_r == F(group["R"])
    assert isinstance(group["local_R"], int) and group["local_R"] % 2 == 0
    assert local_r == count * group["local_R"]
    assert 0 <= local_r <= 2 * count * ex[t + 2 * tau - 1]
    census[t] += count
    triangles += count * tau
    mixed += local_r
    columns = [a + b for a, b in zip(columns, weights)]
assert census == [7, 14, 21]
assert triangles == 3 * witness["T"] == 30
assert mixed == witness["R"] == global_measure["R"] == 96
assert columns == list(map(F, global_measure["weights"]))
print("PASS: exact local moments 0..4, local fifth-moment overlap bounds, even integral local overlaps, integer type census, and global measure; no matrix/graph witness")
