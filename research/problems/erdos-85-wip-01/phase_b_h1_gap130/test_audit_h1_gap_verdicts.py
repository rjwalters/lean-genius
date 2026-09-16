import unittest
from unittest.mock import patch
import hashlib
import json
from pathlib import Path
import tempfile

import audit_h1_gap_verdicts as target


class H1GapVerdictAuditTests(unittest.TestCase):
    @staticmethod
    def synthetic_outside_receipt(run: Path, row: dict):
        case_id = row["id"]
        case = run / case_id
        native_dir = case / "materialization/native"
        solve_dir = case / "solve" / case_id
        native_dir.mkdir(parents=True)
        solve_dir.mkdir(parents=True)
        source = case / "materialization/one-row-source.json"
        source.write_bytes(target.adapter.one_row_manifest(row))
        _, table, _ = target.adapter.native.select_input(
            source, hashlib.sha256(source.read_bytes()).hexdigest(), case_id)
        (native_dir / "table.json").write_text(table)
        (native_dir / "check.log").write_text("MATCH (1 clauses, top 1)\n")
        cnf = native_dir / "input.cnf"
        cnf.write_bytes(b"p cnf 1 1\n1 0\n")
        cnf_hash = hashlib.sha256(cnf.read_bytes()).hexdigest()
        native = {"status": "materialized", "id": case_id,
                  "container_absent": True, "cnf_sha256": cnf_hash,
                  "cnf_bytes": cnf.stat().st_size,
                  "manifest_sha256": hashlib.sha256(source.read_bytes()).hexdigest(),
                  "tag": row["tag"], "profile": row["profile"],
                  "table_sha256": hashlib.sha256(table.encode()).hexdigest(),
                  "emitter_sha256": target.adapter.native.EMITTER_SHA256,
                  "image_id": target.adapter.native.IMAGE_ID,
                  "runner_sha256": target.adapter.NATIVE_SHA256,
                  "validator_sha256": "e" * 64,
                  "solver_launched": False,
                  "emit": {"returncode": 0}, "check": {"returncode": 0},
                  "variables": 1, "clauses": 1}
        native_raw = (json.dumps(native) + "\n").encode()
        (native_dir / "receipt.json").write_bytes(native_raw)
        binding = {"status": "materialized", "id": case_id,
                   "tag": row["tag"], "profile": row["profile"],
                   "capacity_local_index": row["capacity_local_index"],
                   "gap130_sha256": target.adapter.MANIFEST_SHA256,
                   "one_row_source_sha256": target.adapter.sha(target.adapter.one_row_manifest(row)),
                   "native_materializer_sha256": target.adapter.NATIVE_SHA256,
                   "adapter_source_sha256": target.summary.digest(Path(target.adapter.__file__).read_bytes()),
                   "freeze_source_sha256": target.summary.digest((target.HERE / "freeze.py").read_bytes()),
                   "native_receipt_sha256": hashlib.sha256(native_raw).hexdigest(),
                   "solver_launched": False, "cnf_sha256": cnf_hash,
                   "cnf_bytes": cnf.stat().st_size}
        for path in (case / "materialization/binding.json", case / "preparation.json"):
            path.write_text(json.dumps(binding))
        log = b"s UNSATISFIABLE\n"
        log_hash = hashlib.sha256(log).hexdigest()
        (solve_dir / "kissat.log").write_bytes(log)
        (solve_dir / "cadical.log").write_bytes(log)
        def solver(binary, kind, binary_hash):
            options = ["--time=14400"] if kind == "kissat" else ["-t", "14400"]
            return {"command": [binary, *options, str(cnf)],
                    "solver_sha256": binary_hash, "returncode": 20,
                    "stop_reason": None, "verdict": "UNSAT",
                    "log_sha256": log_hash, "log_bytes": len(log),
                    "proof_requested": False}
        solved = {"id": case_id, "sector": "H1", "status": "UNSAT_CROSSCHECKED",
                  "cnf_sha256": cnf_hash, "generator_commit": "d" * 40,
                  "primary": solver("/bin/kissat", "kissat", "b" * 64),
                  "crosscheck": solver("/bin/cadical", "cadical", "c" * 64)}
        (solve_dir / "result.json").write_text(json.dumps(solved))
        record = {"id": case_id, "sector": "H1", "status": "UNSAT_CROSSCHECKED",
                  "profile": row["profile"],
                  "capacity_local_index": row["capacity_local_index"],
                  "gap130_sha256": target.adapter.MANIFEST_SHA256,
                  "binding": binding, "solve": solved, "cnf_sha256": cnf_hash}
        (case / "result.json").write_text(json.dumps(record))
        state = {"h1_generator_commit": "d" * 40,
                 "config": {"tool_sha256": {"materialize_verdict_input.py": "e" * 64}},
                 "solvers": {"kissat": {"path": "/bin/kissat", "sha256": "b" * 64},
                             "cadical": {"path": "/bin/cadical", "sha256": "c" * 64}}}
        return state, record

    def test_dated_exact_join_is_1158_plus_96_plus_34(self):
        plan, _ = target.outside.select()
        gaps, residual, historical, outside = target.dated_gap_ids(
            plan, target.adapter.freeze()["rows"])
        self.assertEqual((len(gaps), len(residual), len(historical), len(outside)),
                         (1288, 1158, 96, 34))
        self.assertEqual(gaps, residual | historical | outside)

    def test_historical_evidence_does_not_count_as_fresh_dual_verdict(self):
        plan, _ = target.outside.select()
        _, residual, historical, outside = target.dated_gap_ids(
            plan, target.adapter.freeze()["rows"])
        phase_rows = [{"id": case["id"], "status":
                       "HISTORICAL_VERIFIED_UNSAT" if case["id"] in historical
                       else "UNSAT_CROSSCHECKED" if case["id"] in residual
                       else "NOT_RUN"} for case in plan["cases"]]
        base = {"rows": phase_rows, "runs": []}
        extra = {case_id: "UNSAT_CROSSCHECKED" for case_id in outside}
        with patch.object(target.summary, "summarize", return_value=base), \
             patch.object(target, "summarize_outside", return_value=(extra, [])):
            report = target.audit([], [])
        self.assertEqual(report["crosschecked_unsat"], 1192)
        self.assertEqual(report["open"], 96)
        self.assertFalse(report["computational_gap_census_complete"])

    def test_outside_receipt_requires_intact_dual_solver_logs(self):
        row = next(r for r in target.adapter.freeze()["rows"]
                   if r["class"] == "outside_frozen_phase_b")
        with tempfile.TemporaryDirectory() as temp:
            run = Path(temp)
            state, record = self.synthetic_outside_receipt(run, row)
            attempt = target.audit_outside_case(run, state, record, row)
            self.assertEqual(attempt["status"], "UNSAT_CROSSCHECKED")
            self.assertEqual(attempt["cnf_sha256"], record["cnf_sha256"])
            check = run / row["id"] / "materialization/native/check.log"
            original_check = check.read_bytes()
            check.write_bytes(b"MATCH (0 clauses, top 0)\n")
            with self.assertRaisesRegex(ValueError, "native emission/check mismatch"):
                target.audit_outside_case(run, state, record, row)
            check.write_bytes(original_check)
            table = run / row["id"] / "materialization/native/table.json"
            original_table = table.read_bytes()
            table.write_bytes(b"[]\n")
            with self.assertRaisesRegex(ValueError, "native table differs"):
                target.audit_outside_case(run, state, record, row)
            table.write_bytes(original_table)
            with (run / row["id"] / "solve" / row["id"] / "cadical.log").open("ab") as output:
                output.write(b"tampered\n")
            with self.assertRaisesRegex(ValueError, "Solver log identity mismatch"):
                target.audit_outside_case(run, state, record, row)


if __name__ == "__main__":
    unittest.main()
