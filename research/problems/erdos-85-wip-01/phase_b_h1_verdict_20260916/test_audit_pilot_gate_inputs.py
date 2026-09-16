import json
from pathlib import Path
import tempfile
import unittest

import audit_pilot_gate_inputs as target


class PilotGateInputAuditTests(unittest.TestCase):
    def test_primary_monitor_rejects_overadmission_and_non_utc_time(self):
        header = ("utc,kissat_processes,cadical_processes,solver_rss_mib,"
                  "largest_solver_rss_mib,memory_free_percent,output_disk_kib\n")
        with tempfile.TemporaryDirectory() as temp:
            path = Path(temp) / "primary.csv"
            path.write_text(header +
                "2026-09-16T19:00:00+00:00,3,1,900,300,94,50000\n" +
                "2026-09-16T19:00:30+00:00,2,2,910,305,94,50100\n")
            report = target.primary_monitor(path, 4)
            self.assertEqual(report["maximum_solver_processes"], 4)
            self.assertEqual(report["maximum_sample_gap_seconds"], 30)
            path.write_text(path.read_text().replace(",2,2,910", ",3,2,910"))
            with self.assertRaisesRegex(ValueError, "exceeds frozen worker count"):
                target.primary_monitor(path, 4)
            path.write_text(path.read_text().replace("19:00:30+00:00", "19:00:30+01:00"))
            with self.assertRaisesRegex(ValueError, "not increasing UTC"):
                target.primary_monitor(path, 4)

    def test_supplement_monitor_parses_container_names_and_rejects_bad_stats(self):
        header = ("utc,host_process_rss_mib,docker_host_rss_mib,swap_used_mib,"
                  "docker_container_stats_json,docker_stats_error\n")
        with tempfile.TemporaryDirectory() as temp:
            path = Path(temp) / "supplement.csv"
            stats = json.dumps([{"Name": "erdos85-h1-input-abc"},
                                {"Name": "unrelated"}]).replace('"', '""')
            path.write_text(header +
                f'2026-09-16T19:00:00+00:00,60000,1300,0,"{stats}",\n')
            report = target.supplement_monitor(path)
            self.assertEqual(report["maximum_h1_input_containers"], 1)
            self.assertEqual(report["maximum_swap_used_mib"], 0)
            path.write_text(path.read_text().replace('""Name""', '""Bad""'))
            with self.assertRaisesRegex(ValueError, "Malformed Docker"):
                target.supplement_monitor(path)


if __name__ == "__main__":
    unittest.main()
