#!/usr/bin/env python3
"""Recount and join U domains only, with per-stage subprocess deadlines."""
from pathlib import Path
import argparse
import subprocess
import sys

parser=argparse.ArgumentParser()
parser.add_argument('--output-dir',type=Path,required=True)
parser.add_argument('--production-dir',type=Path,default=Path(__file__).resolve().parent.parent)
args=parser.parse_args();args.output_dir.mkdir()
here=Path(__file__).resolve().parent
subprocess.run([sys.executable,'-B',str(here/'census.py'),'--output',str(args.output_dir/'results.json')],check=True,timeout=60)
for label,name,boundary in [('5','verify_q7_h3_triple_m3_singleton_exclusion.py','U_reps'),('4','verify_q7_h3_triple_m1_r3_singleton_exclusion.py','U_reps'),('m1r4-5','verify_q7_h3_triple_m1_r4_singleton_exclusion.py','U_reps'),('m2-5','verify_q7_h3_triple_m2_singleton_exclusion.py','U_reps'),('m2-4','verify_q7_h3_triple_m2_singleton_exclusion.py','U_r3')]:
 result=subprocess.run([sys.executable,'-B',str(here/'extract.py'),str(args.production_dir/name),boundary],capture_output=True,check=True,timeout=90)
 with (args.output_dir/f'production-{label}.json').open('xb') as target:target.write(result.stdout)
subprocess.run([sys.executable,'-B',str(here/'compare.py'),'--data-dir',str(args.output_dir),'--output',str(args.output_dir/'joins.json')],check=True,timeout=60)
