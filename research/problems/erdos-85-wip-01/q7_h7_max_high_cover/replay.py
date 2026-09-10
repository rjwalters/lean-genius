from pathlib import Path
import tempfile, subprocess, json, hashlib
p=Path(__file__).parent
pins=json.loads((p/'bank-pins.json').read_text())
assert all(hashlib.sha256((p/f).read_bytes()).hexdigest()==h for f,h in pins.items())
with tempfile.TemporaryDirectory(prefix='erdos85-maxhigh-review-') as t:
 q=Path(t)
 s=(p/'original/check.py').read_text().replace("Path('/tmp/erdos85-sol1-h7-host-profiles/results.json')",repr(p/'profile-source.json').replace('PosixPath','Path'))
 (q/'check.py').write_text(s)
 subprocess.run(['python3',str(q/'check.py')],check=True,stdout=subprocess.DEVNULL)
 assert json.loads((q/'results.json').read_text())==json.loads((p/'original/results.json').read_text())
 s=(p/'review/check.py').read_text().replace("pathlib.Path('/tmp/erdos85-sol1-h7-max-high-cover')",'pathlib.Path('+repr(str(p/'original'))+')').replace("pathlib.Path('/tmp/erdos85-sol1-h7-host-profiles/results.json')",'pathlib.Path('+repr(str(p/'profile-source.json'))+')')
 (q/'review.py').write_text(s)
 subprocess.run(['python3',str(q/'review.py')],check=True)
 assert json.loads((q/'REVIEW2073.json').read_text())==json.loads((p/'review/REVIEW2073.json').read_text())
print('PASS portable original and independent review replay; all bank payload hashes match')
