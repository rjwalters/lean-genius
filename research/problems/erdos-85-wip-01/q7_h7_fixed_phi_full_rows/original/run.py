from pathlib import Path
import json,time,collections
from filter import check
p=Path(__file__).parent
review=json.loads((p/'api-review.json').read_text());assert review['id']==2101 and review['status']=='resolved' and review['resolution'].startswith('PASS')
source=json.loads((p/'input.json').read_text());assert len(source)==18 and len({r['source_index'] for r in source})==18
start=time.monotonic();deadline=start+60;out=[]
for record in source:
 if time.monotonic()>deadline:break
 result=check(record['adjacency'],max_nodes=100000,deadline=deadline)
 result['source_index']=record['source_index'];out.append(result)
summary={'visited':len(out),'total':18,'unvisited':18-len(out),'counts':dict(collections.Counter(r['status'] for r in out)),'nodes':sum(r['nodes'] for r in out),'seconds':time.monotonic()-start}
(p/'results.json').write_text(json.dumps({'summary':summary,'results':out},indent=2)+'\n');print(summary)
