import ast,json,sys,hashlib
from pathlib import Path
boundary=sys.argv[2] if len(sys.argv)>2 else 'U_reps'
path=Path(sys.argv[1]);raw=path.read_bytes();tree=ast.parse(raw);prefix=[]
for node in tree.body:
 prefix.append(node)
 if isinstance(node,ast.Assign) and any(isinstance(t,ast.Name) and t.id==boundary for t in node.targets):break
else:raise RuntimeError('No U_reps boundary')
assert all(not isinstance(n,ast.Call) or not isinstance(n.func,ast.Attribute) or n.func.attr not in ['write_text','write_bytes','open'] for node in prefix for n in ast.walk(node))
ns={'__file__':str(path),'print':lambda *a,**kw:None}
exec(compile(ast.Module(body=prefix,type_ignores=[]),str(path),'exec'),ns)
print(json.dumps({'source':str(path),'sha256':hashlib.sha256(raw).hexdigest(),'end_line':prefix[-1].end_lineno,'configs':len(ns['configs']),'representatives':ns[boundary],'boundary':boundary}))
