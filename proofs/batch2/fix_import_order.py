import sys
# Move all leading import lines above a top-of-file /-! ... -/ (or /- ... -/) docstring block.
def fix(path):
    lines=open(path).read().split('\n')
    # find the docstring block at top: first non-blank line starts with /-! or /-
    i=0
    while i<len(lines) and lines[i].strip()=='':
        i+=1
    if i>=len(lines) or not (lines[i].lstrip().startswith('/-!') or lines[i].lstrip().startswith('/-')):
        return False
    # find end of doc block
    start=i
    bal=0; end=None
    j=i
    while j<len(lines):
        bal += lines[j].count('/-')
        bal -= lines[j].count('-/')
        if bal<=0:
            end=j; break
        j+=1
    if end is None: return False
    # collect import lines that appear AFTER the doc block (contiguous region allowing blanks/comments? just imports+blanks)
    imports=[]
    k=end+1
    # skip blanks
    region=[]
    kk=k
    while kk<len(lines):
        s=lines[kk].strip()
        if s.startswith('import '):
            region.append(kk)
        elif s=='':
            pass
        else:
            break
        kk+=1
    if not region: return False
    imp_lines=[lines[r] for r in region]
    # remove them (from bottom)
    for r in sorted(region, reverse=True):
        del lines[r]
    # insert imports at very top
    newlines = imp_lines + [''] + lines
    open(path,'w').write('\n'.join(newlines))
    return True
for f in sys.argv[1:]:
    print(f, fix('Proofs/'+f+'.lean'))
