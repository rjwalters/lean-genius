import sys, re
# Move `<modifier> in` lines that sit directly after a doc-comment close `-/`
# to ABOVE the doc-comment's opening `/--`.
MOD = re.compile(r'^\s*(open|set_option|unseal|omit|attribute|variable)\b.*\bin\s*$')
def fix(path):
    lines = open(path).read().split('\n')
    changed = False
    i = 0
    while i < len(lines):
        if MOD.match(lines[i]):
            # is previous non-empty line a doc-comment close?
            j = i-1
            if j>=0 and lines[j].rstrip().endswith('-/'):
                # find the opening /-- or /- of this doc block: scan up for a line starting the block
                # walk up until we find a line containing /-- or /- that opens (balance)
                # Simple: find the nearest line at or above j whose stripped starts with /-- or /-
                k = j
                # collect block: a doc comment may be single or multi line. Find opener.
                opener = None
                depth = 0
                # scan upward counting -/ and /-- , /-
                kk = j
                bal = 0
                while kk >= 0:
                    l = lines[kk]
                    bal += l.count('-/')
                    bal -= l.count('/-')
                    if bal <= 0 and ('/--' in l or re.match(r'\s*/-', l)):
                        opener = kk
                        break
                    kk -= 1
                if opener is not None and ('/--' in lines[opener] or lines[opener].lstrip().startswith('/-')):
                    mod = lines[i]
                    # remove modifier line
                    del lines[i]
                    # insert above opener
                    lines.insert(opener, mod)
                    changed = True
                    i = opener + 1
                    continue
        i += 1
    if changed:
        open(path,'w').write('\n'.join(lines))
    return changed

for p in sys.argv[1:]:
    c = fix('Proofs/'+p+'.lean')
    print(f"{p}: {'FIXED' if c else 'nochange'}")
