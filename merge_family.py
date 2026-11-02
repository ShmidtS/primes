import glob, sys, os
def modname(path):
    return 'Hagi.'+path.replace(chr(92),'/').replace('Hagi/','').replace('.lean','').replace('/','.')
def merge(files, out, header):
    internal={ 'import '+modname(f) for f in files }
    imports=[]; bodies=[]
    for f in files:
        t=open(f,encoding='utf-8').read(); lines=t.split('\n')
        for l in lines:
            ls=l.strip()
            if ls.startswith('import ') and ls not in internal and l not in imports: imports.append(l)
        last=max(i for i,l in enumerate(lines) if l.startswith('import '))
        bodies.append('\n'.join(lines[last+1:]).strip('\n'))
    txt='/-\nCopyright (c) 2026 HAGI_v2 authors. All rights reserved.\n-/\n\n'+('\n'.join(imports))+'\n\n'+header+'\n\n'+('\n\n'.join(bodies))+'\n'
    open(out,'w',encoding='utf-8',newline='\n').write(txt)
    oldmods=[modname(f) for f in files]
    newmod=modname(out)
    for g in glob.glob('Hagi/**/*.lean',recursive=True)+['Hagi.lean']:
        if g.replace(chr(92),'/')==out: continue
        t=open(g,encoding='utf-8').read(); orig=t
        for om in oldmods:
            t=t.replace('import '+om+'\n','import '+newmod+'\n')
        if t!=orig:
            lines=t.split('\n'); seen=set(); res=[]
            for l in lines:
                s=l.strip()
                if s==('import '+newmod):
                    if s in seen: continue
                    seen.add(s)
                res.append(l)
            open(g,'w',encoding='utf-8',newline='\n').write('\n'.join(res))
    for f in files:
        if f.replace(chr(92),'/')!=out: os.remove(f)
    print('merged ->',out)

fam=sys.argv[1]; out=sys.argv[2]; header=sys.argv[3]
merge(fam.split(','),out,header)
