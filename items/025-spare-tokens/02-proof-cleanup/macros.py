# 025-02 prune helper: the macro and syntax declarations still used. A macro is used when
# one of its keywords appears as a token in the text that stays (kept declarations and the
# text between declarations, comments stripped). Iterates prune.py (report only) to a fixpoint.
# Run from the clone's lean/ with the original sources. Prints the names to keep.
import re, subprocess, sys, collections
C="/Users/f/fl/bench/2026-11-14/cleanup"; T=C+"/tools"
tsv=T+"/reach-decls.tsv"; keep=sys.argv[1]; tmpkeep=sys.argv[2]; tmprep=sys.argv[3]
decls={}
for line in open(tsv):
    p=line.rstrip("\n").split("\t")
    if len(p)<6: continue
    decls[p[0]]=dict(mod=p[1],kind=p[2],a=int(p[3]),b=int(p[4]))
def path(m): return m.replace(".","/")+".lean"
src={}
for d in decls.values():
    p=path(d["mod"])
    if p not in src:
        try: src[p]=open(p).read().split("\n")
        except FileNotFoundError: src[p]=[]
def strip(text):
    out,i,depth,n=[],0,0,len(text)
    while i<n:
        if text.startswith("/-",i): depth+=1; i+=2; continue
        if depth and text.startswith("-/",i): depth-=1; i+=2; continue
        if depth: i+=1; continue
        if text.startswith("--",i):
            j=text.find("\n",i); i=n if j<0 else j; continue
        out.append(text[i]); i+=1
    return "".join(out)
macro=[n for n,d in decls.items() if re.match(r"«?(tactic|term|command|doElem|conv)[A-Z_]",n.split(".")[-1]) and d["a"]]
kw={}
for n in macro:
    d=decls[n]; t="\n".join(src[path(d["mod"])][d["a"]-1:d["b"]])
    t=strip(t)
    m=re.search(r"\b(macro|syntax|notation|elab)\b(.*?)(=>|:\s*(tactic|term|command|conv)\b)",t,re.S)
    head=m.group(2) if m else t.split("\n")[0]
    ks=[s.strip() for s in re.findall(r'"([^"]+)"',head) if s.strip()]
    kw[n]=[k for k in ks if re.match(r"^[A-Za-z_]",k)][:1]  # the leading keyword
    if not kw[n]: print("NOKW",n,file=sys.stderr)
base=[l.strip() for l in open(keep) if l.strip() and not l.startswith("#")]
added=[]
for it in range(20):
    open(tmpkeep,"w").write("\n".join(base+added)+"\n")
    subprocess.run(["python3",T+"/prune.py",tsv,"--keep",tmpkeep,"--report",tmprep],capture_output=True)
    dead={l.split()[3] for l in open(tmprep) if l.startswith("DEAD ")}
    # text that stays: per file, lines in a kept range or in no range
    stay=[]
    for p,lines in src.items():
        mask=[0]*(len(lines)+2)  # 0 none, 1 dead only, 2 kept
        for n,d in decls.items():
            if path(d["mod"])==p and d["a"]:
                v=1 if n in dead else 2
                for k in range(d["a"],d["b"]+1): mask[k]=max(mask[k],v)
        stay.append("\n".join(l for k,l in enumerate(lines,1) if mask[k]!=1 and not l.startswith("import ")))
    text=strip("\n".join(stay))
    toks=set(re.findall(r"[A-Za-z_][A-Za-z0-9_'!?]*",text))
    new=[n for n in macro if n in dead and n not in added and any(k in toks for k in kw[n])]
    print(f"round {it}: dead {len(dead)}, new macros kept {len(new)}",file=sys.stderr)
    if not new: break
    added+=new
for n in added: print(n, kw[n][0])
