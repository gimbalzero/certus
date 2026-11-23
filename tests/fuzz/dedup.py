"""De-duplicate and densely renumber the expressions of a lean4export file.

Usage: python3 -I dedup.py IN OUT

Structurally equal expression records are merged into the first one, and
every reference is rewritten. Certus accepts either form; nanoda needs this
one."""
import json,sys
src,dst=sys.argv[1],sys.argv[2]
canon={}; seen={}
out=[]
def m(i): return canon.get(i,i)
for l in open(src):
    if not l.strip(): continue
    r=json.loads(l)
    if "ie" in r:
        for k in ("app","lam","forallE","letE","proj"):
            if k in r:
                for f in ("fn","arg","type","body","value","struct"):
                    if f in r[k]: r[k][f]=m(r[k][f])
        key=json.dumps({k:v for k,v in r.items() if k!="ie"},sort_keys=True)
        if key in seen:
            canon[r["ie"]]=seen[key]; continue
        new=len(seen)
        seen[key]=new
        canon[r["ie"]]=new
        r["ie"]=new
    else:
        for k in ("thm","def","axiom","opaque","quot"):
            if k in r:
                for f in ("type","value"):
                    if f in r[k]: r[k][f]=m(r[k][f])
        if "inductive" in r:
            d=r["inductive"]
            for t in d["types"]+d["ctors"]+d["recs"]:
                t["type"]=m(t["type"])
            for rr in d["recs"]:
                for rule in rr["rules"]:
                    rule["rhs"]=m(rule["rhs"])
    out.append(r)
with open(dst,"w") as f:
    for r in out: f.write(json.dumps(r,ensure_ascii=False)+"\n")
