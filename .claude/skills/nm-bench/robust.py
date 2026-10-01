import sys,statistics as st,collections
# robust.py results.txt [v1,v2,...]: per-bench medians after dropping scores
# under 80% of the variant's own median (interference outliers; an
# all-variant median drops a whole variant that is legitimately slower); the
# last columns are each variant relative to the first. A variant with no
# score left prints "-".
d=collections.defaultdict(list); vs=[]
for l in open(sys.argv[1]):
    v,b,sd,s=l.split(); d[(b,v)].append(int(s))
    if v not in vs: vs.append(v)
if len(sys.argv)>2: vs=sys.argv[2].split(",")
bs=sorted({b for b,_ in d})
def med(b,v,m):
    own=[y for y in d[(b,v)] if y>0]
    m=st.median(own) if own else 0
    x=[y for y in own if y>=0.8*m]
    return (st.median(x) if x else None), len(x)
print("%-14s"%"bench"+"".join("%16s"%v for v in vs)+"  drop  "+"  ".join("%s"%v for v in vs[1:]))
for b in bs:
    allv=[x for v in vs for x in d[(b,v)] if x>0]; m=st.median(allv) if allv else 0
    row="%-14s"%b; drop=0; ms=[]
    for v in vs:
        md,n=med(b,v,m); ms.append(md); drop+=len(d[(b,v)])-n
        row+=("%12.0f n=%d"%(md,n)) if md else "%16s"%"-"
    rel=" ".join(("%+.1f%%"%(100*(x/ms[0]-1)) if (x and ms[0]) else "-") for x in ms[1:])
    print(row+"  %d  %s"%(drop,rel))
