# L-meta-3576 partial notes, 2026-11-24 (UNVERIFIED, no proof, not a submission)

CORRECTION: the words "exhaustive", "for every", "strong evidence" and "unlikely" below overstated the result. See the Correction section; the original text is kept unchanged otherwise.

Row: block inequality for independent sets covering the non-adjacent pairs of a 4-cycle-free bipartite graph. Claim: edges + vertex cover number + 1 <= sum over sets of (n - size). The row was not leased by us; this is advance preparation only.

## What was established (computation, not a proof)

Exhaustive check by integer programming over small cases: for every C4-free bipartite graph with side sizes (a,b) in (1,2), (2,2), (1,3), (2,3), (1,4), (3,3), (2,4), (3,4), (2,5), (3,5), (4,4), (2,6), (3,6), the minimum of sum (n - |I_j|) over all valid families of independent sets is at least edges + cover + 1. No counterexample was found. Graphs were deduplicated by a cheap degree-based invariant, so two non-isomorphic graphs could have been merged: treat the coverage as strong evidence, not as a complete enumeration.
The bound is tight (slack 0) on double stars: two adjacent centers, one with all other-side vertices and the second with a few leaves. For example sides 3+5 with 7 edges, cover number 2 and minimum sum 10 = 7 + 2 + 1.

## Consequences

- A counterexample to this row (the negation row) is unlikely on small graphs.
- A proof must be tight on double stars, so any argument that loses a constant will fail. The desk sketch's route (c(v) = number of sets missing v; c(u) + c(v) >= k on each edge) is consistent with the tight cases but gives no bound by itself.

## Correction (2026-11-24, 23:05 Bogota)

The first version of this note said the result was "strong evidence" and that a counterexample was "unlikely". Those statements were not supported and are withdrawn. What was actually tested:

- One representative graph per class of a coarse degree-based invariant, for the side sizes listed above. The invariant is not an isomorphism test, so some non-isomorphic graphs were merged and others were not examined. The graph counts printed per case count invariant classes, not graphs.
- Each instance was a 0/1 integer program. Results were kept only when the solver reported status 0 (optimal). Infeasible programs (hypotheses unsatisfiable for that graph) were skipped and not counted. The optimum was compared by rounding the floating-point objective; that rounding was not independently certified.
- No violation appeared among those tested representatives. Nothing follows about untested graphs, larger sizes, or the truth of the row.
- The tight examples (slack 0) were double stars; this describes tested instances only.

## Not done

No Lean proof, no induction argument that closes. Work on this row is dropped for now. The check script is below.

```python
import itertools, sys, time
import numpy as np
from scipy.optimize import milp, LinearConstraint, Bounds
def run(a,b,limit_s):
    n=a+b; L=list(range(a)); R=list(range(a,n)); pairs=[(i,j) for i in L for j in R]
    seen=set(); worst=None; cnt=0; t0=time.time(); bad=[]
    for m in range(1<<len(pairs)):
        E=[pairs[i] for i in range(len(pairs)) if m>>i&1]
        adj=[0]*n
        for u,v in E: adj[u]|=1<<v; adj[v]|=1<<u
        # C4-free: no two left vertices share 2 right nbrs
        if any(bin(adj[x]&adj[y]).count('1')>=2 for x,y in itertools.combinations(L,2)): continue
        # canonical key by degree sequence + sorted adjacency under no iso reduction: use cheap invariant dedupe
        key=(tuple(sorted(bin(adj[x]).count('1') for x in L)),tuple(sorted(bin(adj[x]).count('1') for x in R)),tuple(sorted(tuple(sorted(bin(adj[x]&adj[y]).count('1') for y in L)) for x in L)))
        if key in seen: continue
        seen.add(key)
        # min vertex cover
        tau=min(bin(T).count('1') for T in range(1<<n) if all((T>>u&1) or (T>>v&1) for u,v in E))
        ind=[S for S in range(1<<n) if all(not (S>>u&1 and S>>v&1) for u,v in E) and bin(S).count('1')<=n-2 and S!=0]
        if len(ind)<2: continue
        A=[];lo=[];hi=[]
        k=len(ind)
        for v in range(n):
            A.append([1 if S>>v&1 else 0 for S in ind]);lo.append(1);hi.append(np.inf)
            A.append([(1 if S>>v&1 else 0)-1 for S in ind]);lo.append(-np.inf);hi.append(-1)
        for u in range(n):
            for v in range(u+1,n):
                if not adj[u]>>v&1:
                    A.append([1 if (S>>u&1 and S>>v&1) else 0 for S in ind]);lo.append(1);hi.append(np.inf)
        A.append([1]*k);lo.append(2);hi.append(np.inf)
        c=[n-bin(S).count('1') for S in ind]
        r=milp(c,constraints=LinearConstraint(np.array(A),lo,hi),integrality=np.ones(k),bounds=Bounds(0,1))
        cnt+=1
        if r.status!=0: continue   # infeasible: hypotheses unsatisfiable
        val=round(r.fun); need=len(E)+tau+1
        slack=val-need
        if worst is None or slack<worst[0]: worst=(slack,a,b,E,tau,val)
        if slack<0: bad.append((a,b,E,tau,val,need))
        if time.time()-t0>limit_s: break
    return cnt,worst,bad

# usage: run(a, b, time_limit_seconds) returns (graphs checked, tightest case, violations)
```
