#!/usr/bin/env python3
"""
ORDER-ONLY VERIFIER -- written from scratch, independent of bdd_verifier.py.

Question under test (Heath, 2026-07-27): is the reachable-set-of-0-1-orderings
representation, ALONE, COMPLETE for deciding whether a comparator network sorts?
No affine ledger, no branch atoms, no parity implications.

METHOD
  State = the set of reachable 0-1 configurations, as an ROBDD over wire vars.
  Each wire i carries a Boolean function w_i(x) = "wire i holds a 1 on input x".
  Comparator (i,j):   w_i <- w_i AND w_j   (min)     w_j <- w_i OR w_j   (max)
  Pair (i,j) is SETTLED iff  w_i AND NOT w_j  is unsatisfiable.
  Network sorts iff every adjacent pair (k,k+1) is settled.

SOUNDNESS rests on the 0-1 principle (Knuth 5.3.4 Thm Z): a comparator network
sorts all inputs iff it sorts all 0-1 inputs.  The BDD is EXACT on that set --
no approximation anywhere -- so a "sorts" verdict is a proof and a "does not
sort" verdict comes with a counterexample.

This file deliberately duplicates ROBDD machinery rather than importing it, so
that agreement with bdd_verifier.py is independent evidence rather than a
tautology.
"""
import sys, json, time, os, glob, re

class ROBDD:
    FALSE, TRUE = 0, 1
    def __init__(self, nvars):
        self.nvars = nvars
        self.nodes = [None, None]      # 0=FALSE, 1=TRUE; else (var, lo, hi)
        self.unique = {}
        self.memo = {}
    def mk(self, var, lo, hi):
        if lo == hi:
            return lo                                   # redundant test elided
        key = (var, lo, hi)
        got = self.unique.get(key)
        if got is not None:
            return got                                  # shared subgraph
        idx = len(self.nodes); self.nodes.append(key); self.unique[key] = idx
        return idx
    def var(self, i):  return self.mk(i, self.FALSE, self.TRUE)
    def top(self, n):  return self.nodes[n][0] if n > 1 else self.nvars
    def _apply(self, tag, fn, a, b, commutative):
        if a < 2 and b < 2: return fn(a, b)
        key = (tag, b, a) if (commutative and a > b) else (tag, a, b)
        got = self.memo.get(key)
        if got is not None: return got
        va, vb = self.top(a), self.top(b)
        v = va if va < vb else vb
        alo, ahi = (self.nodes[a][1], self.nodes[a][2]) if (a > 1 and va == v) else (a, a)
        blo, bhi = (self.nodes[b][1], self.nodes[b][2]) if (b > 1 and vb == v) else (b, b)
        res = self.mk(v, self._apply(tag, fn, alo, blo, commutative),
                         self._apply(tag, fn, ahi, bhi, commutative))
        self.memo[key] = res
        return res
    def AND(self, a, b):    return self._apply("and", lambda x, y: x & y, a, b, True)
    def OR(self, a, b):     return self._apply("or",  lambda x, y: x | y, a, b, True)
    def DIFF(self, a, b):   return self._apply("dif", lambda x, y: x & (1 - y), a, b, False)
    def size(self):         return len(self.nodes) - 2
    def witness(self, node):
        """Any satisfying assignment, or None. Used to report counterexamples."""
        if node == self.FALSE: return None
        asg = {}
        while node > 1:
            v, lo, hi = self.nodes[node]
            if hi != self.FALSE: asg[v] = 1; node = hi
            else:                asg[v] = 0; node = lo
        return asg

def verify(n, comparators, var_order=None):
    order = var_order or list(range(n))
    b = ROBDD(n)
    w = [b.var(order[i]) for i in range(n)]
    peak = 0
    for (i, j) in comparators:
        lo = b.AND(w[i], w[j])          # min: 1 only if both are 1
        hi = b.OR(w[i], w[j])           # max: 1 if either is 1
        w[i], w[j] = lo, hi
        if b.size() > peak: peak = b.size()
    unsettled = []
    for k in range(n - 1):
        bad = b.DIFF(w[k], w[k + 1])    # w_k = 1 AND w_{k+1} = 0  -> out of order
        if bad != b.FALSE:
            unsettled.append((k, k + 1, b.witness(bad)))
    return {"sorts": not unsettled, "nodes": b.size(), "peak": peak,
            "unsettled": unsettled}

def load(path):
    d = json.load(open(path))
    n = d.get("n") or d.get("num_inputs")
    net = d["network"]
    flat = ([tuple(c) for L in net for c in L]
            if net and isinstance(net[0][0], (list, tuple))
            else [tuple(c) for c in net])
    return n, flat

# NOTE: ground truth by 2^n enumeration lived here as brute().  It has moved to
# exhaustive.py, per the principle that a verifier must neither contain nor reach
# combinatoric search.  Tests import it from there; this module cannot.

if __name__ == "__main__":
    for p in sys.argv[1:]:
        n, f = load(p)
        t0 = time.time(); r = verify(n, f); dt = time.time() - t0
        print(f"{os.path.basename(p):<26} n={n:<3} m={len(f):<4} sorts={str(r['sorts']):<5} "
              f"nodes={r['nodes']:<8} t={dt:.3f}s")
