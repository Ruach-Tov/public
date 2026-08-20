# References — Sorting Networks

*A living bibliography for the Ruach Tov Collective's sorting-networks research.
Compiled 2026-07-30, drawing on `SMITH.md` and `ROOTS.md` (Mavdil), the
bibliography in `mavchin/discharge_calculus_preprint.tex`, `RESULTS-n16.md`
(Heath + Mavdil), `references/README.md` (the AKS-generator Step-0 log), and
web/citation-tracing research (Doresh).*

**Purpose.** Two things: (1) a place for a researcher — human or agent — to find
the literature relevant to what we're doing here, with a note on *why* each
source matters to our actual work, not just a title; (2) a mechanism so the
collective doesn't forget to cite (or verify) work it already knows about.
Entries marked **[UNREAD]** or **[UNVERIFIED]** are known gaps — flagged
deliberately rather than silently dropped. Please add to this file rather than
let a new citation live only in an intercom message or a single contributor's
private notes.

Organized roughly chronologically within each section.

---

## 1. The origin — patents, before there was a "sorting network" literature

### O'Connor & Nelson, U.S. Patent 3,029,413, "Sorting System with n-line Sorting Switch"
Filed Feb 21, 1957; issued Apr 10, 1962.

**THE ROOT.** Per `ROOTS.md` (Mavdil's citation-forward traversal, proposed by
Heath): this patent's **Figure 4** is, as far as we have traced, the *first*
appearance of the modern sorting-network diagram notation — wires as horizontal
lines, comparators as vertical connectors — drawn in 1957, over a decade before
Knuth's Volume 3. The patent's claims embed optimal or near-optimal networks for
n = 4, 5, 6, 8. Everything downstream in this bibliography is, in a real sense,
commentary on an idea already fully formed here.

Cites five earlier antecedent patents (below), making this **not** the true
origin, only the earliest point where the modern representation crystallizes.

### Antecedents cited by O'Connor & Nelson (1957/1962)
- **Robbins (1954)**, U.S. Patent 2,674,733 — the *earliest* known antecedent
  found so far.
- **Goldberg et al. (1956)**, U.S. Patent 2,735,082.
- **Nelson (1958)**, U.S. Patent 2,837,732.
- **Ayres (1958)**, U.S. Patent 2,844,309.
- **Booth (1958)**, U.S. Patent 2,865,567 — **[UNVERIFIED]** plausibly A.D. Booth
  (the British computing pioneer), but this has not been confirmed.

*Relevance:* these are listed for completeness and because ROOTS.md flags them
as read-but-not-deeply-analyzed. If anyone traces these further, update this
entry with what's found — right now they're five names and patent numbers, not
yet incorporated into our understanding of the field's actual prehistory.

---

## 2. The 0-1 principle, and the correction of an attribution

### Floyd & Knuth (1970), "The Bose-Nelson Sorting Problem," Stanford TR STAN-CS-70-177
Later published as Floyd & Knuth, *A Symposium on Combinatorial Mathematics and
Its Applications*, 1970.

**This is the actual source of the 0-1 principle** (their Corollary 1) — not
Knuth's TAOCP Vol. 3 (1973) and not Burton Smith's 1972 thesis, both of which
state it but postdate this paper. Per `ROOTS.md`: an open question the
collective has flagged and not yet resolved is whether TAOCP §5.3.4 itself
cites Smith, and whether the "0-1 principle as a threshold-logic fact" framing
originates here, in Smith, or earlier still. **[UNRESOLVED — worth checking.]**

Floyd & Knuth's own bibliography (relevant entries, all **[UNREAD]** by us
except where noted, listed here specifically so the collective doesn't lose
track of them):
- **Batcher (1964)**, "A new internal sorting method," Goodyear Aerospace
  report GER-11759. Four years *before* Batcher's famous 1968 paper — the
  Batcher construction existed, in some form, earlier than the citation
  everyone actually uses.
- **Batcher (1968)**, "Sorting networks and their applications," AFIPS Spring
  Joint Computer Conference, 307–314. **Already formally cited** in
  `mavchin/discharge_calculus_preprint.tex` (`\bibitem{batcher1968}`). This is
  the standard reference for the odd-even mergesort network our own `n16`
  results (`RESULTS-n16.md`) are benchmarked against (63 comparators, depth 10,
  at n=16). **[Full paper itself still UNREAD by us — we cite it via its
  well-known results, not from having read the original.]**
- **Bose & Nelson (1962)**, "A sorting problem," *JACM* 9, 282–296. The paper
  that gives the field its name for a whole family of constructions
  ("the Bose-Nelson sorting problem").
- **Floyd (1964)**, "A minute improvement in the Bose-Nelson sorting
  procedure."
- **Floyd & Knuth (1967)**, "Improved constructions for the Bose-Nelson
  sorting problem," *Notices of the AMS* 14, 283.
- **Hibbard (1963)**, "A simple sorting algorithm," *JACM* 10, 142–150.

---

## 3. Smith's thesis — independently rediscovered results, and a real prior-art correction

### Smith, Burton J. (1972), "An Analysis of Sorting Networks," MIT Project MAC Technical Report TR-105
Found via a bitsavers scan — **does not appear in modern citation graphs or
search results** for the field. Full write-up: `SMITH.md` (Mavdil).

**Why this matters, concretely, to our own work:**
- **Theorem 3.2.3** (comparator action expressible in closed Boolean form) is
  **prior art to the discharge calculus** central to `mavchin`'s and `Mavdil`'s
  work this project — independently *rediscovered* by Heath, not derived from
  Smith. Worth citing precisely so we don't imply we found something no one
  had found before, when in fact Smith found an adjacent form of it in 1972.
- **Theorem 4.2.3** (convexity of a settled-state set iff describable by a
  partial order) explains a real DBM (difference-bound-matrix) representation
  failure case the team independently measured this project — Smith's proof
  gives the *reason* the failure mode exists, not just a description of it.
- **§2.1.13**: counts reachable states via ordered Bell numbers (Fubini
  numbers) — a real combinatorial fact we can cite rather than re-derive.
- **§2.2**: proves the 0-1 principle is *sharp* (not just sufficient) —
  stronger than the version usually quoted from Knuth.

Smith's own five-item bibliography (all **[UNREAD]** by us — noted here
precisely to avoid losing track):
- **Gale & Karp (1970)**, "A Phenomenon in the Theory of Sorting," IEEE
  Symposium on Switching and Automata Theory.
- **Knuth**, *TAOCP* Vol. 3 — cited by Smith as "to be published" (i.e., Smith's
  1972 thesis predates TAOCP Vol 3's 1973 publication date).
- **Liu (1971)**, "Construction of Sorting Plans," in *Theory of Machines and
  Computations*.
- **Miller (1965)**, *Switching Theory*, Vol. 1: Combinational Circuits.
- **Van Voorhis (1971)**, "A Lower Bound for Sorting Networks that Use the
  Divide-Sort-Merge Strategy," Stanford TR-17. **Not the same person** as the
  van Voorhis of the n=16 network below — or possibly the same; **[UNVERIFIED,
  worth checking]**.

**Open questions from `ROOTS.md`, still unresolved, worth restating here so
they aren't lost:**
- Has anyone, ever, published a citation *to* Smith's thesis? (Current
  finding: no evidence of any.)
- Where does "standard form" terminology (for sorting-network normal forms)
  actually originate — Smith, or earlier?

---

## 4. Optimality proofs — depth, size, and what's actually settled

### Parberry, I. (1991), "On the computational complexity of optimal sorting network construction," and related earlier work (~1985-era claims of coNP-completeness)
**Already formally cited** (`\bibitem{parberry1991}` in
`mavchin/discharge_calculus_preprint.tex`). **[UNREAD in full by us — flagged
explicitly in `ROOTS.md` as "known but unread," and this matters]**: the
folklore belief that optimal-sorting-network verification/construction was
"proven coNP-complete" circulates widely (see
`KNOWLEDGE-CONDITIONAL-PARALLELIZATION.md`, which references this folklore
directly), but **current collective belief, per `ROOTS.md`, is that this claim
has been neither proved nor refuted in the literature we've actually read** —
i.e., we do not have a confirmed source for the strong "proven coNP-complete"
claim. Do not cite this as settled without reading Parberry's actual papers
first. This directly bears on the polynomial-verification result
(`collective/polynomial-verification.tex`) — Exhibit 24a in that paper
correctly scopes our own polynomial claim narrowly rather than overclaiming
against an unverified folklore result.

### Bundala, D. & Závodný, J. (2014), "Optimal Sorting Networks," LATA 2014 / arXiv:1310.6271
Settles **depth-optimality for all n ≤ 16** (building on Parberry's earlier
n=9,10 depth-optimality proof). **This is the source for "depth 9 is proved
optimal at n=16,"** cited repeatedly in our own `RESULTS-n16.md` and
`TOURNAMENT-CASCADE.md`. Our own `n16_beam_61.json` (61 comparators, depth 9)
achieves this proven bound; it does not — and cannot — improve on it. **Also
already in `references/README.md`** as a downloaded/local reference.

### Codish, M., Cruz-Filipe, L., Frank, M., Schneider-Kamp, P. (2014–2016), sequence of papers establishing exact optimal sizes S(n) for n ≤ 12
Specifically: "Twenty-five comparators is optimal when sorting nine inputs
(and Ten)" — **already formally cited** (`\bibitem{codish2014}`). Established:
S(9)=25, S(10)=29, S(11)=35, S(12)=39. **Critical scoping fact, repeated
correctly in our own `RESULTS-n16.md`:** for n=13–16, only *bounds* are known
(best upper bounds 45, 51, 56, 60) — **exact optimal size is unknown at n=16**.
Our own 60-comparator n=16 network *matches* the best known upper bound; it
does **not** prove optimality. Keep this distinction sharp in any future
publication — it is the single easiest thing to overclaim.

### Codish, M., Cruz-Filipe, L., Ehlers, T., Müller, M., Schneider-Kamp, P. (2015), "Sorting Networks: to the End and Back Again," arXiv:1507.01428
**Already downloaded**, per `references/README.md`. Useful as a source of
optimal small-network base cases and as a verification benchmark for our own
generator's small-n output.

---

## 5. Historical n=16 constructions (pre-computer-search era)

### Green (c. 1969), and van Voorhis (c. 1970) — the two canonical hand-derived n=16 networks
- **Green's network**: 60 comparators, depth 10.
- **van Voorhis's network**: 61 comparators, depth 9.

Both predate widespread computer search for sorting networks and are treated
in the literature (see Sergeev below) as *the* canonical n=16 examples — not
one of many published alternatives, but the small, named handful the field
actually cites. Our own `RESULTS-n16.md` benchmarks against both by name
(our `n16_braid_60.json` beats Green's comparator count by 3 at the same
depth; our `n16_beam_61.json` matches van Voorhis's depth-9 bound with one
fewer comparator and one fewer layer than Batcher's odd-even mergesort).

**[UNVERIFIED — worth chasing]**: neither Green's nor van Voorhis's original
publication has been directly located/read by us; we know them through
secondary description (Sergeev 2018, Dobbelaere's catalog, and this
project's own prior research). If anyone finds Green's or van Voorhis's
actual original paper, add the citation here.

### Sergeev, I. (2018), "Some comments on the structure of the best known networks sorting 16 elements," arXiv:1810.11262
Direct structural analysis of the Green and van Voorhis networks — why they
have the structure they do. Notes it is not aware of prior published analysis
of this specific question. **Zero forward citations**, confirmed via the
Semantic Scholar API (Doresh, 2026-07-30) — this paper appears to be an
epistemic dead end in terms of follow-up work, despite being a careful, useful
analysis in itself.

Sergeev's own paper cites three sources for **additional, independently-found,
60-comparator/depth-10 n=16 networks with different structure** from Green's —
this is the actual answer to "how many n=16 networks have been published,"
and it was found by tracing Sergeev's own backward citations (Doresh,
2026-07-30):

- **Juillé, H. (1995)**, "Evolution of Non-Deterministic Incremental
  Algorithms as a New Approach for Search in State Spaces," Proc. 6th Int'l
  Conf. on Genetic Algorithms (ICGA). Found 60-comparator n=16 networks in 2 of
  3 runs on a Maspar MP-2 supercomputer, each run taking 2–3 days. **One
  concrete, complete example survives**, preserved by the University of
  Kaiserslautern's Averest project:
  `averest.org/examples/Quartz/Algorithms/Sorting/SortNet16/Juille1.html` —
  a full, machine-verifiable 60-comparator, 10-layer network with test cases.
  Worth mirroring locally given how easily such pages disappear.
- **Choi, B.-D. & Moon, B.-R. (2002)**, "Isomorphism, normalization, and a
  genetic algorithm for sorting network optimization," GECCO 2002. Explicitly
  benchmarks against Juillé. Reports finding 60-comparator n=16 networks in
  **all 50 of 50 trials** with their base method (HGA) and **all 100 of 100**
  with their improved method (N-HGA) — a single-CPU-PC run taking about half a
  day total, versus Juillé's multi-day supercomputer runs. **On the order of
  150 independently-found 60-comparator networks in this one paper alone**,
  though the paper's central contribution is a symmetry/isomorphism reduction
  showing many of these are equivalent under wire relabeling — the *distinct
  up to symmetry* count is almost certainly much smaller than 150, and is not
  stated explicitly in what we've read of this paper. **[Worth a closer read —
  we have the PDF, `/tmp/choi_moon.pdf` as of this writing, not yet permanently
  archived in this repo.]**
- **Valsalam, V.K. & Miikkulainen, R. (2013)**, "Using symmetry and
  evolutionary search to minimize sorting networks," *Journal of Machine
  Learning Research* 14, 303–331 (preliminary version: UT Austin TR AITR-11-09,
  2011). Same era, same symmetry-exploiting strategy (their system is named
  SENSO). Same caveat applies: found many networks, exact distinct-up-to-symmetry
  count at n=16 not confirmed by us as a specific number.

**Honest summary of the actual state of "how many n=16 networks are published"
(Doresh's answer to Heath, 2026-07-30, refined here)**: there is no public
atlas/catalog of many *named*, individually distinguishable n=16 networks the
way there might be for small enumerable combinatorial objects. Instead, there
is strong evidence that **multiple independent research groups (1995, 2002,
2011–2013), across three different computational approaches, each
independently found dozens to over a hundred size-60 networks** — but
typically only one representative was shown per paper, and none of the sources
we've found states a confirmed "distinct up to symmetry" census.

**A notable contrast worth recording precisely (Heath, 2026-07-30, verified
against the actual network files by Doresh):** Juillé's 1995 runs took
2–3 days each on a Maspar MP-2 supercomputer; Choi & Moon's 2002 runs took
about half a day total on a single-CPU PC, across 150 trials. **Our own three
n=16 networks in `RESULTS-n16.md` (`n16_braid_60.json`, `n16_beam_61.json`,
`n16_crossblock_62.json`) were found in *minutes* on a laptop CPU.** Checked
directly: all three share an **identical canonical layer 1** (the eight
adjacent-pair comparators `(0,1)(2,3)(4,5)...(14,15)`) and an **identical
layer-2 comparator set** (the eight pairs `(0,2)(1,3)(4,6)(5,7)...(12,14)(13,15)`
— i.e. the standard Knuth/Floyd bitonic-style opening prefix, referenced
elsewhere in `RESULTS-n16.md` as "the canonical Knuth/Floyd prefix"). This is
not a coincidence: fixing this canonical two-layer opening is precisely what
collapses the search space this project actually explored (`RESULTS-n16.md`
reports "all matchings on live pairs: 15,519,643" down to "935 class-role
pairings" and eventually 135–175 candidate layer-3 shapes) — the speed
advantage over prior computational approaches appears to come substantially
from *not* re-searching a prefix that earlier evolutionary/genetic-algorithm
approaches (Juillé, Choi & Moon, Valsalam & Miikkulainen) had to rediscover
each run, rather than from raw hardware improvement alone. Worth stating
explicitly in any future write-up: the comparison across methods is not
apples-to-apples on search difficulty, since our method starts from a fixed,
literature-known canonical prefix that the earlier evolutionary approaches
were themselves searching over.

---

## 6. The collective's own n=16 generation work (not a citation — our own result, recorded for completeness)

### `RESULTS-n16.md` (Heath: structural account; Mavdil: implementation, measurement, verification), 28–30 July 2026
Three verified networks in `networks/`: `n16_braid_60.json` (60 comparators,
depth 10 — beats Batcher's 63/10 by 3), `n16_beam_61.json` (61 comparators,
depth 9 — matches the Bundala-Závodný proven-optimal depth), and
`n16_crossblock_62.json` (62, 10). All verified exhaustively on all 2¹⁶ binary
inputs plus 20,000 random real vectors.

A systematic sweep of all 175 within-class layer-3 shapes found **16 distinct
size-60/depth-10 networks and 20 distinct size-61/depth-9 networks** by this
project's own `tourney.py` generator.

**[AUDIT RESOLVED, Mavdil 2026-07-31.]** An earlier version of this note
questioned the second figure, having counted the committed `networks/` files and
found exactly one size-61/depth-9 file rather than twenty. The figure is correct
and the audit was wrong: all thirty-six networks were stored in
`runs/sym_results.json` at generation time and only the sixteen size-60 ones were
ever extracted to files. The twenty existed but had never been written out. Found
by running `tools/origin_story/ls-by-origin-story.pl` over `networks/`, which
attributes each file to the commit that introduced it and led straight back to the
extraction commit and its source JSON. Both catalogues are now complete:
`networks/catalog60/` (16 files) and `networks/catalog61/` (20 files), each
carrying its layer-3 program tag and symmetry data.

A further fact worth recording, measured the same way: those **16 distinct
size-60 layerings are only 4 distinct comparator multisets**, while the twenty
size-61 networks are **18 distinct multisets** — far less degenerate. Five of the
twenty are reversal-symmetric as a set and fifteen are not. Layering and multiset are
different equivalence relations and the library collapses hard under the second
one. `TAXONOMY.md` reports the same phenomenon over the whole n=16 library —
20 files, 18 distinct layerings, 6 distinct multisets — and the two counts are
consistent, being different scopes. Any future census claim needs to say *which*
equivalence it counts, since the answer differs by a factor of four. The file is explicit and honest about
what this does and doesn't establish: *"the count of size-60 networks is
unknown... '16 size-60 shapes' is a lower bound from a sample... it is not a
census."* This is worth cross-referencing against Choi & Moon's ~150-run
figure above — different methods, different eras, neither is a confirmed
exhaustive count, and that gap (no one has published a true census of
distinct n=16 optimal-or-near-optimal networks) is itself worth stating
plainly as an open question for the field, not just for us.

---

## 7. Asymptotically-optimal constructions (the AKS family)

### Ajtai, M., Komlós, J., Szemerédi, E. (1983), the original AKS sorting network
O(n log n) comparators, matching the Ω(n log n) information-theoretic lower
bound — asymptotically optimal, but with astronomically large constants,
famously impractical. **[Not yet a formal citation entry anywhere in this
repo's `.tex` files as of this writing — should be added if we ever
reference AKS formally rather than just by name, since it's currently only
named informally in `doresh/conversation_log_doresh_jul_19_to_24.md`.]**

### Paterson, M. (1990), "Improved sorting networks with O(log N) depth," Algorithmica, DOI 10.1007/BF01840378
A simplified AKS construction. **Springer-paywalled, not downloaded** — DOI
recorded in `references/README.md` but the paper itself is unread by us.

### Goodrich, M. (2014), "Zig-zag Sort: A Simple Deterministic Data-Oblivious Sorting Algorithm Running in O(n log n) Time," STOC 2014 / arXiv:1403.2777
**THE actual build target** for this project's AKS-alternative generator
effort, per `references/README.md` and confirmed working code in
`dual-landscape/AFFINE-GATE-PARITY.md`: "we now HAVE a real, verified O(n log
n) sorter generated from first principles," built on the same ε-halver
primitive already implemented (`aks_faithful.verified_halver`). Uses a
Shellsort-style zig-zag pass structure instead of AKS's notoriously hard
expander-based construction. Constants "orders of magnitude smaller than
constructive AKS variants," per the paper's own abstract. **This is real,
active, working code in this repo** — not just a citation.

---

## 8. BDD / formal-verification tooling

### Bryant, R.E. (1986), "Graph-based algorithms for Boolean function manipulation," IEEE Trans. Computers
**Already formally cited** (`\bibitem{bryant1986}`). The foundational BDD
paper — underlies the 0-1-reachability/BDD verification approach in
`collective/polynomial-verification.tex` §2, and the empirical O(n³)-scaling
BDD measurements reported there (48 seconds at n=256, ~3M nodes).

### Knuth, D.E. (1998), *The Art of Computer Programming*, Vol. 3: Sorting and Searching, §5.3.4
**Already formally cited** (`\bibitem{knuth1998}`). The standard textbook
treatment of sorting networks — states the 0-1 principle (which, per §2
above, actually originates with Floyd & Knuth 1970, not this later
publication) and surveys Batcher's and other constructions. **[Whether TAOCP
§5.3.4 itself cites Smith 1972 is an open question from `ROOTS.md`, unresolved
— worth checking directly against a physical/PDF copy.]**

---

## 9. Living/community resources

### Dobbelaere, Bert — "Sorting Networks" catalog, bertdobbelaere.github.io/sorting_networks_extended.html
A maintained, non-academic but carefully-sourced catalog listing one
representative network per size/depth frontier point, for a wide range of n.
For n=16 specifically, lists only the same two canonical points as Sergeev
(60,10) and (61,9) — **not** a broader atlas of many distinct examples (see
§5 above for why the real multiplicity story has to be traced through the
Sergeev/Juillé/Choi-Moon/Valsalam-Miikkulainen citation chain instead). Useful
as a fast reference for "what's the current best known bound at size n," less
useful for "how many distinct networks are known."

---

## Open items — things we know we should check, but haven't yet

These are restated from `ROOTS.md` and this compilation process, gathered
here so they aren't lost across multiple source documents:

1. Does Knuth's TAOCP (any edition) cite Smith's 1972 thesis? Unknown.
2. Has *anyone*, ever, published a citation to Smith's 1972 thesis? Current
   finding: no evidence of any — it appears to be genuinely obscure, outside
   the citation graphs we can search.
3. Is the 0-1-principle-as-threshold-logic framing original to Smith, or does
   it predate him (e.g., in Floyd & Knuth 1970, or earlier)?
4. Where does "standard form" terminology (for sorting-network normalization)
   actually originate?
5. Was Parberry's coNP-completeness claim (folklore-attributed to
   ~1985-era work) ever actually *proved* by anyone, in a paper we can point
   to? Current belief: neither proved nor refuted in what we've read — **do
   not cite this as settled.**
6. Green's and van Voorhis's original n=16 publications have not been located
   directly — we know them only secondhand.
7. Batcher's actual 1968 paper (and his earlier 1964 Goodyear report) remain
   unread by us in full, despite being cited/relied upon repeatedly.
8. No confirmed census of "distinct optimal-or-near-optimal n=16 sorting
   networks up to wire-relabeling symmetry" exists anywhere we've found — an
   open question for the field, not just for us, and possibly worth being the
   first to actually answer. **Note the equivalence ambiguity flagged in §6:**
   any such census must state whether it counts layerings or comparator
   multisets, which differ by a factor of four in our own library.
9. **[Added 2026-07-31; ANSWERED the same day.]** Dobbelaere's catalog gives
   185/14 as the best known at $n = 32$, and we benchmark against it constantly
   without having traced its source.

   **It is not a searched network.** The extended catalog attributes it plainly:
   *"Size/depth ubounds: Batcher odd-even merge"* — the same attribution it gives
   $n = 30$ and $n = 31$. Below $n = 30$ almost every entry is SorterHunter or a
   cited paper; at 30, 31 and 32 the classical construction is still the best
   known.

   **And it decomposes exactly.** Batcher's odd-even *merge* of two sorted
   16-sequences costs 65 comparators, so

   $$185 = 2 \times 60 + 65, \qquad 191 = 2 \times 63 + 65.$$

   The 185 is **two optimal 16-sorters plus Batcher's merge**; our own recorded
   figure of 191 is **full recursive Batcher**, which uses two 63-comparator
   Batcher 16-sorters. Same merge, different sub-sorters, and both numbers were
   right. Verified locally: textbook Batcher mergesort gives 5, 19, 63, 191, 543
   at $n = 4, 8, 16, 32, 64$, matching the known values.

   Two consequences worth stating. First, the record at $n = 32$ rests on a
   *construction*, not a search — so it is a softer target than the searched
   entries at smaller sizes, and the 147…185 size bracket in the catalog is wide.
   Second, since $185 = 2 \times 60 + 65$ inherits its quality directly from the
   optimal 16-sorter, **any improvement to $S(16)$ below 60 would immediately
   improve the $n = 32$ record by twice as much** — which is one reason the
   $n = 16$ census question in item 8 is not merely of local interest.

   **And the leverage compounds.** Batcher's merge costs 65, 161 and 385
   comparators at $n = 32, 64, 128$, and each level of the recursion consumes two
   copies of the level below. So a single comparator saved at $n = 16$ propagates
   as

   | | $n{=}16$ | $n{=}32$ | $n{=}64$ | $n{=}128$ |
   |---|---:|---:|---:|---:|
   | $S(16) = 60$ | 60 | 185 | 531 | 1447 |
   | $S(16) = 59$ | 59 | 183 | 527 | 1439 |
   | saving | 1 | **2** | **4** | **8** |

   The saving doubles at every level. That is not an argument that $S(16) < 60$ is
   attainable — 60 has stood since Knuth reports it — but it does mean the $n = 16$
   problem is the load-bearing one for every power of two above it, so long as the
   record at those sizes rests on the merge construction.
10. **[Added 2026-07-31]** Is there any literature on the *structure* of
   endgame layers — the observation that a final layer of $c$ comparators
   closes exactly $2c$ ranks, and that good networks arrive at it with many
   width-2 rank windows on adjacent pairs? Dobbelaere's 185/14 finishes with 13
   adjacent comparators $(3,4)(5,6)\dots(27,28)$, a perfect odd-phase matching.
   Sergeev (2018) analyses the structure of the n=16 networks; whether anyone
   has analysed endgames specifically is unknown to us.

   **[Partial answer, 2026-07-31.]** No endgame-structure literature found, but a
   directly adjacent result was: **Ichikawa et al. (2026), "Odd-even transposition
   sort is an optimal stable standard sorting network"**, *Information Processing
   Letters* (ScienceDirect S0020019026000402, paywalled; abstract read). It proves
   odd-even transposition is both **size-optimal and depth-optimal among STABLE
   STANDARD sorting networks**, and notes the standing asymptotic gap: the best
   known lower bound on stable-network size is $\Omega(n \log n)$ while odd-even
   transposition uses $\Theta(n^2)$.

   This confirms independently a result derived in this project on 2026-07-31,
   and sharpens it. We had established that **adjacent-only implies stable**, that
   the adjacent-only network is odd-even transposition, and that it costs
   $n(n-1)/2$ comparators and depth $n$ — 120/16 at $n = 16$ against our 60/10.
   Ichikawa et al. establish that this is not a defect of the construction but
   **optimal for the class**: no stable standard network does better. The price of
   stability is exactly the gap between $60$ and $120$, and it is unavoidable.

   Bearing on the endgame question: every optimal or near-optimal network we have
   examined **finishes with an odd-even transposition layer** — a maximal set of
   adjacent comparators of one phase. Dobbelaere's $185/14$ ends with
   $(3,4)(5,6)\dots(27,28)$; our $199/16$ ends with four even-phase adjacent
   pairs. So the last layer of a fast network is a single step of the slow
   stable one. Whether that is remarked anywhere in the literature remains open.

---

## Mechanistic Interpretability — Comparator Circuits in Transformers

9. **Bhardia, Ramirez, Verma, and Mkrtchyan (2026)** — *Mechanistic Analysis
   of Universality: Numerical Comparison Circuits Across Transformer
   Architectures.* Proceedings of the 64th Annual Meeting of the Association
   for Computational Linguistics (Volume 4: Student Research Workshop), pages
   951–967. Also presented at LIT Workshop @ ICLR 2026.

   Code: https://github.com/KarenMkrtchyan/Mechanistic_Analysis_of_Universality
   ACL Anthology: https://aclanthology.org/2026.acl-srw.84/
   Local copy: references/bhardia-et-al-2026-acl-srw.pdf

   Studies numerical-comparison circuits across several transformer families
   including Qwen3-1.7B. Uses activation patching and path patching on
   matched clean/corrupt prompt pairs to identify causally significant heads.
   Reports a top-ten ranked list for Qwen3-1.7B by logit-diff impact: L17H1,
   L17H11, L15H9, L17H0, L24H9, L18H15, L19H6, L23H6, L17H2, L18H14.

   Bearing on our work: Doresh's companion papers ("Two Comparators, Not Six"
   and "Comparator Mechanism Statistics") test Bhardia et al.'s reported heads
   directly against our own antisymmetry-based findings on the same model.
   Two of three tested pairs from their circuit are statistically
   indistinguishable from a null distribution on our sorting task; one pair
   (L15H9, L19H6) shows a real but weaker effect. We read this as evidence
   for a broader, comparator-relevant substrate that different detection
   methods sample from unevenly, rather than as evidence against either study.
