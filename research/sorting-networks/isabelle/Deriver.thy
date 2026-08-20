theory Deriver
  imports DischargeCalculus
begin

(* ============================================================================
   ROUTE B — ISABELLE AS A PER-NETWORK DERIVER (not just a certifier).

   Heath's idea (2026-07-19): make Isabelle ITSELF run the discharge derivation and
   emit a per-network machine-checkable certificate. Not "Isabelle certifies the
   calculus is correct" (Correctness.thy) and not "Isabelle checks facts Bocher's
   Python derived" (isabelle_emit.py) — but "Isabelle DERIVES the facts and the
   derivation IS the proof."

   This file builds the EXECUTABLE deriver, lifting the proved-sound rules from
   DischargeCalculus.thy into a function that, given a network, produces the set of
   banked pairwise facts. BONUS: Isabelle's inductive closure has no arbitrary budget,
   so it settles the (3,5) budget-vs-logic question independently.

   INCREMENT 1 (this): the UNCONDITIONAL core — comparator axiom + frame + transitive
   closure. No branch-atoms / covering-family yet (that's the conditional layer, later
   increments). This already derives the facts for networks that close via
   transitivity alone.

   Author: Iyun (Route B), on Heath's go-ahead (overnight build). Machine-checked
   incrementally — no step recorded until `isabelle process` prints val it = (): unit.
   ============================================================================ *)

section \<open>Facts as a ledger of ordered wire-pairs\<close>

text \<open>A banked fact (i,j) with i<j means "wire i <= wire j" holds unconditionally at
  the current column. We represent the ledger as a set of such pairs. (We keep i<j as
  a normalization; the semantic meaning is the <= relation.)\<close>

type_synonym fact_pair = "nat \<times> nat"
type_synonym ledger = "fact_pair set"

text \<open>The comparator (a,b) with a<b, applied at a column, banks (a,b) unconditionally
  (comparator axiom: out_a <= out_b). This is the atomic derivation step's core fact.\<close>

definition comparator_fact :: "nat \<Rightarrow> nat \<Rightarrow> fact_pair" where
  "comparator_fact a b = (if a \<le> b then (a,b) else (b,a))"

section \<open>Transitive closure of a ledger (the derivation's inference engine)\<close>

text \<open>Given a set of banked pairwise <= facts, the derivable facts are its reflexive-
  transitive closure viewed as a relation. We compute the closure of the ledger as a
  relation on wires. This is the transitivity rule as a DERIVATION step.\<close>

definition ledger_rel :: "ledger \<Rightarrow> (nat \<times> nat) set" where
  "ledger_rel L = L"

definition derive_closure :: "ledger \<Rightarrow> ledger" where
  "derive_closure L = { (i,j). (i,j) \<in> (ledger_rel L)\<^sup>+ }"

text \<open>Soundness of the closure step: if every banked pair is a true <= fact on a
  config, then every derived (closure) pair is also true. This lifts
  DischargeCalculus.pairwise_closure_sound to the ledger representation.\<close>

lemma derive_closure_sound:
  fixes v :: "('a::linorder) config"
  assumes banked_true: "\<forall>(i,j) \<in> L. v i \<le> v j"
  assumes derived: "(a,b) \<in> derive_closure L"
  shows "v a \<le> v b"
proof -
  from derived have "(a,b) \<in> (ledger_rel L)\<^sup>+" by (simp add: derive_closure_def)
  hence "(a,b) \<in> L\<^sup>+" by (simp add: ledger_rel_def)
  thus "v a \<le> v b"
  proof (induction rule: trancl_induct)
    case (base y)
    thus ?case using banked_true by auto
  next
    case (step y z)
    have "v y \<le> v z" using step.hyps(2) banked_true by auto
    with step.IH show ?case by (rule order_trans)
  qed
qed

section \<open>INCREMENT 2 — derive along a network\<close>

text \<open>Fold the derivation over a network: start with the empty ledger; for each
  comparator (a,b), add its comparator_fact, then close under transitivity. This is the
  UNCONDITIONAL deriver — it banks exactly the facts reachable by comparator-axiom +
  frame + transitivity, NOT yet the conditional/covering-family facts (later increments).\<close>

text \<open>FRAME-CORRECT derive_step: when comparator (a,b) fires, facts touching wire a or b
  may be disturbed and are DROPPED (frame rule — only untouched-wire facts survive). Then
  the comparator's own output fact (a,b) is added, and we close under transitivity. This
  fixes the increment-3 unsoundness (facts on touched wires were kept forever).\<close>

definition survives :: "nat \<Rightarrow> nat \<Rightarrow> fact_pair \<Rightarrow> bool" where
  "survives a b p = (fst p \<noteq> a \<and> fst p \<noteq> b \<and> snd p \<noteq> a \<and> snd p \<noteq> b)"

fun derive_step :: "ledger \<Rightarrow> comparator \<Rightarrow> ledger" where
  "derive_step L (a,b) =
     derive_closure (insert (comparator_fact a b) {p \<in> L. survives a b p})"

fun derive_network :: "network \<Rightarrow> ledger" where
  "derive_network [] = {}"
| "derive_network (c # cs) = derive_step (derive_network cs) c"

text \<open>NOTE ON ORDER: derive_network processes the list head-first via recursion, so we
  must be careful the fold direction matches network application order. We define it to
  process comparators in list order by folding left-to-right. Redefine with foldl for
  clarity of order (comparators applied in sequence).\<close>

definition derive_net :: "network \<Rightarrow> ledger" where
  "derive_net net = foldl derive_step {} net"

section \<open>Soundness of the network deriver\<close>

text \<open>KEY SOUNDNESS: every fact derive_net banks is TRUE on the output of the network,
  for every input. This is the deriver's correctness — it lifts derive_closure_sound
  across the whole network. We prove: if (i,j) is banked by derive_net, then for every
  config v, (run net v) i <= (run net v) j.

  NOTE: this increment proves the CLOSURE step sound (derive_closure_sound, done). The
  full network-soundness requires that each comparator_fact is true at its column, which
  is comparator_axiom + frame. That composition is increment 3. Here we record the
  deriver DEFINITION and its executable form; the end-to-end soundness theorem is next.\<close>

text \<open>Executable sanity: the empty network derives no facts; a single comparator (0,1)
  derives exactly (0,1).\<close>

lemma derive_net_empty: "derive_net [] = {}"
  by (simp add: derive_net_def)

lemma derive_net_single:
  "derive_net [(0,1)] = derive_closure {(0::nat,1::nat)}"
  by (simp add: derive_net_def comparator_fact_def)

section \<open>INCREMENT 3 — executable test on n=4-optimal\<close>

text \<open>Make the deriver EXECUTABLE and test whether pure comparator-axiom + transitivity
  closes the n=4-optimal network. derive_closure uses trancl, which is executable over
  finite relations via the code equations in HOL-Library. We test with `value`.

  n=4-optimal = [(0,1),(2,3),(0,2),(1,3),(1,2)]. Full sortedness = all 6 pairs
  {(0,1),(0,2),(0,3),(1,2),(1,3),(2,3)}. HONEST HYPOTHESIS: the deriver is UNCONDITIONAL
  (no branch-atoms), and the discharge calculus needs conditional facts to close even
  n=4 (recall Bocher's verifier banks 2 receivables at col 3-4 that discharge at the
  (1,2) move). So pure transitivity likely does NOT bank all 6 — and THAT gap is exactly
  what the conditional/covering-family layer (increment 4) must supply. Whichever way the
  value-test lands, it is recorded honestly.\<close>

text \<open>trancl is executable; but derive_closure as a set-comprehension over trancl may
  need a computable form. We provide an explicit finite closure for evaluation by
  restricting to the wires actually present. For the value-test we compute directly.\<close>

value "derive_net [(0::nat,1::nat)]"
value "derive_net [(0::nat,1),(2,3),(0,2),(1,3),(1,2)]"

section \<open>★ INCREMENT 3 — bug found AND frame-fixed: SOUND but INCOMPLETE (honest) ★\<close>

text \<open>THE FULL HONEST ARC of increment 3:

  (1) First deriver (no frame): value-test on n=4-optimal banked all 6 pairs — LOOKED like
      success. But a soundness check found it UNSOUND: on [(0,1),(1,2)] it banked (0,1),
      which is FALSE at the output (the 2nd comparator disturbs wire 1). It over-banked by
      keeping facts on wires a later comparator touched. NOT recorded as working.

  (2) FRAME FIX (survives predicate): a fact survives a comparator only if its wires are
      untouched by that comparator (DischargeCalculus.apply_comp_untouched). Now SOUND on
      the bug case: [(0,1),(1,2)] banks {(1,2)} only — the false (0,1) is correctly dropped.

  (3) BUT now SOUND-AND-INCOMPLETE: n=4-optimal banks only {(1,2)} (the last comparator's
      fact). The frame rule DROPS earlier facts whenever a comparator touches their wires —
      but it does NOT RE-DERIVE the facts that STILL hold after the disturbance. E.g. after
      (0,1) then (0,2): (0,1) is dropped (wire 0 touched), but (0,1) may still be TRUE at
      the new output and re-derivable — the naive frame just loses it.

  THE REAL LESSON (this is exactly Bocher's calculus's subtlety, now concrete in Isabelle):
  pure {comparator-axiom + frame-drop + transitivity} is SOUND but far too INCOMPLETE.
  The discharge calculus's power comes from the CONDITIONAL layer: when a comparator (a,b)
  fires, instead of just dropping facts on a/b, it re-establishes them via BRANCH ATOMS
  (Ox: input already ordered -> outputs keep order; tx: input reversed -> outputs swap) and
  discharges the resulting conditional facts. THAT is what recovers completeness. My frame-
  only deriver proves the floor (sound, but only trivially complete); the branch-atom layer
  (increment 4) is what closes real networks.

  This mirrors the GENERATOR result exactly (§18): my clean-room generator, penalizing
  conditional state, converged to bubble; here my clean-room deriver, dropping conditional
  facts, converges to near-nothing. SAME LESSON: you cannot get completeness (sub-trivial
  banking) WITHOUT the conditional/branch-atom machinery. Deferral is debt; frame-drop
  without re-derivation is amnesia.

  STATUS: increment 3 records a SOUND foundation (frame-correct) and the HONEST diagnosis
  that it is incomplete without the conditional layer. NOT overstated as "derives networks."
  It derives the frame-stable facts soundly; it needs branch-atoms (increment 4) for real
  completeness. Machine-checked (compiles); soundness of the frame-correct deriver is the
  next lemma to PROVE (not just test), then the branch-atom layer.\<close>

end
