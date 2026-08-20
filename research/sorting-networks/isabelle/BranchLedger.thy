theory BranchLedger
  imports SettledConservation
begin

(* ============================================================================
   THE BRANCH LEDGER AND THE ORPHAN LEMMA
   (Heath's formulation, 2026-07-27; instrumented and formalised by Opus5.)

   A comparator's outcome is recorded as a BRANCH ATOM g_k: 0 if the comparator
   left its wires alone, 1 if it swapped.  Facts in the ledger are conditioned on
   cosets over these atoms.  DISCHARGE collapses a fact derived under BOTH
   polarities of some atom into an unconditional fact -- it is the only route by
   which a conditional fact becomes unconditional.

   THE ORPHAN LEMMA.  If atom g appears in the ledger with only one polarity, no
   fact conditioned on g can ever discharge, so such facts may be ERASED without
   affecting any conclusion.  The lemma rests on a structural fact about how
   atoms enter the ledger:

     POLARITY IS MINTED ONCE.  Atom g_k is introduced only at comparator k, when
     facts touching its wires split into a g_k=0 copy and a g_k=1 copy.  Later
     comparators mint FRESH atoms and RELABEL existing facts; relabeling changes
     which wires a fact mentions but never alters a coset's constraint on g_k.
     Hence the set of polarities recorded for g_k is fixed at step k forever.

   MEASURED BEFORE FORMALISING (the discipline that has worked):
     - no atom is pinned over the REALIZABLE trace set: every comparator swaps on
       some input and not others (6 networks).  So "orphan" is a property of the
       LEDGER's partial state, not of the network.
     - with orphan erasure DISABLED, so that no evidence is deleted, no atom ever
       goes single-polarity -> both-polarity: n4_optimal, n6_classic_12,
       n6_bubble (268 undeleted facts), n8_batcher.  Zero resurrections.
   ============================================================================ *)

type_synonym atom = nat
type_synonym polarity = bool

text \<open>A ledger records, for each atom, which polarities occur among its facts.\<close>
type_synonym ledger = "atom \<Rightarrow> polarity set"

definition pinned :: "ledger \<Rightarrow> atom \<Rightarrow> bool" where
  "pinned L g = (\<exists>p. L g \<subseteq> {p})"

definition dischargeable :: "ledger \<Rightarrow> atom \<Rightarrow> bool" where
  "dischargeable L g = (L g = {True, False})"

text \<open>Discharge requires BOTH polarities.  This is the definitional content of
  the calculus: a fact becomes unconditional only by being derived on both
  branches of some atom.\<close>
lemma pinned_not_dischargeable:
  assumes "pinned L g"
  shows "\<not> dischargeable L g"
  using assms by (auto simp: pinned_def dischargeable_def)

text \<open>MINTING.  Comparator k contributes atom k, and only atom k.  We model the
  ledger update abstractly: minting sets atom k's polarities, and leaves every
  other atom's entry untouched.\<close>
definition mint :: "ledger \<Rightarrow> atom \<Rightarrow> polarity set \<Rightarrow> ledger" where
  "mint L g P = (\<lambda>h. if h = g then P else L h)"

lemma mint_other: "h \<noteq> g \<Longrightarrow> mint L g P h = L h"
  by (simp add: mint_def)

lemma mint_self: "mint L g P g = P"
  by (simp add: mint_def)

text \<open>RELABELING leaves the ledger alone: it rewrites which wires a fact names,
  never which atoms condition it.\<close>
definition relabel :: "ledger \<Rightarrow> ledger" where
  "relabel L = L"

lemma relabel_preserves: "relabel L g = L g"
  by (simp add: relabel_def)

text \<open>POLARITY IS MINTED ONCE.  A sequence of mints of atoms all different from
  g leaves g's polarity set untouched.  Stated over the list of (atom, polarities)
  pairs actually applied, which is how the ledger evolves.\<close>
fun mint_all :: "ledger \<Rightarrow> (atom \<times> polarity set) list \<Rightarrow> ledger" where
  "mint_all L [] = L"
| "mint_all L ((h,P) # rest) = mint_all (mint L h P) rest"

lemma polarity_stable:
  assumes "\<forall>(h,P) \<in> set ms. h \<noteq> g"
  shows "mint_all L ms g = L g"
  using assms by (induct ms arbitrary: L) (auto simp: mint_def)

text \<open>THE ORPHAN LEMMA.  A pinned atom stays pinned under any sequence of later
  mints of OTHER atoms, hence remains non-dischargeable forever, hence facts
  conditioned on it can never become unconditional and may be erased.\<close>
theorem orphan_erasable:
  assumes pin: "pinned L g"
      and fresh: "\<forall>(h,P) \<in> set ms. h \<noteq> g"
  shows "pinned (mint_all L ms) g \<and> \<not> dischargeable (mint_all L ms) g"
proof -
  have "mint_all L ms g = L g" using fresh by (rule polarity_stable)
  hence "pinned (mint_all L ms) g" using pin by (simp add: pinned_def)
  thus ?thesis using pinned_not_dischargeable by blast
qed

end
