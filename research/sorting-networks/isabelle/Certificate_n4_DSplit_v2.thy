theory Certificate_n4_DSplit_v2
  imports TransGen Certificate_n4
begin

(* ============================================================================
   ROUTE B v1.2 — the DSplit artifact with STRUCTURAL intra-branch transitivity.

   v1.1 (Certificate_n4_DSplit.thy) proved the tc-branch fact but as a Leaf; the 1-hop
   was proven-correct (leg1/leg2) but not exhibited as a tree node. Iyun's referee named
   exactly this gap. v1.2 closes it: the tc-branch is now a GTrans node (TransGen.thy)
   exhibiting the hop through the middle value mid(v) = (run pre2 v) 0 STRUCTURALLY.

   Ground truth (dsplit_ground_truth_n4.json): tc branch = 1 hop. Now the hop IS a node:
   GTrans ctx_tc lhs mid rhs (GLeaf leg1) (GLeaf leg2), where lhs=(run pre3 v)0,
   mid=(run pre2 v)0, rhs=(run pre3 v)1. The referee's '1 hop' is now the tree's structure.
   ============================================================================ *)

section \<open>The mid-derivation state and value-expressions\<close>

definition pre3 :: network where "pre3 = [(0,1),(2,3),(0,2)]"
definition pre2 :: network where "pre2 = [(0,1),(2,3)]"

definition lhs_e :: "bool config \<Rightarrow> bool" where "lhs_e = (\<lambda>v. (run pre3 v) 0)"
definition mid_e :: "bool config \<Rightarrow> bool" where "mid_e = (\<lambda>v. (run pre2 v) 0)"
definition rhs_e :: "bool config \<Rightarrow> bool" where "rhs_e = (\<lambda>v. (run pre3 v) 1)"

text \<open>The mid fact = (vle lhs_e rhs_e) = wire0<=wire1 after col 3.\<close>
definition mid_fact2 :: "bool fact" where "mid_fact2 = vle lhs_e rhs_e"

definition ctx_tc :: "bool context_den" where
  "ctx_tc = {v \<in> all4. (run pre2 v) 2 \<le> (run pre2 v) 0}"

section \<open>The two legs, as GLeaf nodes proving value-le facts\<close>

text \<open>leg1 = (vle lhs_e mid_e) : (run pre3 v)0 <= (run pre2 v)0.
      leg2 = (vle mid_e rhs_e) : (run pre2 v)0 <= (run pre3 v)1. Both hold on ctx_tc.\<close>

text \<open>Prove each leg on the bool_configs4 enumeration (the v1.1 working pattern), then
  lift to ctx_tc via all4_configs. The legs hold on ALL configs (no branch condition
  needed for these particular legs), which makes the lift trivial.\<close>

lemma leg1_enum: "\<forall>v \<in> set bool_configs4. (run pre3 v) 0 \<le> (run pre2 v) 0"
  unfolding pre3_def pre2_def bool_configs4_def by (simp add: apply_comp_def)

lemma leg2_enum: "\<forall>v \<in> set bool_configs4. (run pre2 v) 0 \<le> (run pre3 v) 1"
  unfolding pre3_def pre2_def bool_configs4_def by (simp add: apply_comp_def)

lemma leg1_on_tc: "implies_fact ctx_tc (vle lhs_e mid_e)"
  unfolding implies_fact_def vle_def lhs_e_def mid_e_def
proof (intro ballI)
  fix v assume "v \<in> ctx_tc"
  hence "v \<in> all4" by (simp add: ctx_tc_def)
  then obtain w where w1: "w \<in> set bool_configs4" and "\<forall>k. v k = w k"
    using all4_configs by blast
  hence "v = w" by (simp add: fun_eq_iff)
  with w1 leg1_enum show "(run pre3 v) 0 \<le> (run pre2 v) 0" by auto
qed

lemma leg2_on_tc: "implies_fact ctx_tc (vle mid_e rhs_e)"
  unfolding implies_fact_def vle_def mid_e_def rhs_e_def
proof (intro ballI)
  fix v assume "v \<in> ctx_tc"
  hence "v \<in> all4" by (simp add: ctx_tc_def)
  then obtain w where w1: "w \<in> set bool_configs4" and "\<forall>k. v k = w k"
    using all4_configs by blast
  hence "v = w" by (simp add: fun_eq_iff)
  with w1 leg2_enum show "(run pre2 v) 0 \<le> (run pre3 v) 1" by auto
qed

section \<open>★ THE STRUCTURAL tc-BRANCH — a GTrans node, hop exhibited ★\<close>

definition tc_leg1 :: "bool gtree" where "tc_leg1 = GLeaf ctx_tc (vle lhs_e mid_e)"
definition tc_leg2 :: "bool gtree" where "tc_leg2 = GLeaf ctx_tc (vle mid_e rhs_e)"

definition t_tc_structural :: "bool gtree" where
  "t_tc_structural = GTrans ctx_tc lhs_e mid_e rhs_e tc_leg1 tc_leg2"

text \<open>The structural tc-branch is well-formed: both legs are GLeaf nodes holding on ctx_tc,
  and the GTrans composes them through mid_e. The 1-hop is now a NODE.\<close>

lemma tc_structural_wf: "gwell_formed t_tc_structural"
  unfolding t_tc_structural_def tc_leg1_def tc_leg2_def
  using leg1_on_tc leg2_on_tc by simp

text \<open>Hence the tc-branch proves mid_fact2 on ctx_tc — DERIVED through the explicit hop,
  not checked directly. This is what v1.1 lacked.\<close>

theorem tc_structural_derivable: "derivable ctx_tc mid_fact2"
proof -
  have "derivable (gclaim_ctx t_tc_structural) (gclaim_fact t_tc_structural)"
    using tc_structural_wf by (rule gwf_derivable)
  thus ?thesis
    by (simp add: t_tc_structural_def mid_fact2_def)
qed

section \<open>v1.2 status\<close>

text \<open>THE v1.2 CLOSURE: the tc-branch's 1-hop is now STRUCTURAL — t_tc_structural is a
  GTrans node with the two legs as GLeaf children, and tc_structural_derivable shows the
  branch fact is DERIVED through the explicit hop (via gwf_derivable), not checked as a
  Leaf. The referee gap from v1.1 is closed: 'tc: 1 hop' is now exhibited in the tree
  structure, matching the ground truth's transitivity_hops=1 as an actual node.
  (The full DSplit CoverN combining this structural tc-branch with the Oc Leaf is the
  final assembly — same shape as v1.1's dsplit_cert but with t_tc_structural in place of
  the collapsed Leaf.) Machine-checked via ./check.sh --clean.\<close>

end
