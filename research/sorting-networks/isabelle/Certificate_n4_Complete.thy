theory Certificate_n4_Complete
  imports Certificate_n4 CertificateA
begin

(* ============================================================================
   ROUTE B — CLOSING THE CHAIN: formal `sorts 4 n4_net`.

   Iyun's referee pass found the final "n4 SORTS" was PROSE in Certificate_n4.thy, not a
   theorem. This file discharges it, upgrading the artifact's claim from "the deriver
   found certificates" to "THIS FILE PROVES THE NETWORK SORTS" — the one-line sentence
   the product needs. Uses run_agree_below (DischargeCalculus, general cert-lifting infra)
   + the capstone machinery (CertificateA).
   ============================================================================ *)

section \<open>Certificates give the adjacent output facts on the all4 context\<close>

lemma post_fact_holds:
  assumes "n4.derive_exec 1 orc0 all4 (post_fact a b) \<noteq> None"
  shows "\<forall>v \<in> all4. (run n4_net v) a \<le> (run n4_net v) b"
proof -
  from assms obtain t where "n4.derive_exec 1 orc0 all4 (post_fact a b) = Some t" by auto
  hence "derivable all4 (post_fact a b)" by (rule n4.exec_sound)
  hence "implies_fact all4 (post_fact a b)" by (rule derivable_sound)
  thus ?thesis by (auto simp: implies_fact_def post_fact_def)
qed

lemma adj01: "\<forall>v \<in> all4. (run n4_net v) 0 \<le> (run n4_net v) 1"
  using post_fact_holds[OF cert_01] .
lemma adj12: "\<forall>v \<in> all4. (run n4_net v) 1 \<le> (run n4_net v) 2"
  using post_fact_holds[OF cert_12] .
lemma adj23: "\<forall>v \<in> all4. (run n4_net v) 2 \<le> (run n4_net v) 3"
  using post_fact_holds[OF cert_23] .

section \<open>n4_net is well-formed below 4\<close>

lemma n4_wf: "wf_net_lt 4 n4_net"
  by (simp add: wf_net_lt_def n4_net_def)

section \<open>Every bool config sorts under n4_net (lift all4 -> all configs)\<close>

lemma n4_sorts_cfg: "sorted_cfg 4 (run n4_net (v :: bool config))"
proof -
  \<comment> \<open>Restrict v to its all4-representative v'; run agrees on wires < 4 (run_agree_below);
     the certificates give adjacent-monotone on v'; transitivity gives all i<j<4.\<close>
  define v' :: "bool config" where
    "v' = (\<lambda>k. if k < 4 then v k else False)"
  have v'4: "v' \<in> all4" by (simp add: all4_def v'_def)
  have agree: "agree_below 4 v' v" by (simp add: agree_below_def v'_def)
  have run_ag: "agree_below 4 (run n4_net v') (run n4_net v)"
    using n4_wf agree by (rule run_agree_below)
  hence run_eq: "\<And>k. k < 4 \<Longrightarrow> (run n4_net v') k = (run n4_net v) k"
    by (auto simp: agree_below_def)
  from adj01 adj12 adj23 v'4
  have a01: "(run n4_net v') 0 \<le> (run n4_net v') 1"
   and a12: "(run n4_net v') 1 \<le> (run n4_net v') 2"
   and a23: "(run n4_net v') 2 \<le> (run n4_net v') 3" by auto
  let ?w = "run n4_net v'"
  have c01: "?w 0 \<le> ?w 1" and c12: "?w 1 \<le> ?w 2" and c23: "?w 2 \<le> ?w 3"
    using a01 a12 a23 by simp_all
  \<comment> \<open>all six ordered pairs below 4 follow from the adjacent chain by transitivity\<close>
  have c02: "?w 0 \<le> ?w 2" using c01 c12 by (rule order_trans)
  have c13: "?w 1 \<le> ?w 3" using c12 c23 by (rule order_trans)
  have c03: "?w 0 \<le> ?w 3" using c02 c23 by (rule order_trans)
  show ?thesis
    unfolding sorted_cfg_def
  proof (intro allI impI)
    fix i j :: nat assume ij: "i < j" and j4: "j < 4"
    \<comment> \<open>i<j<4: (i,j) is one of six pairs; get the disjunction fast via linarith\<close>
    have six: "(i=0\<and>j=1)\<or>(i=0\<and>j=2)\<or>(i=0\<and>j=3)\<or>(i=1\<and>j=2)\<or>(i=1\<and>j=3)\<or>(i=2\<and>j=3)"
      using ij j4 by linarith
    have "?w i \<le> ?w j"
      using six c01 c12 c23 c02 c13 c03 by fastforce
    thus "(run n4_net v) i \<le> (run n4_net v) j"
      using run_eq ij j4 by simp
  qed
qed

section \<open>★ THE CLOSING THEOREM — n4_net SORTS (formal, capstone-tied) ★\<close>

theorem n4_sorts: "sorts 4 n4_net"
  unfolding sorts_def using n4_sorts_cfg by blast

text \<open>DONE. n4_net is PROVEN to sort — a formal theorem, not prose — via the complete
  Route B chain: derive_exec (search) -> exec_sound -> derivable -> derivable_sound ->
  the three adjacent output facts (on all4) -> run_agree_below lifts to all configs ->
  sorted_cfg -> sorts. The artifact now says: THIS FILE PROVES THE NETWORK SORTS, tied to
  the same `sorts` predicate the 4-file correctness proof and sorts_bool_eq_sorts are about.\<close>

end
