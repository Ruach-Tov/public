theory Certificate_n4_DSplit_final
  imports Ctree Certificate_n4_DSplit_v2
begin

(* ============================================================================
   ROUTE B v1.2-final — the CANONICAL DSplit certificate on the unified ctree.

   Bocher's sequencing (2e6fecc4): build dsplit_final as the REFERENCE TARGET, referee it
   end-to-end vs ground truth, commit as THE canonical example certificate. Then the
   annotate adapter has a fixed bullseye: annotate(derive_exec compact) must produce
   exactly this (or an alpha-equivalent tree). Adapter-correctness becomes a decidable
   comparison against a refereed reference.

   REFEREE FINDING (caught building this): the branch atom must be evaluated at the
   comparator's INPUT state (run pre2 v), NOT the raw config. BranchSplit.ctx_tx uses
   branch_tx on raw v; the DSplit needs branch_tx on (run pre2 v). So dsplit_final uses
   the pre-comparator branch contexts (matching Certificate_n4_DSplit_v2's ctx_tc, which
   correctly conditions on (run pre2 v)). The Oc context is defined symmetrically.

   Structure (structural all the way down, one grammar):
     dsplit_final = CCover all4 mid_fact2 [t_Oc, t_tc]
       t_Oc = CLeaf ctx_Oc mid_fact2                              (0 hops, direct)
       t_tc = CTrans ctx_tc lhs_e mid_e rhs_e (CLeaf leg1)(CLeaf leg2)  (1 hop, structural)
   ============================================================================ *)

section \<open>The Oc branch context (symmetric to v2's ctx_tc)\<close>

definition ctx_Oc :: "bool context_den" where
  "ctx_Oc = {v \<in> all4. (run pre2 v) 0 \<le> (run pre2 v) 2}"

text \<open>The two branch contexts cover all4: every config has (run pre2 v)0 <= (run pre2 v)2
  OR (run pre2 v)2 <= (run pre2 v)0 (linear order totality). This is the covering condition
  for the DSplit on comparator (0,2) at its input state.\<close>

lemma branch_cover_all4: "exhaustive_over {ctx_Oc, ctx_tc} all4"
  unfolding exhaustive_over_def ctx_Oc_def ctx_tc_def by auto

section \<open>The Oc branch: mid_fact2 holds directly (0 hops)\<close>

text \<open>On ctx_Oc, wire0<=wire1 after col 3 holds directly. Proven via bool_configs4
  enumeration (the house pattern) + lift to all4.\<close>

lemma oc_direct_enum:
  "\<forall>v \<in> set bool_configs4. ((run pre2 v) 0 \<le> (run pre2 v) 2) \<longrightarrow> (run pre3 v) 0 \<le> (run pre3 v) 1"
  unfolding pre3_def pre2_def bool_configs4_def by (simp add: apply_comp_def)

lemma oc_branch_holds: "implies_fact ctx_Oc mid_fact2"
  unfolding implies_fact_def mid_fact2_def vle_def lhs_e_def rhs_e_def
proof (intro ballI)
  fix v assume "v \<in> ctx_Oc"
  hence oc: "v \<in> all4" "(run pre2 v) 0 \<le> (run pre2 v) 2" by (auto simp: ctx_Oc_def)
  from oc(1) obtain w where w1: "w \<in> set bool_configs4" and "\<forall>k. v k = w k"
    using all4_configs by blast
  hence "v = w" by (simp add: fun_eq_iff)
  with w1 oc(2) oc_direct_enum show "(run pre3 v) 0 \<le> (run pre3 v) 1" by auto
qed

section \<open>★ THE CANONICAL DSplit CERTIFICATE (unified ctree, structural all the way) ★\<close>

definition t_Oc_final :: "bool ctree" where
  "t_Oc_final = CLeaf ctx_Oc mid_fact2"

definition t_tc_final :: "bool ctree" where
  "t_tc_final = CTrans ctx_tc lhs_e mid_e rhs_e
                  (CLeaf ctx_tc (vle lhs_e mid_e))
                  (CLeaf ctx_tc (vle mid_e rhs_e))"

definition dsplit_final :: "bool ctree" where
  "dsplit_final = CCover all4 mid_fact2 [t_Oc_final, t_tc_final]"

text \<open>The Oc leaf is well-formed (mid_fact2 holds on ctx_Oc, 0 hops).\<close>
lemma t_Oc_final_wf: "cwf t_Oc_final"
  unfolding t_Oc_final_def by (simp add: oc_branch_holds)

text \<open>The tc branch is well-formed: a CTrans through mid_e, legs holding on ctx_tc.\<close>
lemma t_tc_final_wf: "cwf t_tc_final"
  unfolding t_tc_final_def using leg1_on_tc leg2_on_tc by simp

text \<open>The tc branch proves mid_fact2 = vle lhs_e rhs_e.\<close>
lemma t_tc_final_fact: "cfact t_tc_final = mid_fact2"
  by (simp add: t_tc_final_def mid_fact2_def)

lemma t_Oc_final_fact: "cfact t_Oc_final = mid_fact2"
  by (simp add: t_Oc_final_def)

lemma t_Oc_final_ctx: "cctx t_Oc_final = ctx_Oc"
  by (simp add: t_Oc_final_def)
lemma t_tc_final_ctx: "cctx t_tc_final = ctx_tc"
  by (simp add: t_tc_final_def)

text \<open>THE WHOLE CERTIFICATE is well-formed: both branches well-formed and prove mid_fact2,
  and their contexts {ctx_Oc, ctx_tc} cover all4.\<close>

theorem dsplit_final_wf: "cwf dsplit_final"
  unfolding dsplit_final_def
proof (simp, intro conjI)
  show "cwf t_Oc_final" by (rule t_Oc_final_wf)
  show "cwf t_tc_final" by (rule t_tc_final_wf)
  show "cfact t_Oc_final = mid_fact2" by (rule t_Oc_final_fact)
  show "cfact t_tc_final = mid_fact2" by (rule t_tc_final_fact)
  show "exhaustive_over {cctx t_Oc_final, cctx t_tc_final} all4"
    using branch_cover_all4 t_Oc_final_ctx t_tc_final_ctx by simp
qed

text \<open>★ AND THEREFORE DERIVABLE — the whole DSplit, kernel-checked, one theorem ★\<close>

theorem dsplit_final_derivable: "derivable all4 mid_fact2"
proof -
  have "derivable (cctx dsplit_final) (cfact dsplit_final)"
    using dsplit_final_wf by (rule cwf_derivable)
  thus ?thesis by (simp add: dsplit_final_def)
qed

section \<open>Canonical-certificate status\<close>

text \<open>dsplit_final is THE reference DSplit certificate: a single ctree, structural all the
  way down (Oc = 0-hop CLeaf, tc = 1-hop CTrans through mid_e), covering all4 by the
  comparator-(0,2) branch family, proven well-formed (dsplit_final_wf) and hence derivable
  (dsplit_final_derivable) via the ONE soundness theorem cwf_derivable. This is the fixed
  bullseye: the annotate adapter's output on n4 col-3 must equal this (or alpha-equivalent).
  Refereed vs dsplit_ground_truth_n4.json: Oc 0-hop direct, tc 1-hop through mid, covering
  = comparator C's family. Machine-checked via ./check.sh --clean.\<close>

end
