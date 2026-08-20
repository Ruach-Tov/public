theory BranchSplit
  imports DtreeSketch BranchAtoms
begin

(* ============================================================================
   ROUTE B v1.1 — the DSplit bridge (Iyun's half of the branch-reasoning artifact).

   A DSplit certifies a fact by splitting a context K on a comparator c into its two
   branch sub-contexts:  K_Ox = {v in K. branch_Ox c v}  and  K_tx = {v in K. branch_tx c v}.
   Since branch_exhaustive gives branch_Ox c v OR branch_tx c v for EVERY config, the
   family {K_Ox, K_tx} is exhaustive over K. So a CoverN whose two children carry these
   branch sub-contexts (and each proves phi) discharges phi on K via wf_tree_derivable.

   This is the SPEC/tree side of the DSplit: it shows the branch-split family satisfies
   the covering condition my CoverN already checks. Bocher's derive_exec emits the
   compact DSplit node (records only the comparator); this lemma is what makes the
   emitted split kernel-checkable as a covering-family discharge.

   The ground truth this must certify (dsplit_ground_truth_n4.json, from verifier.py):
   n4 col-3, comparator C=(0,2) fires, fact A<=B holds in Oc branch (0 hops) and tc
   branch (1 hop) => Oc v tc covers => A<=B unconditional. THIS lemma is the covering step.
   ============================================================================ *)

section \<open>Branch sub-contexts of a context under a comparator\<close>

definition ctx_Ox :: "comparator \<Rightarrow> ('a::linorder) context_den \<Rightarrow> 'a context_den" where
  "ctx_Ox c K = {v \<in> K. branch_Ox c v}"

definition ctx_tx :: "comparator \<Rightarrow> ('a::linorder) context_den \<Rightarrow> 'a context_den" where
  "ctx_tx c K = {v \<in> K. branch_tx c v}"

section \<open>The branch split is exhaustive over K\<close>

text \<open>{K_Ox, K_tx} covers K: every config in K is in one branch or the other, since
  branch_exhaustive gives branch_Ox OR branch_tx for every config. This is the DSplit's
  covering-family condition.\<close>

lemma branch_split_exhaustive:
  "exhaustive_over {ctx_Ox c K, ctx_tx c K} K"
  unfolding exhaustive_over_def
proof
  fix v assume "v \<in> K"
  have "branch_Ox c v \<or> branch_tx c v" by (rule branch_exhaustive)
  thus "v \<in> \<Union> {ctx_Ox c K, ctx_tx c K}"
  proof
    assume "branch_Ox c v"
    with \<open>v \<in> K\<close> have "v \<in> ctx_Ox c K" by (simp add: ctx_Ox_def)
    thus ?thesis by auto
  next
    assume "branch_tx c v"
    with \<open>v \<in> K\<close> have "v \<in> ctx_tx c K" by (simp add: ctx_tx_def)
    thus ?thesis by auto
  qed
qed

section \<open>★ THE DSPLIT DISCHARGE — a branch-split CoverN witnesses derivability ★\<close>

text \<open>If phi is derivable in BOTH branch sub-contexts, it is derivable in K. This is the
  DSplit rule as a derivability fact — the covering-family discharge specialized to the
  two-branch split. Directly from d_cover + branch_split_exhaustive.\<close>

theorem dsplit_derivable:
  assumes "derivable (ctx_Ox c K) phi"
      and "derivable (ctx_tx c K) phi"
  shows "derivable K phi"
proof (rule derivable.d_cover)
  show "\<forall>Kf \<in> {ctx_Ox c K, ctx_tx c K}. derivable Kf phi" using assms by auto
  show "exhaustive_over {ctx_Ox c K, ctx_tx c K} K" by (rule branch_split_exhaustive)
qed

text \<open>And as a self-certifying TREE: a CoverN with the two branch sub-contexts as its
  children's claims is well-formed (hence maps to derivable via wf_tree_derivable),
  provided each child is well-formed and proves phi. This is the tree-shaped DSplit that
  Bocher's derive_exec emits (compactly, recording only c).\<close>

lemma dsplit_wf_tree:
  assumes "well_formed_tree tOx" "claim_ctx tOx = ctx_Ox c K" "claim_fact tOx = phi"
      and "well_formed_tree ttx" "claim_ctx ttx = ctx_tx c K" "claim_fact ttx = phi"
  shows "well_formed_tree (CoverN K phi [tOx, ttx])"
proof -
  have "\<forall>t \<in> set [tOx, ttx]. well_formed_tree t \<and> claim_fact t = phi"
    using assms by auto
  moreover have "exhaustive_over (claim_ctx ` set [tOx, ttx]) K"
    using assms(2) assms(5) branch_split_exhaustive by simp
  ultimately show ?thesis by simp
qed

section \<open>DSplit bridge status\<close>

text \<open>The branch-split covering condition is proven: {ctx_Ox c K, ctx_tx c K} is
  exhaustive over K (branch_split_exhaustive), so (dsplit_derivable) a fact derivable in
  both branches is derivable in K, and (dsplit_wf_tree) a CoverN with the two branch
  children is well-formed = kernel-checkable via wf_tree_derivable. This is Iyun's half of
  the DSplit artifact: the covering-family discharge that makes a branch split a valid
  derivation step. Bocher's derive_exec emits the compact DSplit node; this maps it into
  the derivable spec. Together: the n4 col-3 A<=B discharge (Oc/tc covering) becomes a
  kernel-checked certificate. Machine-checked via ./check.sh.\<close>

end
