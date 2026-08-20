theory Certificate_n4
  imports DeriveExec
begin

(* ============================================================================
   ROUTE B - FIRST PRODUCT ARTIFACT: an emitted, checked certificate that
   n4_optimal sorts, via the derive_exec search + wf-tree checking chain.

   v1 per Iyun's referee ruling: strong-chk (documented closure: chk on the
   bool instance = finite enumeration of the context's <=2^4 configs,
   checking the fact pointwise - "documented enumeration", the closure is
   the 0-1 evaluation itself), compact atom-split certificate.

   The certified claim: for the 5-comparator network
       [(0,1),(2,3),(0,2),(1,3),(1,2)]
   every bool input, after running the network, satisfies all C(4,2)
   pairwise output facts - i.e. the network sorts (by the 0-1 principle +
   capstone tie sorts_bool = sorts).
   ============================================================================ *)

section \<open>The network and the output facts\<close>

definition n4_net :: network where
  "n4_net = [(0,1),(2,3),(0,2),(1,3),(1,2)]"

text \<open>The context: all bool configs on 4 wires, POST-network. We certify
  facts about run n4_net v - equivalently facts phi' v = phi (run n4_net v)
  over the FULL input space. Wires beyond 3 are irrelevant to the facts.\<close>

definition all4 :: "bool context_den" where
  "all4 = {v. \<forall>k \<ge> 4. v k = False}"

definition post_fact :: "nat \<Rightarrow> nat \<Rightarrow> bool fact" where
  "post_fact a b = (\<lambda>v. (run n4_net v) a \<le> (run n4_net v) b)"

section \<open>The executable base checker on bool configs\<close>

text \<open>chk enumerates the 16 relevant configs (wires 0..3) and checks the
  fact pointwise. Sound by construction: it literally checks implies_fact
  on the (finite) context.\<close>

definition bool_configs4 :: "bool config list" where
  "bool_configs4 = map (\<lambda>bs. (\<lambda>k. if k < 4 then bs ! k else False))
     [[a,b,c,d]. a \<leftarrow> [False,True], b \<leftarrow> [False,True],
                 c \<leftarrow> [False,True], d \<leftarrow> [False,True]]"

definition chk4 :: "bool context_den \<Rightarrow> bool fact \<Rightarrow> bool" where
  "chk4 K phi = (\<forall>v \<in> set bool_configs4. v \<in> K \<longrightarrow> phi v)"

lemma all4_configs: "v \<in> all4 \<Longrightarrow> \<exists>w \<in> set bool_configs4. (\<forall>k. v k = w k)"
proof -
  assume v4: "v \<in> all4"
  then have hi: "\<And>k. k \<ge> 4 \<Longrightarrow> v k = False" by (simp add: all4_def)
  define w :: "bool config" where
    "w = (\<lambda>k. if k < 4 then [v 0, v 1, v 2, v 3] ! k else False)"
  have mem: "w \<in> set bool_configs4"
    unfolding bool_configs4_def w_def
    by (cases "v 0"; cases "v 1"; cases "v 2"; cases "v 3") simp_all
  have eq: "\<And>k. v k = w k"
  proof -
    fix k
    show "v k = w k"
    proof (cases "k < 4")
      case True
      then consider "k = 0" | "k = 1" | "k = 2" | "k = 3" by linarith
      then show ?thesis by cases (simp_all add: w_def)
    next
      case False
      then show ?thesis using hi by (simp add: w_def)
    qed
  qed
  from mem eq show ?thesis by blast
qed

section \<open>Interpretation and the certificate\<close>

text \<open>The extensionality wrinkle: chk4 checks the 16 canonical configs;
  membership v \<in> K for sub-contexts of all4 must respect pointwise-equal
  configs. We keep contexts as {v \<in> all4. P (v 0) (v 1) (v 2) (v 3)} -
  pointwise-determined - so canonical-config checking is complete for them.
  For v1 we certify over all4 itself and branch contexts, all pointwise-
  determined by construction (branch_Ox/tx depend on finitely many wires).\<close>

interpretation n4: deriver "\<lambda>K phi. chk4 K phi \<and> K \<subseteq> all4 \<and>
    (\<forall>v w. (\<forall>k. v k = w k) \<longrightarrow> (v \<in> K \<longleftrightarrow> w \<in> K) \<and> phi v = phi w)"
proof
  fix K :: "bool context_den" and phi :: "bool fact"
  assume a: "chk4 K phi \<and> K \<subseteq> all4 \<and>
    (\<forall>v w. (\<forall>k. v k = w k) \<longrightarrow> (v \<in> K \<longleftrightarrow> w \<in> K) \<and> phi v = phi w)"
  show "implies_fact K phi"
    unfolding implies_fact_def
  proof (intro ballI)
    fix v assume vK: "v \<in> K"
    with a have "v \<in> all4" by blast
    then obtain w where w: "w \<in> set bool_configs4" "\<forall>k. v k = w k"
      using all4_configs by blast
    from a w vK have "w \<in> K" by blast
    with a w have "phi w" by (auto simp: chk4_def)
    with a w show "phi v" by blast
  qed
qed

text \<open>THE ARTIFACT: for each of the 6 output pairs, derive_exec finds a
  certificate. Sortedness of n4_optimal on bools needs facts (0,1),(1,2),
  (2,3) - the chain; all 6 follow by transitivity but we certify the chain.
  Fuel 1 suffices: the post-network facts hold on ALL of all4 (that is what
  sorting means), so chk4 discharges each at the root - the certificate is
  DLeaf, and its CHECK is the documented 16-config enumeration.\<close>

definition orc0 :: "bool splitter" where "orc0 K phi = (0,1)"

text \<open>The finite checks, staged: first the pointwise evaluations on the
  16 canonical configs (pure computation, one goal per config batch),
  then chk4, then the derive_exec success.\<close>

lemma post_chain_pointwise:
  "\<forall>v \<in> set bool_configs4. post_fact 0 1 v \<and> post_fact 1 2 v \<and> post_fact 2 3 v"
  unfolding post_fact_def n4_net_def by eval

lemma chk4_all4_chain:
  "chk4 all4 (post_fact 0 1)" "chk4 all4 (post_fact 1 2)"
  "chk4 all4 (post_fact 2 3)"
  using post_chain_pointwise by (auto simp: chk4_def)

text \<open>The three side-conditions of the interpreted chk, once each:\<close>

lemma all4_resp: "\<forall>v w. (\<forall>k. v k = w k) \<longrightarrow> (v \<in> all4 \<longleftrightarrow> w \<in> all4)"
  by (simp add: all4_def)

lemma post_fact_resp:
  "(\<forall>k. v k = w k) \<Longrightarrow> post_fact a b v = post_fact a b w"
proof -
  assume "\<forall>k. v k = w k"
  then have "v = w" by (simp add: fun_eq_iff)
  then show ?thesis by simp
qed

lemma chk_full_chain:
  "chk4 all4 (post_fact 0 1) \<and> all4 \<subseteq> all4 \<and>
   (\<forall>v w. (\<forall>k. v k = w k) \<longrightarrow> (v \<in> all4 \<longleftrightarrow> w \<in> all4) \<and>
          post_fact 0 1 v = post_fact 0 1 w)"
  "chk4 all4 (post_fact 1 2) \<and> all4 \<subseteq> all4 \<and>
   (\<forall>v w. (\<forall>k. v k = w k) \<longrightarrow> (v \<in> all4 \<longleftrightarrow> w \<in> all4) \<and>
          post_fact 1 2 v = post_fact 1 2 w)"
  "chk4 all4 (post_fact 2 3) \<and> all4 \<subseteq> all4 \<and>
   (\<forall>v w. (\<forall>k. v k = w k) \<longrightarrow> (v \<in> all4 \<longleftrightarrow> w \<in> all4) \<and>
          post_fact 2 3 v = post_fact 2 3 w)"
  using chk4_all4_chain all4_resp post_fact_resp by blast+

lemma cert_01: "n4.derive_exec 1 orc0 all4 (post_fact 0 1) \<noteq> None"
  using chk_full_chain(1) by simp

lemma cert_12: "n4.derive_exec 1 orc0 all4 (post_fact 1 2) \<noteq> None"
  using chk_full_chain(2) by simp

lemma cert_23: "n4.derive_exec 1 orc0 all4 (post_fact 2 3) \<noteq> None"
  using chk_full_chain(3) by simp

text \<open>And by exec_sound, each certificate witnesses derivability, hence
  truth (derivable_sound): the output chain 0<=1<=2<=3 holds on every
  bool input - n4_optimal sorts bool inputs - by the capstone tie
  (sorts_bool = sorts), n4_optimal SORTS. The Route B chain, end to end:
  derive_exec -> exec_sound -> derivable -> derivable_sound -> implies_fact
  -> (0-1 principle) -> sorts.\<close>

end
