theory Comparator_Monotone
  imports Main
begin

(* ============================================================================
   COMPARATOR NETWORKS ARE MONOTONE.

   The foundational lemma for the reduced-operations-BDD width argument: the wire
   functions a comparator network computes are monotone Boolean functions of the
   input bits.  Stated on 0/1 vectors as the product order:

       x <= y   ==>   run net x  <=  run net y      (both componentwise)

   Proof by induction on the comparator list.  Base case: the empty network is the
   identity, trivially monotone.  Inductive step: one comparator replaces
   (v!a, v!b) by (min, max); min and max are monotone, and monotonicity is closed
   under a single comparator step, so the step preserves the property.

   This is the machine-checked counterpart of tools/comparator_monotone.py, whose
   TDD tests pin the exact statement (exhaustive at n<=5).
   ============================================================================ *)

text \<open>A 0/1 vector is a bool list.  The product order is the pointwise \<open><=\<close>.\<close>

definition vleq :: "bool list \<Rightarrow> bool list \<Rightarrow> bool" (infix "\<sqsubseteq>" 50) where
  "vleq x y \<longleftrightarrow> length x = length y \<and> (\<forall>i < length x. x!i \<longrightarrow> y!i)"

text \<open>One comparator on adjacent-or-not positions \<open>a < b\<close>: put the min at \<open>a\<close>,
      the max at \<open>b\<close>.  On booleans, min = conjunction, max = disjunction.\<close>

definition comp_step :: "nat \<Rightarrow> nat \<Rightarrow> bool list \<Rightarrow> bool list" where
  "comp_step a b v = v[a := (v!a \<and> v!b), b := (v!a \<or> v!b)]"

fun run :: "(nat \<times> nat) list \<Rightarrow> bool list \<Rightarrow> bool list" where
  "run [] v = v" |
  "run ((a,b) # cs) v = run cs (comp_step a b v)"

text \<open>Length is preserved by a comparator step and by the whole network.\<close>

lemma length_comp_step [simp]: "length (comp_step a b v) = length v"
  by (simp add: comp_step_def)

lemma length_run [simp]: "length (run cs v) = length v"
  by (induct cs arbitrary: v) (auto simp: length_comp_step split: prod.split)

text \<open>The inductive heart: a single comparator step is monotone in the product
      order.  We require the touched indices to be in range; outside the two
      touched positions the vectors are unchanged, and at the two positions the
      new values are conjunction/disjunction of monotone inputs.\<close>

lemma comp_step_mono:
  assumes "x \<sqsubseteq> y" and "a < length x" and "b < length x" and "a < b"
  shows "comp_step a b x \<sqsubseteq> comp_step a b y"
proof -
  have len: "length x = length y" using assms(1) by (simp add: vleq_def)
  have imp: "\<And>i. i < length x \<Longrightarrow> x!i \<longrightarrow> y!i"
    using assms(1) by (simp add: vleq_def)
  { fix i assume iL: "i < length x"
    have "(comp_step a b x)!i \<longrightarrow> (comp_step a b y)!i"
      using assms(2,3,4) len imp[OF assms(2)] imp[OF assms(3)] imp[OF iL] iL
      by (cases "i=a"; cases "i=b"; simp add: comp_step_def nth_list_update) }
  thus ?thesis using len by (simp add: vleq_def comp_step_def)
qed

text \<open>A network is \emph{well-formed} on length \<open>n\<close> if every comparator touches
      in-range positions.  Under that hypothesis the whole network is monotone.\<close>

definition wf_net :: "(nat \<times> nat) list \<Rightarrow> nat \<Rightarrow> bool" where
  "wf_net cs n \<longleftrightarrow> (\<forall>(a,b) \<in> set cs. a < b \<and> b < n)"

lemma run_mono:
  "wf_net cs n \<Longrightarrow> x \<sqsubseteq> y \<Longrightarrow> length x = n \<Longrightarrow> run cs x \<sqsubseteq> run cs y"
proof (induct cs arbitrary: x y)
  case Nil
  then show ?case by simp
next
  case (Cons c cs)
  obtain a b where c: "c = (a,b)" by (cases c)
  have wf_c: "a < b \<and> b < n" using Cons.prems(1) c by (auto simp: wf_net_def)
  have wf_rest: "wf_net cs n" using Cons.prems(1) by (auto simp: wf_net_def)
  have lx: "length x = n" using Cons.prems(3) .
  have aL: "a < length x" using wf_c lx by simp
  have bL: "b < length x" using wf_c lx by simp
  have ab: "a < b" using wf_c by simp
  have step: "comp_step a b x \<sqsubseteq> comp_step a b y"
    using comp_step_mono[OF Cons.prems(2) aL bL ab] .
  have lstep: "length (comp_step a b x) = n" using lx by simp
  have "run cs (comp_step a b x) \<sqsubseteq> run cs (comp_step a b y)"
    using Cons.hyps[OF wf_rest step lstep] .
  thus ?case using c by simp
qed

text \<open>THE LEMMA (comparator networks are monotone).\<close>

theorem comparator_network_monotone:
  assumes "wf_net cs n" and "x \<sqsubseteq> y" and "length x = n"
  shows "run cs x \<sqsubseteq> run cs y"
  using run_mono[OF assms] .

text \<open>Corollary: each wire function is monotone.  If \<open>x \<sqsubseteq> y\<close> then the value on
      any wire \<open>i\<close> cannot drop from output(x) to output(y).\<close>

corollary wire_function_monotone:
  assumes "wf_net cs n" and "x \<sqsubseteq> y" and "length x = n" and "i < n"
  shows "(run cs x)!i \<longrightarrow> (run cs y)!i"
proof -
  have "run cs x \<sqsubseteq> run cs y" using comparator_network_monotone[OF assms(1-3)] .
  moreover have "i < length (run cs x)" using assms(3,4) by simp
  ultimately show ?thesis by (simp add: vleq_def)
qed

end
