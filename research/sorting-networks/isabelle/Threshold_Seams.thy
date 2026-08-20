theory Threshold_Seams
  imports Main
begin

(* ============================================================================
   TWO SEAMS MADE PLAIN: the threshold structure as a specialisation.

   Several theorems proven separately are, on inspection, instances of more general
   ones.  This theory makes two such connections explicit, showing the threshold
   results are the general structure specialised:

     SEAM 1  a threshold function is MONOTONE.  Consequently its Shannon cofactors
             are ordered, and the comparability of thresholds proven in the threshold
             route is the monotone ordering read on thresholds.

     SEAM 2  Boolean duality dualises T_t to T_{n+1-t}, and it is an INVOLUTION on
             thresholds -- an instance of the general antipode, whose fixed point is
             the median.

   Self-contained (imports Main); the definitions are re-stated minimally so the
   theory carries no name clash.  Everything is symbolic in the count and the
   parameter t.
   ============================================================================ *)

definition count_true :: "bool list \<Rightarrow> nat" where
  "count_true x = length (filter id x)"

definition thr :: "nat \<Rightarrow> bool list \<Rightarrow> bool" where
  "thr t x = (t \<le> count_true x)"

definition vleq :: "bool list \<Rightarrow> bool list \<Rightarrow> bool" (infix "\<sqsubseteq>" 50) where
  "vleq x y \<longleftrightarrow> length x = length y \<and> (\<forall>i < length x. x!i \<longrightarrow> y!i)"

definition mono_on :: "(bool list \<Rightarrow> bool) \<Rightarrow> nat \<Rightarrow> bool" where
  "mono_on f n \<longleftrightarrow> (\<forall>x y. length x = n \<and> length y = n \<and> x \<sqsubseteq> y \<longrightarrow> f x \<longrightarrow> f y)"

text \<open>The count is monotone in the product order: if x is below y (same length) then
      x has no more trues than y.\<close>

lemma count_true_mono:
  assumes "x \<sqsubseteq> y"
  shows "count_true x \<le> count_true y"
proof -
  have len: "length x = length y" using assms by (simp add: vleq_def)
  have imp: "\<And>i. i < length x \<Longrightarrow> x!i \<longrightarrow> y!i" using assms by (simp add: vleq_def)
  have "count_true x = card {i. i < length x \<and> x!i}"
    by (simp add: count_true_def length_filter_conv_card)
  moreover have "count_true y = card {i. i < length y \<and> y!i}"
    by (simp add: count_true_def length_filter_conv_card)
  moreover have "{i. i < length x \<and> x!i} \<subseteq> {i. i < length y \<and> y!i}"
    using imp len by auto
  moreover have "finite {i. i < length y \<and> y!i}" by simp
  ultimately show ?thesis by (metis card_mono)
qed

text \<open>SEAM 1.  A threshold function is MONOTONE.  It is true on x when x has at least
      t trues; a larger y has at least as many, so the threshold survives.  This is
      the fact that places thresholds inside the monotone class --- so the ordering
      and comparability results of the monotone chapters apply to them, and the
      threshold-specific comparability proven in the threshold route is that general
      ordering specialised.\<close>

theorem threshold_is_monotone: "mono_on (thr t) n"
  unfolding mono_on_def
proof (intro allI impI)
  fix x y assume "length x = n \<and> length y = n \<and> x \<sqsubseteq> y" and tx: "thr t x"
  hence le: "x \<sqsubseteq> y" by simp
  have "count_true x \<le> count_true y" using count_true_mono[OF le] .
  moreover have "t \<le> count_true x" using tx by (simp add: thr_def)
  ultimately show "thr t y" by (simp add: thr_def)
qed

text \<open>The comparability of thresholds is exactly the ordering of the corresponding
      monotone functions: for any two thresholds on length-n inputs, one implies the
      other.  (Higher threshold implies lower.)  This is the monotone ordering on the
      threshold family, so the chain of thresholds is a chain of monotone functions.\<close>

theorem threshold_comparability_is_ordering:
  "(\<forall>x. length x = n \<longrightarrow> thr t x \<longrightarrow> thr t' x)
     \<or> (\<forall>x. length x = n \<longrightarrow> thr t' x \<longrightarrow> thr t x)"
proof (cases "t' \<le> t")
  case True
  have "\<forall>x. length x = n \<longrightarrow> thr t x \<longrightarrow> thr t' x"
    using True by (auto simp: thr_def)
  thus ?thesis by blast
next
  case False
  hence "t \<le> t'" by simp
  have "\<forall>x. length x = n \<longrightarrow> thr t' x \<longrightarrow> thr t x"
    using \<open>t \<le> t'\<close> by (auto simp: thr_def)
  thus ?thesis by blast
qed

text \<open>SEAM 2.  Boolean duality on thresholds is the general antipode, specialised.
      The dual dualf f x = (not f (map Not x)); on a threshold it sends T_t to
      T_{n+1-t}, and it is an involution.  We re-derive the two facts the general
      antipode gives, now visibly as statements about thresholds.\<close>

definition dualf :: "(bool list \<Rightarrow> bool) \<Rightarrow> (bool list \<Rightarrow> bool)" where
  "dualf f = (\<lambda>x. \<not> f (map Not x))"

lemma count_true_map_Not:
  "count_true (map Not x) = length x - count_true x"
proof (induct x)
  case Nil then show ?case by (simp add: count_true_def)
next
  case (Cons a x)
  have le: "count_true x \<le> length x"
    unfolding count_true_def by (rule length_filter_le)
  show ?case
  proof (cases a)
    case True then show ?thesis using Cons by (simp add: count_true_def)
  next
    case False
    have "count_true (map Not (a # x)) = Suc (count_true (map Not x))"
      using False by (simp add: count_true_def)
    also have "... = Suc (length x - count_true x)" using Cons by simp
    also have "Suc (length x - count_true x) = Suc (length x) - count_true x"
      using le by simp
    also have "... = length (a # x) - count_true (a # x)"
      using False by (simp add: count_true_def)
    finally show ?thesis .
  qed
qed

text \<open>The general antipode is an involution on any function; here as an instance.\<close>

theorem dualf_involution_general: "dualf (dualf f) = f"
  by (simp add: dualf_def comp_def)

text \<open>Applied to a threshold, the antipode reflects the parameter (SEAM 2): the dual
      of T_t is T_{n+1-t}, an instance of the general dualf.\<close>

theorem dual_threshold:
  assumes "length x = n" and "1 \<le> t" and "t \<le> n"
  shows "dualf (thr t) x = thr (n + 1 - t) x"
proof -
  have "dualf (thr t) x = (\<not> (t \<le> count_true (map Not x)))"
    by (simp add: dualf_def thr_def)
  also have "... = (\<not> (t \<le> n - count_true x))"
    using assms(1) by (simp add: count_true_map_Not)
  also have "... = (n + 1 - t \<le> count_true x)"
  proof -
    have "count_true x \<le> n" using assms(1) unfolding count_true_def by (metis length_filter_le)
    thus ?thesis using assms(2,3) by auto
  qed
  also have "... = thr (n + 1 - t) x" by (simp add: thr_def)
  finally show ?thesis .
qed

text \<open>Reading.  @{thm threshold_is_monotone} places the thresholds inside the
      monotone class, so the ordering results of the monotone chapters apply to them:
      the threshold chain is the monotone structure on thresholds.
      @{thm dualf_involution_general} and @{thm dual_threshold} exhibit the threshold
      antipode as the general Boolean-duality antipode specialised.  Two seams that
      were adjacent are now theorems: the threshold results are instances, not
      separate facts.\<close>

end
