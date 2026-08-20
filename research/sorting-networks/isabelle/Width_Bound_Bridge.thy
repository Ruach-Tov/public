theory Width_Bound_Bridge
  imports Main
begin

(* EXPERIMENTAL self-contained bridge -- avoids the bsorted name-clash that made the
   two-import version slow. Re-states the minimal defs (thr, count_true, bsorted) and
   proves the Gap-1 + Gap-3 welds directly. If fast, we know the clash was the cause. *)

definition count_true :: "bool list \<Rightarrow> nat" where
  "count_true x = length (filter id x)"
definition thr :: "nat \<Rightarrow> bool list \<Rightarrow> bool" where
  "thr t x = (t \<le> count_true x)"
definition bsorted :: "bool list \<Rightarrow> bool" where
  "bsorted v \<longleftrightarrow> (\<forall>i j. i \<le> j \<and> j < length v \<longrightarrow> v!i \<longrightarrow> v!j)"

text \<open>GAP 1: a sorted vector's entry i is the threshold (length - i).\<close>
theorem sorted_entry_is_threshold:
  assumes "bsorted v" and "i < length v"
  shows "v!i = thr (length v - i) v"
proof
  assume vi: "v!i"
  have suf: "\<And>j. \<lbrakk>i \<le> j; j < length v\<rbrakk> \<Longrightarrow> v!j"
    using assms(1) vi assms(2) by (auto simp: bsorted_def)
  have "{i..<length v} \<subseteq> {j. j < length v \<and> v!j}" using suf by auto
  moreover have "card {i..<length v} = length v - i" by simp
  moreover have "count_true v = card {j. j < length v \<and> v!j}"
    by (simp add: count_true_def length_filter_conv_card)
  moreover have "finite {j. j < length v \<and> v!j}" by simp
  ultimately have "length v - i \<le> count_true v" by (metis card_mono)
  thus "thr (length v - i) v" by (simp add: thr_def)
next
  assume "thr (length v - i) v"
  hence cnt: "length v - i \<le> count_true v" by (simp add: thr_def)
  show "v!i"
  proof (rule ccontr)
    assume nvi: "\<not> v!i"
    have low: "\<And>j. j \<le> i \<Longrightarrow> \<not> v!j"
      using assms(1) nvi assms(2) by (auto simp: bsorted_def)
    have sub: "{j. j < length v \<and> v!j} \<subseteq> {j. i < j \<and> j < length v}"
    proof
      fix x assume "x \<in> {j. j < length v \<and> v!j}"
      hence xl: "x < length v" and vx: "v!x" by auto
      have "i < x" using low vx by (metis not_less)
      thus "x \<in> {j. i < j \<and> j < length v}" using xl by simp
    qed
    have "count_true v = card {j. j < length v \<and> v!j}"
      by (simp add: count_true_def length_filter_conv_card)
    also have "... \<le> card {j. i < j \<and> j < length v}" using sub by (simp add: card_mono)
    also have "card {j. i < j \<and> j < length v} = length v - i - 1"
    proof -
      have "{j. i < j \<and> j < length v} = {i<..<length v}" by auto
      thus ?thesis by simp
    qed
    finally have "count_true v \<le> length v - i - 1" .
    thus False using cnt assms(2) by simp
  qed
qed

text \<open>GAP 3: at most n+2 distinct thresholds on length-n inputs.\<close>
definition thr_on :: "nat \<Rightarrow> nat \<Rightarrow> (bool list \<Rightarrow> bool)" where
  "thr_on n t = (\<lambda>x. if length x = n then thr t x else undefined)"
theorem distinct_thresholds_le: "card (thr_on n ` {0..Suc n}) \<le> n + 2"
proof -
  have "card (thr_on n ` {0..Suc n}) \<le> card {0..Suc n}" by (rule card_image_le) simp
  also have "card {0..Suc n} = n + 2" by simp
  finally show ?thesis .
qed

end
