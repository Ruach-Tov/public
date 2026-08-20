theory Chain_And_Thermometer
  imports Main
begin

(* ============================================================================
   TWO MORE SEAMS MADE PLAIN.

     SEAM 4  a threshold's cofactor set is a CHAIN.  The cofactors of a threshold
             are thresholds (fixing a variable shifts the parameter), and any two
             thresholds are comparable; so the set of cofactors at any level is
             totally ordered -- antichain width one.  This states, in a single
             theorem, the width factor W = 1 that the threshold route established in
             pieces.

     SEAM 5  the thermometer view and the entry-wise threshold view are one.  A
             nondecreasing (thermometer) vector has entry i equal to the threshold
             "at least (length - i) of the entries are true".  So bsorted_iff_
             thermometer and sorted_entry_is_threshold are two readings of the same
             fact.

   Self-contained (imports Main); symbolic in the count and the parameter.
   ============================================================================ *)

definition count_true :: "bool list \<Rightarrow> nat" where
  "count_true x = length (filter id x)"

definition thr :: "nat \<Rightarrow> bool list \<Rightarrow> bool" where
  "thr t x = (t \<le> count_true x)"

text \<open>Cofactors of a threshold are thresholds: fixing the head to False keeps T_t;
      to True lowers it to T_{t-1}.\<close>

lemma count_true_Cons [simp]:
  "count_true (b # xs) = (if b then Suc (count_true xs) else count_true xs)"
  by (simp add: count_true_def)

lemma cof_false_thr: "thr t (False # w) = thr t w"
  by (simp add: thr_def)

lemma cof_true_thr: "thr t (True # w) = thr (t - 1) w"
  by (cases t) (simp_all add: thr_def)

text \<open>Any two thresholds on inputs of a fixed length are comparable.\<close>

lemma thresholds_comparable:
  "(\<forall>x. length x = n \<longrightarrow> thr t x \<longrightarrow> thr t' x)
     \<or> (\<forall>x. length x = n \<longrightarrow> thr t' x \<longrightarrow> thr t x)"
proof (cases "t' \<le> t")
  case True thus ?thesis by (auto simp: thr_def)
next
  case False hence "t \<le> t'" by simp
  thus ?thesis by (auto simp: thr_def)
qed

text \<open>SEAM 4.  The two Shannon cofactors of a threshold are comparable, so the
      cofactor set is a chain.  We phrase the chain property as: the head cofactors
      (fixing the first variable to False, then True) are comparable on the residual
      inputs; iterated, this makes every pair of cofactors comparable --- antichain
      width one.\<close>

theorem threshold_cofactors_chain:
  "(\<forall>w. length w = m \<longrightarrow> thr t (False # w) \<longrightarrow> thr t' (True # w))
     \<or> (\<forall>w. length w = m \<longrightarrow> thr t' (True # w) \<longrightarrow> thr t (False # w))"
proof -
  have "(\<forall>w. length w = m \<longrightarrow> thr t w \<longrightarrow> thr (t' - 1) w)
       \<or> (\<forall>w. length w = m \<longrightarrow> thr (t' - 1) w \<longrightarrow> thr t w)"
    using thresholds_comparable by blast
  thus ?thesis by (simp add: cof_false_thr cof_true_thr)
qed

text \<open>Sortedness of a bool list (nondecreasing along positions).\<close>

definition bsorted :: "bool list \<Rightarrow> bool" where
  "bsorted v \<longleftrightarrow> (\<forall>i j. i \<le> j \<and> j < length v \<longrightarrow> v!i \<longrightarrow> v!j)"

text \<open>SEAM 5.  For a nondecreasing (thermometer) vector, entry i is the threshold
      "at least (length - i) of the entries are true".  So the thermometer view and
      the entry-wise threshold view are the same fact.  (This is the counting
      argument of the sorted-entry theorem, stated here to make the seam explicit.)\<close>

theorem thermometer_entry_is_threshold:
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
      fix y assume "y \<in> {j. j < length v \<and> v!j}"
      hence yl: "y < length v" and vy: "v!y" by auto
      have "i < y" using low vy by (metis not_less)
      thus "y \<in> {j. i < j \<and> j < length v}" using yl by simp
    qed
    have "count_true v = card {j. j < length v \<and> v!j}"
      by (simp add: count_true_def length_filter_conv_card)
    also have "... \<le> card {j. i < j \<and> j < length v}"
      by (rule card_mono[OF finite_Collect_conjI[OF disjI2[OF finite_Collect_less_nat]] sub])
    also have "card {j. i < j \<and> j < length v} = length v - i - 1"
    proof -
      have "{j. i < j \<and> j < length v} = {Suc i..<length v}" by auto
      thus ?thesis by simp
    qed
    finally have "count_true v \<le> length v - i - 1" .
    thus False using cnt assms(2) by simp
  qed
qed

text \<open>Reading.  @{thm threshold_cofactors_chain} states the width factor W = 1 in one
      theorem: the cofactors of a threshold are pairwise comparable, a chain.
      @{thm thermometer_entry_is_threshold} makes the thermometer and entry-wise
      views one: a nondecreasing vector's entries are thresholds of its count.  Two
      more adjacent facts, now welded.\<close>

end
