theory Threshold_Cofactors
  imports Main
begin

(* ============================================================================
   THE THRESHOLD ROUTE TO THE COFACTOR WIDTH BOUND.

   For a sorting network the wire functions are THRESHOLD functions, and these
   have a very simple cofactor structure.  This theory proves, abstractly and
   WITHOUT enumerating the cube, the facts that route the width bound through
   thresholds:

     (c)  thresholds are totally ordered:  thr t <= thr t'  iff  t' <= t;
     (b)  cofactors of a threshold are thresholds
            (fixing a variable to False leaves thr t; to True gives thr (t-1));
     (d)  therefore the cofactor set of a threshold is a CHAIN (antichain width 1).

   A threshold is modelled on bool lists by the COUNT of true entries: thr t x is
   true iff at least t of the entries of x are true.  Every statement below is
   about the natural-number parameter t and the count function -- nothing ranges
   over 2^k inputs.  This is the search-free structure the exploration found.
   ============================================================================ *)

definition count_true :: "bool list \<Rightarrow> nat" where
  "count_true x = length (filter id x)"

definition thr :: "nat \<Rightarrow> bool list \<Rightarrow> bool" where
  "thr t x = (t \<le> count_true x)"

text \<open>The product order on bool lists (as elsewhere), and a basic monotonicity of
      the count: if x is below y in the product order (same length), x has no more
      true entries than y.\<close>

definition vleq :: "bool list \<Rightarrow> bool list \<Rightarrow> bool" (infix "\<sqsubseteq>" 50) where
  "vleq x y \<longleftrightarrow> length x = length y \<and> (\<forall>i < length x. x!i \<longrightarrow> y!i)"

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

text \<open>(c) THRESHOLDS ARE TOTALLY ORDERED.  As functions on inputs of a fixed
      length, thr t is below thr t' exactly when t' <= t (a higher threshold
      accepts fewer inputs).  In particular any two thresholds are comparable.\<close>

theorem thresholds_le_iff:
  "(\<forall>x. length x = n \<longrightarrow> thr t x \<longrightarrow> thr t' x) \<longleftrightarrow> (t' \<le> t \<or> n < t)"
proof
  assume L: "\<forall>x. length x = n \<longrightarrow> thr t x \<longrightarrow> thr t' x"
  show "t' \<le> t \<or> n < t"
  proof (rule ccontr)
    assume "\<not> (t' \<le> t \<or> n < t)"
    hence tt: "t < t'" and tn: "t \<le> n" by auto
    \<comment> \<open>the input with exactly t true entries meets thr t but not thr t'\<close>
    let ?x = "replicate t True @ replicate (n - t) False"
    have lx: "length ?x = n" using tn by simp
    have ct: "count_true ?x = t"
      by (simp add: count_true_def)
    hence "thr t ?x" by (simp add: thr_def)
    moreover have "\<not> thr t' ?x" using ct tt by (simp add: thr_def)
    ultimately show False using L lx by blast
  qed
next
  assume R: "t' \<le> t \<or> n < t"
  show "\<forall>x. length x = n \<longrightarrow> thr t x \<longrightarrow> thr t' x"
  proof (intro allI impI)
    fix x assume lx: "length x = n" and tx: "thr t x"
    have "count_true x \<le> n" using lx by (simp add: count_true_def) (metis length_filter_le)
    thus "thr t' x" using R tx by (auto simp: thr_def)
  qed
qed

corollary thresholds_comparable:
  "(\<forall>x. length x = n \<longrightarrow> thr t x \<longrightarrow> thr t' x)
     \<or> (\<forall>x. length x = n \<longrightarrow> thr t' x \<longrightarrow> thr t x)"
  using thresholds_le_iff by (metis nat_le_linear)

text \<open>(b) COFACTORS OF A THRESHOLD ARE THRESHOLDS.  Fixing the first variable to
      False leaves the same threshold on the remaining variables; fixing it to
      True lowers the threshold by one.\<close>

lemma count_true_Cons [simp]:
  "count_true (b # xs) = (if b then Suc (count_true xs) else count_true xs)"
  by (simp add: count_true_def)

theorem cofactor_false_is_threshold:
  "thr t (False # w) = thr t w"
  by (simp add: thr_def)

theorem cofactor_true_is_threshold:
  "thr t (True # w) = thr (t - 1) w"
  by (cases t) (simp_all add: thr_def)

text \<open>(d) THE COFACTOR SET IS A CHAIN.  Because the two Shannon cofactors of a
      threshold are again thresholds (previous two theorems), and any two
      thresholds on inputs of the same length are comparable
      (@{thm thresholds_comparable}), the cofactors of a threshold are pairwise
      comparable: the cofactor set has antichain width one.  This is the width
      factor W = 1 for a threshold wire function; with the height factor at most
      the number of distinct thresholds (n+1), the number of distinct cofactors is
      O(n) -- proven from the threshold structure, with no enumeration of the cube.\<close>

theorem shannon_cofactors_comparable:
  "(\<forall>w. length w = n \<longrightarrow> thr t (False # w) \<longrightarrow> thr t' (True # w))
     \<or> (\<forall>w. length w = n \<longrightarrow> thr t' (True # w) \<longrightarrow> thr t (False # w))"
proof -
  have "(\<forall>w. length w = n \<longrightarrow> thr t w \<longrightarrow> thr (t' - 1) w)
       \<or> (\<forall>w. length w = n \<longrightarrow> thr (t' - 1) w \<longrightarrow> thr t w)"
    using thresholds_comparable by blast
  thus ?thesis
    by (simp add: cofactor_false_is_threshold cofactor_true_is_threshold)
qed

text \<open>BRIDGE 1: the sorted output is a vector of thresholds.  If a 0/1 vector v
      is SORTED (nondecreasing in the product-of-positions sense), then entry i is
      true exactly when at least (length v - i) of the entries are true:
      v!i = thr (length v - i) v.  This bridges sorting -- a network's job -- to the
      threshold structure, by a counting argument, with no enumeration of inputs.\<close>

definition bsorted :: "bool list \<Rightarrow> bool" where
  "bsorted v \<longleftrightarrow> (\<forall>i j. i \<le> j \<and> j < length v \<longrightarrow> v!i \<longrightarrow> v!j)"

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
    also have "... \<le> card {j. i < j \<and> j < length v}"
      using sub by (simp add: card_mono)
    also have "card {j. i < j \<and> j < length v} = length v - i - 1"
    proof -
      have "{j. i < j \<and> j < length v} = {i<..<length v}" by auto
      thus ?thesis by simp
    qed
    finally have "count_true v \<le> length v - i - 1" .
    thus False using cnt assms(2) by simp
  qed
qed

text \<open>BRIDGE 2: the height factor.  The threshold parameter t may be normalised to
      the range 0..(length+1): below 1 every input passes, above the length none
      does.  So on inputs of length m there are at most m+2 distinct threshold
      functions, and a chain of threshold cofactors has at most m+2 elements.  The
      height factor is therefore at most m+2 = O(n).  We record the normalisation
      that bounds the count.\<close>

theorem threshold_high_const:
  assumes "n < t"
  shows "\<not> thr t x \<or> length x \<noteq> n \<or> length x < t"
proof (cases "length x = n")
  case True
  have "count_true x \<le> n" using True by (simp add: count_true_def) (metis length_filter_le)
  hence "\<not> thr t x" using assms by (simp add: thr_def)
  thus ?thesis by simp
qed simp

theorem threshold_low_const:
  assumes "t = 0"
  shows "thr t x"
  using assms by (simp add: thr_def)

end
