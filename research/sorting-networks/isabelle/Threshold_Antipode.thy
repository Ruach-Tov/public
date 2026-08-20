theory Threshold_Antipode
  imports Main
begin

(* ============================================================================
   A DIVERSION: THE THRESHOLD ANTIPODE (for its own sake).

   The goal of the book is reached; this theory is play.  It proves, for the
   pleasure of it, how the antipode acts on the threshold functions --- the objects
   a sorter's wires realise --- and finds a small delight: the antipode has a fixed
   point exactly when n is odd, and that fixed point is the MEDIAN threshold.  The
   wire that is its own antipode is the median wire; and (as the exploration
   measured) that same median wire is where the decision diagram is widest.  The
   centre of the antipodal symmetry is the peak of the difficulty.

   The Boolean dual of a function is dual f x = (not f (map Not x)).  A threshold
   T_t on n-bit inputs is true iff at least t of the bits are true.  Self-contained
   (imports Main); everything is symbolic in the count and the parameter t.
   ============================================================================ *)

definition count_true :: "bool list \<Rightarrow> nat" where
  "count_true x = length (filter id x)"

definition thr :: "nat \<Rightarrow> bool list \<Rightarrow> bool" where
  "thr t x = (t \<le> count_true x)"

definition dualf :: "(bool list \<Rightarrow> bool) \<Rightarrow> (bool list \<Rightarrow> bool)" where
  "dualf f = (\<lambda>x. \<not> f (map Not x))"

text \<open>Complementing a bit list complements the count: the number of trues in
      @{term "map Not x"} is @{term "length x - count_true x"}.\<close>

lemma count_true_map_Not:
  "count_true (map Not x) = length x - count_true x"
proof (induct x)
  case Nil then show ?case by (simp add: count_true_def)
next
  case (Cons a x)
  show ?case
  proof (cases a)
    case True
    then show ?thesis using Cons by (simp add: count_true_def)
  next
    case False
    have le: "count_true x \<le> length x" unfolding count_true_def by (rule length_filter_le)
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

text \<open>THE THRESHOLD ANTIPODE.  On inputs of length n, the dual of the threshold
      T_t is the threshold T_{n+1-t}: "at least t are true" dualises to "at least
      n+1-t are true".  (A higher bar becomes a lower one, reflected about the
      midpoint.)\<close>

theorem dual_threshold:
  assumes "length x = n" and "1 \<le> t" and "t \<le> n"
  shows "dualf (thr t) x = thr (n + 1 - t) x"
proof -
  have "dualf (thr t) x = (\<not> thr t (map Not x))"
    by (simp add: dualf_def)
  also have "... = (\<not> (t \<le> count_true (map Not x)))"
    by (simp add: thr_def)
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

text \<open>THE FIXED POINT.  The threshold T_t is self-dual on length-n inputs exactly
      when @{term "2 * t = n + 1"} --- which has a (unique) solution iff n is odd,
      namely the median @{term "t = (n + 1) div 2"}.  So among a sorter's wires,
      one is its own antipode precisely when n is odd, and it is the median wire.\<close>

theorem threshold_self_dual_iff:
  assumes "1 \<le> t" and "t \<le> n"
  shows "(\<forall>x. length x = n \<longrightarrow> dualf (thr t) x = thr t x) \<longleftrightarrow> (2 * t = n + 1)"
proof
  assume L: "\<forall>x. length x = n \<longrightarrow> dualf (thr t) x = thr t x"
  \<comment> \<open>the dual is T_{n+1-t}; equal to T_t on all length-n inputs forces the
      parameters equal (thresholds on length n are distinct for parameters in
      range), hence t = n+1-t.\<close>
  have "\<forall>x. length x = n \<longrightarrow> thr (n + 1 - t) x = thr t x"
    using L dual_threshold[OF _ assms] by simp
  \<comment> \<open>the input with exactly (t-1) trues separates T_t (false) from T_{t-1}\<close>
  hence eq: "thr (n + 1 - t) = thr t \<or> (\<forall>x. length x = n \<longrightarrow> thr (n+1-t) x = thr t x)"
    by blast
  have "t = n + 1 - t"
  proof (rule ccontr)
    assume ne: "t \<noteq> n + 1 - t"
    show False
    proof (cases "t < n + 1 - t")
      case True
      \<comment> \<open>an input with exactly t trues: meets T_t, not T_{n+1-t}\<close>
      let ?x = "replicate t True @ replicate (n - t) False"
      have lx: "length ?x = n" using assms by simp
      have "count_true ?x = t" by (simp add: count_true_def)
      hence "thr t ?x" and "\<not> thr (n+1-t) ?x"
        using True by (simp_all add: thr_def)
      thus False using L lx dual_threshold[OF lx assms] by simp
    next
      case False
      hence gt: "n + 1 - t < t" using ne by simp
      let ?x = "replicate (n+1-t) True @ replicate (t-1) False"
      have lx: "length ?x = n" using assms by simp
      have "count_true ?x = n + 1 - t" by (simp add: count_true_def)
      hence "thr (n+1-t) ?x" and "\<not> thr t ?x"
        using gt by (simp_all add: thr_def)
      thus False using L lx dual_threshold[OF lx assms] by simp
    qed
  qed
  thus "2 * t = n + 1" using assms by simp
next
  assume R: "2 * t = n + 1"
  hence "n + 1 - t = t" by simp
  thus "\<forall>x. length x = n \<longrightarrow> dualf (thr t) x = thr t x"
    using dual_threshold[OF _ assms] by simp
qed

text \<open>Reading.  @{thm dual_threshold} is the threshold antipode: duality reflects
      the parameter about @{term "(n+1)/2"}.  @{thm threshold_self_dual_iff} finds
      its fixed point: a threshold is self-dual iff its parameter is the median
      @{term "(n+1)/2"}, which is an integer iff n is odd.  A sorter's median wire,
      for odd n, is its own antipode --- the still centre of the antipodal symmetry,
      and (as the diagrams show) the widest wire.\<close>

end
