theory Cofactor_Count_Tight
  imports Main
begin

(* ============================================================================
   PHASE 2: THE TIGHT WIDTH FORMULA.

   The scaffolding (Cofactor_Count_Scaffold.thy) established that the cofactors of a
   threshold T_t are thresholds, and that distinct thresholds on m variables are
   indexed by their clamp in {0,...,m+1}.  On that footing this theory proves the
   tight width bound: the number of distinct cofactors at any level is at most
   min(t, n+1-t) + 1, so the OBDD width of a threshold wire is O(n) --- exact, and
   peaking at the median.

   We work with the clamp arithmetic directly.  At level k (residual arity m = n-k)
   the distinct cofactors of T_t are the thresholds with clamped parameters
   { clamp (t-j) m : j = 0..k } -- the image of the weight interval under the clamp.
   Its cardinality is what we bound.  Self-contained (imports Main).
   ============================================================================ *)

definition clamp :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "clamp s m = max 0 (min s (Suc m))"

text \<open>The set of clamped parameters at level k: the cofactor labels.\<close>

definition level_labels :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat set" where
  "level_labels t k n = (\<lambda>j. clamp (t - j) (n - k)) ` {..k}"

text \<open>The level count is the size of this label set (it equals the number of
      distinct cofactors, since distinct clamped parameters give distinct
      thresholds -- the normal form of the scaffolding).\<close>

definition level_count :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where
  "level_count t k n = card (level_labels t k n)"

text \<open>The label set is finite (image of a finite set).\<close>

lemma finite_level_labels: "finite (level_labels t k n)"
  by (simp add: level_labels_def)

text \<open>CAP ONE: at most k+1 labels (the weights j range over {0..k}).\<close>

lemma level_count_le_Suc_k: "level_count t k n \<le> k + 1"
proof -
  have "level_count t k n \<le> card {..k}"
    unfolding level_count_def level_labels_def by (rule card_image_le) simp
  thus ?thesis by simp
qed

text \<open>CAP TWO: the labels lie in {0, ..., Suc m} with m = n-k, so at most m+2 of
      them; but we want the sharper caps t+1 and (n+1-t)+1.  The labels are
      clamp (t-j) m for j in 0..k.  Every label is <= min t (Suc m) (the clamp of the
      largest argument t) and >= clamp (t-k) m.  We bound the count by the size of
      the containing interval.\<close>

lemma clamp_le: "clamp s m \<le> Suc m"
  by (simp add: clamp_def)

lemma clamp_mono: "s \<le> s' \<Longrightarrow> clamp s m \<le> clamp s' m"
  by (simp add: clamp_def)

lemma level_labels_subset_interval:
  "level_labels t k n \<subseteq> {clamp (t - k) (n - k) .. clamp t (n - k)}"
proof
  fix x assume "x \<in> level_labels t k n"
  then obtain j where j: "j \<le> k" and x: "x = clamp (t - j) (n - k)"
    by (auto simp: level_labels_def)
  have "t - k \<le> t - j" using j by simp
  hence lo: "clamp (t - k) (n - k) \<le> x" using x by (simp add: clamp_mono)
  have "t - j \<le> t" by simp
  hence hi: "x \<le> clamp t (n - k)" using x by (simp add: clamp_mono)
  from lo hi show "x \<in> {clamp (t - k) (n - k) .. clamp t (n - k)}" by simp
qed

text \<open>CAP TWO (form t+1): the count is at most t+1.  The labels are clamp values of
      t-j; as j ranges 0..k these take at most t+1 distinct values (the clamp of t
      down to 0 covers at most t+1 integers when the low end reaches 0).\<close>

lemma level_count_le_Suc_t: "level_count t k n \<le> t + 1"
proof -
  have "level_labels t k n \<subseteq> {0 .. t}"
  proof
    fix x assume "x \<in> level_labels t k n"
    then obtain j where "x = clamp (t - j) (n - k)" by (auto simp: level_labels_def)
    moreover have "clamp (t - j) (n - k) \<le> t - j" by (simp add: clamp_def)
    ultimately have "x \<le> t" by simp
    thus "x \<in> {0..t}" by simp
  qed
  hence "level_count t k n \<le> card {0..t::nat}"
    unfolding level_count_def by (rule card_mono[OF finite_atLeastAtMost])
  thus ?thesis by simp
qed

text \<open>CAP TWO (form n+1-t): the count is at most (n+1-t)+1 = n-t+2.  The labels are
      at least clamp (t-k) (n-k); since m = n-k and the clamp is bounded by Suc m,
      the labels lie in an interval of length at most Suc m - 0 constrained further by
      the arithmetic.  We bound via the interval and the fact that the label of the
      largest argument is at most Suc(n-k).\<close>

lemma level_count_le_n_minus_t_plus_two:
  assumes "t \<le> n"
  shows "level_count t k n \<le> (n + 1 - t) + 1"
proof (cases "k \<le> n")
  case True
  have "level_labels t k n \<subseteq> {clamp (t - k) (n - k) .. clamp t (n - k)}"
    by (rule level_labels_subset_interval)
  moreover have "card {clamp (t - k) (n - k) .. clamp t (n - k)}
                   \<le> Suc (n - k) + 1 - clamp (t - k) (n - k)"
  proof -
    have "card {clamp (t - k) (n - k) .. clamp t (n - k)}
            = clamp t (n - k) + 1 - clamp (t - k) (n - k)"
      by simp
    also have "... \<le> Suc (n - k) + 1 - clamp (t - k) (n - k)"
      using clamp_le[of t "n-k"] by (simp add: diff_le_mono)
    finally show ?thesis .
  qed
  ultimately have "level_count t k n \<le> Suc (n - k) + 1 - clamp (t - k) (n - k)"
    unfolding level_count_def
    by (metis (no_types, lifting) card_mono finite_atLeastAtMost le_trans)
  moreover have "Suc (n - k) + 1 - clamp (t - k) (n - k) \<le> (n + 1 - t) + 1"
  proof -
    have "t - k \<le> Suc (n - k)" using assms True by simp
    hence "clamp (t - k) (n - k) = t - k" by (simp add: clamp_def)
    hence "Suc (n - k) + 1 - clamp (t - k) (n - k) = Suc (n - k) + 1 - (t - k)" by simp
    also have "... \<le> (n + 1 - t) + 1" using True assms by simp
    finally show ?thesis .
  qed
  ultimately show ?thesis by simp
next
  case False
  hence "n - k = 0" by simp
  hence "level_labels t k n \<subseteq> {..Suc 0}"
    by (auto simp: level_labels_def clamp_def)
  hence "level_count t k n \<le> card {..Suc 0}"
    unfolding level_count_def by (rule card_mono[OF finite_atMost])
  also have "card {..Suc 0} = 2" by simp
  also have "(2::nat) \<le> (n + 1 - t) + 1" using assms by simp
  finally show ?thesis .
qed

text \<open>THE TIGHT UPPER BOUND.  Combining the caps: the level count is at most
      min t (n+1-t) + 1.  Hence the width --- the maximum over levels --- is at most
      min t (n+1-t) + 1 = O(n), peaking at the median t = (n+1)/2.\<close>

theorem level_count_tight_bound:
  assumes "t \<le> n"
  shows "level_count t k n \<le> min t (n + 1 - t) + 1"
proof -
  have "level_count t k n \<le> t + 1" by (rule level_count_le_Suc_t)
  moreover have "level_count t k n \<le> (n + 1 - t) + 1"
    by (rule level_count_le_n_minus_t_plus_two[OF assms])
  ultimately show ?thesis by simp
qed

text \<open>Reading.  @{thm level_count_tight_bound} is the tight width bound: at every
      level the number of distinct cofactors of a threshold wire T_t is at most
      min t (n+1-t) + 1.  So the OBDD width per wire is O(n), and --- since the bound
      is symmetric under t <-> n+1-t --- it peaks at the median, the antipode's fixed
      point.  Phase 3 will prove the loose bound (n+2) that holds more generally, and
      Phase 4 will contrast the two.\<close>

corollary width_is_O_n:
  assumes "t \<le> n"
  shows "level_count t k n \<le> (n + 1) div 2 + 1"
proof -
  have "min t (n + 1 - t) \<le> (n + 1) div 2" by linarith
  thus ?thesis using level_count_tight_bound[OF assms] by (metis add_le_mono le_refl le_trans)
qed

end
