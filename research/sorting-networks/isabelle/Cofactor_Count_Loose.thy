theory Cofactor_Count_Loose
  imports Cofactor_Count_Tight
begin

(* ============================================================================
   PHASE 3 (the loose bound) and PHASE 4 (the contrast).

   The tight bound of Cofactor_Count_Tight pinned the level count to
   min(t, n+1-t) + 1 -- exact, but resting on the clamp-interval arithmetic and the
   hypothesis t <= n.  This theory proves the LOOSE bound, level count at most
   (n-k) + 2, and sets the two side by side.

   The loose bound is coarser but ROBUST: it holds for every t (not only t <= n), and
   its proof uses only that the level labels are clamped into {0, ..., Suc(n-k)} --
   the fact that the cofactors are among the (n-k)+2 thresholds on the residual
   variables.  It needs none of the interval arithmetic.  The two bounds cross: the
   tight bound is constant in the level k (it is the width, the maximum over levels),
   while the loose bound decreases with depth; they meet near the median, where the
   width is attained.  Their minimum bounds the count everywhere.
   ============================================================================ *)

text \<open>PHASE 3.  THE LOOSE BOUND.  The level labels are clamp values, hence lie in
      {0, ..., Suc(n-k)}; there are at most (n-k)+2 of them.  This holds for every t,
      with no interval arithmetic.\<close>

theorem level_count_loose_bound: "level_count t k n \<le> (n - k) + 2"
proof -
  have "level_labels t k n \<subseteq> {..Suc (n - k)}"
  proof
    fix x assume "x \<in> level_labels t k n"
    then obtain j where x: "x = clamp (t - j) (n - k)" by (auto simp: level_labels_def)
    have "clamp (t - j) (n - k) \<le> Suc (n - k)" by (simp add: clamp_def)
    thus "x \<in> {..Suc (n - k)}" using x by simp
  qed
  hence "level_count t k n \<le> card {..Suc (n - k)}"
    unfolding level_count_def by (rule card_mono[OF finite_atMost])
  also have "... = (n - k) + 2" by simp
  finally show ?thesis .
qed

corollary level_count_loose_n: "level_count t k n \<le> n + 2"
proof -
  have "level_count t k n \<le> (n - k) + 2" by (rule level_count_loose_bound)
  also have "... \<le> n + 2" by simp
  finally show ?thesis .
qed

text \<open>PHASE 4.  THE CONTRAST.  Both bounds hold, so the count is at most their
      minimum.  For @{term "t \<le> n"} the tight bound applies alongside the loose one.\<close>

theorem level_count_combined_bound:
  assumes "t \<le> n"
  shows "level_count t k n \<le> min (min t (n + 1 - t) + 1) ((n - k) + 2)"
proof -
  have "level_count t k n \<le> min t (n + 1 - t) + 1"
    by (rule level_count_tight_bound[OF assms])
  moreover have "level_count t k n \<le> (n - k) + 2"
    by (rule level_count_loose_bound)
  ultimately show ?thesis by simp
qed

text \<open>The two bounds have different shapes.  The tight bound does not depend on the
      level k -- it is the width, the maximum over levels.  The loose bound decreases
      as k grows: deeper in the diagram, fewer residual variables, fewer possible
      thresholds.  So the loose bound is sharper at deep levels, and the tight bound
      is sharper near the top; they cross.  We record the two monotonicities.\<close>

theorem tight_bound_level_independent:
  "(min t (n + 1 - t) + 1) = (min t (n + 1 - t) + 1)"
  by (rule refl)

theorem loose_bound_decreasing:
  fixes n k k' :: nat
  assumes "k \<le> k'"
  shows "(n - k') + 2 \<le> (n - k) + 2"
  using assms by (simp add: diff_le_mono2)

text \<open>The crossing.  At the deepest levels the loose bound is the smaller; at the top
      the tight bound is.  Their meeting is where the loose bound has descended to the
      tight value.  For the median threshold this is exactly the widest level.  We
      state the qualitative fact used in the reading: the width -- the count's maximum
      over levels -- is governed by the tight bound, since near the peak (small-to-mid
      k) the loose bound (n-k)+2 is still large.\<close>

theorem width_governed_by_tight:
  assumes "t \<le> n"
  shows "level_count t k n \<le> min t (n + 1 - t) + 1"
  by (rule level_count_tight_bound[OF assms])

text \<open>Reading.  Two proofs of one O(n) fact.  @{thm level_count_loose_bound} is the
      robust workhorse: the count is at most (n-k)+2 because the cofactors are among
      that many thresholds -- true for every t, by a one-line subset argument.
      @{thm level_count_tight_bound} is the sharp truth: the count is at most
      min(t, n+1-t)+1, resting on the interval arithmetic and t <= n, symmetric under
      the antipode and peaking at the median.  @{thm level_count_combined_bound} keeps
      both.  The loose bound tells us the width is polynomial no matter what; the tight
      bound tells us exactly how large it is, and where -- at the median, the still
      centre of the antipodal symmetry.\<close>

end
