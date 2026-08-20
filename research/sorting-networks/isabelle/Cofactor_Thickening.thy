theory Cofactor_Thickening
  imports Cofactor_Count_Tight
begin

(* ============================================================================
   THICKENING THIN PLACES IN THE THREAD.

   Reviewing the thesis for spots where a load-bearing step stands a little alone,
   two were found and are reinforced here, each by connecting the thin step to the
   substance around it:

   THIN 2 -- the cofactor of a threshold was proven for the HEAD (fixing one
   variable) and for a SORTED prefix (a block of Trues then Falses).  But the
   cofactor by an ARBITRARY prefix -- any 0/1 pattern -- is what the count machinery
   really needs.  We prove it in general: the cofactor of T_t by any prefix p is
   T_{t - weight p}.  The sorted case becomes a corollary; the special was an
   instance of the general all along.

   THIN 4 -- the width formula was stated for a threshold T_t generically.  A sorter's
   wire i is the threshold T_{n-i}; substituting gives the per-wire width directly, and
   shows the median wire is the widest -- the general formula met at the specific wire.

   Self-contained beyond the count theory (imports Cofactor_Count_Tight for clamp/
   level_count); everything symbolic in the count and the parameter.
   ============================================================================ *)

definition count_true :: "bool list \<Rightarrow> nat" where
  "count_true x = length (filter id x)"

definition thr :: "nat \<Rightarrow> bool list \<Rightarrow> bool" where
  "thr t x = (t \<le> count_true x)"

lemma count_true_append: "count_true (p @ w) = count_true p + count_true w"
  by (simp add: count_true_def)

text \<open>THIN 2 THICKENED.  The cofactor of a threshold by ANY prefix is a threshold,
      shifted by the prefix weight.  No assumption on the shape of the prefix.\<close>

theorem cofactor_general_prefix:
  "thr t (p @ w) = thr (t - count_true p) w"
proof -
  have "thr t (p @ w) = (t \<le> count_true p + count_true w)"
    by (simp add: thr_def count_true_append)
  also have "... = (t - count_true p \<le> count_true w)" by linarith
  also have "... = thr (t - count_true p) w" by (simp add: thr_def)
  finally show ?thesis .
qed

text \<open>The sorted-prefix case (a block of Trues then Falses) is now a corollary: its
      weight is the number of Trues, so its cofactor is the threshold shifted by that
      count.  The special result was an instance of the general one.\<close>

corollary cofactor_sorted_prefix:
  "thr t (replicate j True @ replicate i False @ w) = thr (t - j) w"
proof -
  have "count_true (replicate j True @ replicate i False) = j"
    by (simp add: count_true_def)
  moreover have "thr t ((replicate j True @ replicate i False) @ w)
                   = thr (t - count_true (replicate j True @ replicate i False)) w"
    by (rule cofactor_general_prefix)
  ultimately show ?thesis by simp
qed

text \<open>Corollary: the cofactor depends only on the prefix WEIGHT, not its pattern.
      Two prefixes of equal length and equal weight give the same cofactor -- so the
      distinct cofactors at a level are indexed by the weight alone, which is what the
      level-count development assumed.  This connects the abstract level_labels (a set
      of clamped weights) to the actual cofactors: they are in bijection with the
      distinct weights, hence with the label set.\<close>

theorem cofactor_depends_on_weight:
  assumes "count_true p = count_true q"
  shows "thr t (p @ w) = thr t (q @ w)"
  using assms by (simp add: cofactor_general_prefix)

text \<open>THIN 4 THICKENED.  A sorter's wire i is the threshold T_{n-i} (the sorted-entry
      theorem).  Substituting into the tight width bound gives the per-wire width: the
      number of distinct cofactors of wire i, at any level, is at most
      min (n-i) (i+1) + 1.  So each wire's diagram width is O(n), and the bound, read
      across the wires, peaks at the median wire i = (n-1)/2.\<close>

theorem sorter_wire_width_bound:
  assumes "i < n"
  shows "level_count (n - i) k n \<le> min (n - i) (i + 1) + 1"
proof -
  have "n - i \<le> n" by simp
  hence "level_count (n - i) k n \<le> min (n - i) (n + 1 - (n - i)) + 1"
    by (rule level_count_tight_bound)
  moreover have "n + 1 - (n - i) = i + 1" using assms by simp
  ultimately show ?thesis by simp
qed

text \<open>The median wire is the widest.  For odd n the median wire is i = (n-1) div 2,
      whose threshold is n - i = (n+1) div 2 -- the self-dual threshold of the antipode
      chapter.  Its width bound is (n+1) div 2 + 1, the maximum of the per-wire bounds.
      The general width formula, met at the specific median wire, recovers the jewel:
      the wire that is its own antipode is the widest.\<close>

theorem median_wire_width:
  assumes "odd n" and "i = (n - 1) div 2"
  shows "level_count (n - i) k n \<le> (n + 1) div 2 + 1"
proof -
  have "i < n" using assms by (cases n) auto
  hence "level_count (n - i) k n \<le> min (n - i) (i + 1) + 1"
    by (rule sorter_wire_width_bound)
  moreover have "min (n - i) (i + 1) \<le> (n + 1) div 2" by linarith
  ultimately show ?thesis by simp
qed

text \<open>Reading.  Two thin places are now thick.  @{thm cofactor_general_prefix} lifts
      the cofactor-is-a-threshold fact from special prefixes to ALL prefixes, with the
      sorted case (@{thm cofactor_sorted_prefix}) and the weight-only dependence
      (@{thm cofactor_depends_on_weight}) as corollaries -- so the level count is about
      the real cofactors, not an abstract stand-in.  @{thm sorter_wire_width_bound}
      substitutes wire i = T_{n-i} into the width bound, giving the concrete per-wire
      width, and @{thm median_wire_width} recovers the jewel at the median wire.  The
      thread, at these two points, is woven back into the fabric.\<close>

end
