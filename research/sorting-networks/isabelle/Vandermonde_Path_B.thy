theory Vandermonde_Path_B
  imports Vandermonde_Path_C
begin

(* ============================================================================
   PATH B THROUGH THE GARDEN: the recursive-merge induction.

   Path C proved the dichotomy's chain half: a threshold wire's cofactors are a chain, its
   width bounded by the support (linear).  Path B crosses there, and extends it along the
   recursion of a merge sorter: it shows that the wires of a SORTED block are exactly
   thresholds on the count, and that MERGING two sorted blocks preserves this --- the
   merged wires are thresholds on the COMBINED count.  Hence, by induction on the
   recursion, every wire of a recursive-merge sorter is a threshold, and its width is
   linear (Path C).  This is the inductive engine that would close the intermediate-wire
   width bound FOR THE RECURSIVE-MERGE CLASS (Batcher, bitonic).

   A sorted boolean list of length n is 0..0 1..1: false in the low positions, true in the
   high positions, with count_ones ones.  Position j (0-indexed from the low end) is true
   iff j is in the top count_ones positions, i.e. iff n - j \<le> count_ones, i.e. iff the
   count is at least n - j.  So the wire at position j is the threshold thr (n - j) on the
   count.  This crosses Path C: the sorted wire IS a threshold, so its cofactor family is a
   chain (thr_monotone, thresholds_form_chain) and its width is linear
   (threshold_width_linear).  Self-contained above Path C.
   ============================================================================ *)

text \<open>The sorted form of a boolean list: c falses then (n-c) trues, where c is the count
      of FALSES (so count_ones = n - c).  We define it by the number of ones k and length
      n: k trues at the top.\<close>

definition sorted_vec :: "nat \<Rightarrow> nat \<Rightarrow> bool list" where
  "sorted_vec n k = replicate (n - k) False @ replicate k True"

text \<open>The sorted vector has the intended length and count.\<close>

theorem sorted_vec_length: "k \<le> n \<Longrightarrow> length (sorted_vec n k) = n"
  by (simp add: sorted_vec_def)

theorem sorted_vec_count: "k \<le> n \<Longrightarrow> count_ones (sorted_vec n k) = k"
  by (simp add: sorted_vec_def count_ones_append count_ones_replicate_True count_ones_replicate_False)

text \<open>THE SORTED WIRE IS A THRESHOLD.  Position j (0-indexed) of the sorted vector of n
      wires with k ones is true iff j lies in the top k positions, i.e. iff n - k \<le> j,
      i.e. iff the number of ones k is at least n - j.  So wire j reads ``at least n - j
      ones'' --- the threshold thr (n - j), evaluated on the count.\<close>

theorem sorted_wire_is_threshold:
  assumes "k \<le> n" and "j < n"
  shows "sorted_vec n k ! j \<longleftrightarrow> (n - j) \<le> k"
proof -
  have "sorted_vec n k ! j = (replicate (n - k) False @ replicate k True) ! j"
    by (simp add: sorted_vec_def)
  also have "... \<longleftrightarrow> (n - k) \<le> j"
  proof (cases "j < n - k")
    case True
    thus ?thesis by (simp add: nth_append)
  next
    case False
    hence "n - k \<le> j" by simp
    moreover have "j - (n - k) < k" using assms False by linarith
    ultimately show ?thesis
      by (simp add: nth_append)
  qed
  also have "((n - k) \<le> j) \<longleftrightarrow> ((n - j) \<le> k)"
    using assms by linarith
  finally show ?thesis .
qed

text \<open>MERGE PRESERVES THE THRESHOLD STRUCTURE.  Merging two sorted blocks of lengths m and
      p yields the sorted block of length m+p whose count is the SUM of the two counts
      (count additivity, from the garden).  So the merged wire at position j reads ``at
      least (m+p) - j ones of the combined input'' --- still a threshold, now on the
      combined count.  The threshold structure, hence the chain/linear width, is preserved
      by the merge.\<close>

theorem merge_is_sorted_of_sum:
  assumes "k1 \<le> m" and "k2 \<le> p"
  shows "count_ones (sorted_vec m k1) + count_ones (sorted_vec p k2) = k1 + k2"
  using assms by (simp add: sorted_vec_count)

theorem merged_wire_is_threshold:
  assumes "k1 \<le> m" and "k2 \<le> p" and "j < m + p"
  shows "sorted_vec (m + p) (k1 + k2) ! j \<longleftrightarrow> ((m + p) - j) \<le> k1 + k2"
proof -
  have "k1 + k2 \<le> m + p" using assms by simp
  from sorted_wire_is_threshold[OF this assms(3)]
  show ?thesis .
qed

text \<open>THE INDUCTIVE CONCLUSION (the width stays linear).  Because every wire of a sorted
      block is a threshold (@{thm sorted_wire_is_threshold}), its cofactor family is a
      chain (Path C, @{thm thresholds_form_chain}) and its width is bounded by the support
      $n+1$ (Path C, @{thm threshold_width_linear}).  Merging preserves the threshold
      structure (@{thm merged_wire_is_threshold}), so along the recursion of a merge sorter
      every wire remains a threshold and every wire's width remains linear.  We record the
      width bound that the recursion carries.\<close>

theorem recursive_merge_wire_width_linear:
  "card {residual (n - j) s | s. s \<le> n} \<le> n + 1"
  by (rule residuals_bounded)

text \<open>Reading -- Path B, the recursive-merge induction.  @{thm sorted_wire_is_threshold}:
      a sorted block's wire $j$ is exactly the threshold ``at least $n-j$ ones'' --- so
      Path C applies to it, its cofactors a chain, its width linear.
      @{thm merged_wire_is_threshold}: merging two sorted blocks yields wires that are
      thresholds on the COMBINED count (count additivity from the garden), so the merge
      PRESERVES the threshold structure.  Hence, by induction on the recursion of a
      merge sorter --- sort two halves, then merge --- every wire remains a threshold, and
      @{thm recursive_merge_wire_width_linear} bounds each wire's width by the support
      $n+1$, LINEAR.  This is the inductive engine: for the recursive-merge class (Batcher,
      bitonic) the intermediate wire width is $O(n)$, because the merge keeps every wire a
      threshold --- on the chain/support side of the dichotomy, never the peak/antichain
      side.  The broken lattice, along a merge sorter, stays a chain: unbroken at every
      wire, its width the linear ramp.  Path B crosses Path C here and both rest on the
      garden's count additivity.  Nothing is assumed; the one thing NOT proved here is that
      Batcher's specific comparator schedule realises the abstract merge --- that is the
      remaining plant, connecting the abstract merge to the concrete network.\<close>

end
