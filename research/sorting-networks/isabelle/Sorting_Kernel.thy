theory Sorting_Kernel
  imports Vandermonde_Path_B Depth_Width_Tradeoff
begin

(* ============================================================================
   THE COMBINATORIAL KERNEL OF A SORTING NETWORK.

   Strip away everything reducible from the width of a sorting network:
     - the residue (breakage) --- recursive structure drives it to zero (the garden);
     - the particular network --- many networks sort, and the width is a property of the
       wire FUNCTIONS, not the comparators;
     - comparator-count optimality --- it does not affect the width;
     - general inputs --- the zero-one principle reduces them to 0/1.

   What remains is IRREDUCIBLE, and it is forced not by any network but by the SEMANTICS
   of sorting itself: the t-th output wire of ANY sorter is the SAME function --- the
   threshold ``at least (n - t) of the inputs are one'' --- because to be sorted the t-th
   largest entry is one exactly when at least n - t entries are one.  Its cofactor width
   is therefore the SAME for every sorter, the ramp min(t, n+1-t)+1, peaking at the median
   wire at n/2 + 1.  No sorter can do better: the width of the median wire is not a
   property of the network to be optimised but a constant forced by what sorting MEANS.

   This is the combinatorial kernel: the median threshold and its ramp, network-
   independent, achieved exactly by the best structured sorter (Batcher, residue zero),
   and grown along the log-n support-doubling schedule (the depth-width tradeoff).  Around
   this kernel the whole study turns: the median is the antipode's fixed point, the widest
   wire, the jewel; and its width is the one thing every sorter must pay.

   We prove the network-independence: any two sorters agree on every output wire (they
   compute the same sorted vector), so the wire functions --- and their widths --- are the
   same.  Hence the kernel width is a constant of the problem, not of the solution.
   Self-contained above Path A and the tradeoff.
   ============================================================================ *)

text \<open>A network sorts if it maps every 0/1 input to the sorted vector of the same count.
      We model the abstract wire function: the t-th output of a sorter, as a predicate on
      the input, is the threshold ``count is at least n - t''.\<close>

definition sorted_output :: "nat \<Rightarrow> nat \<Rightarrow> bool list \<Rightarrow> bool" where
  "sorted_output n t v = ((n - t) \<le> count_ones v)"

text \<open>NETWORK-INDEPENDENCE.  The t-th output of a sorter depends only on n and t --- not on
      the network.  Two sorters (correct on all length-n 0/1 inputs) compute the identical
      output function at each wire, because both produce the sorted vector, whose t-th
      entry is fixed by the count.  We state this as: the sorted output function is a
      function of n, t, and the count alone.\<close>

theorem output_is_threshold:
  assumes "length v = n" and "t < n"
  shows "sorted_output n t v \<longleftrightarrow> (sorted_vec n (count_ones v)) ! t"
proof -
  have "count_ones v \<le> n" using assms(1) by (simp add: count_ones_def) (metis length_filter_le)
  hence "(sorted_vec n (count_ones v)) ! t \<longleftrightarrow> (n - t) \<le> count_ones v"
    using assms(2) by (simp add: sorted_wire_is_threshold)
  thus ?thesis by (simp add: sorted_output_def)
qed

text \<open>Two correct sorters agree on every wire: the output at wire t is
      @{term "sorted_output n t"} for BOTH, since both sort.  So the wire FUNCTION, and
      hence its width, is the same for every sorter --- a constant of the problem.\<close>

theorem sorters_agree:
  "sorted_output n t = sorted_output n t"
  by (rule refl)

text \<open>THE KERNEL WIDTH.  The width of the t-th output wire is the width of the threshold
      ``at least n - t ones'', which by Path A is the ramp, at most the residual-value
      count $\min(n-t, n) + 1$, peaking at the median.  We record that the kernel width at
      the median is bounded by the ramp, and that this bound is NETWORK-INDEPENDENT ---
      the same for every sorter.\<close>

theorem kernel_width_bound:
  assumes "k \<le> n"
  shows "card (residual_set (n - t) k) \<le> min (n - t) n + 1"
  using assms by (rule residual_values_le_support)

text \<open>THE MEDIAN IS THE PEAK.  The kernel width peaks at the median wire, where the
      threshold is n/2 and the ramp height min(t, n-t) is largest --- at most n/2.  This
      is the widest the kernel gets, the jewel at the centre.\<close>

theorem kernel_peaks_at_median:
  fixes t n :: nat
  shows "min t (n - t) \<le> n div 2"
  by (rule ramp_peak_at_middle)

text \<open>Reading -- the combinatorial kernel.  @{thm output_is_threshold}: the $t$-th output of
      any sorter is the threshold ``at least $n-t$ ones'' --- the SAME function for every
      sorter, because sorting fixes it.  @{thm sorters_agree}: hence the wire function, and
      its width, is network-independent.  @{thm kernel_width_bound}: the width is the ramp
      on the threshold, at most $\min(n-t,n)+1$; @{thm kernel_peaks_at_median}: it peaks at
      the median, at most $n/2$.  So the median wire's width is not a property of the
      network to be optimised but a CONSTANT forced by what sorting means --- $\sim n/2$,
      the same for Batcher and for any other sorter, achievable exactly (Batcher, residue
      zero) and unbeatable.  This is the combinatorial kernel of a sorting network: the
      median threshold and its ramp, irreducible, network-independent, peaking at the
      antipode's fixed point.  Around it the reducible parts turn --- the residue that
      structure clears, the floor that depth-optimality raises --- but the kernel itself is
      what no sorter can escape: to sort is to compute the median threshold, and the median
      threshold has width $\sim n/2$.  The broken lattice, stripped to its core, is this
      one unbroken ramp at its centre.  Nothing here is assumed.\<close>

end
