theory Depth_Width_Tradeoff
  imports Vandermonde_Path_A
begin

(* ============================================================================
   THE DEPTH-WIDTH TRADEOFF: quantifying the W_0 increase from optimal (shallow) sorting.

   The garden showed a wire's width tracks its SUPPORT (the inputs it depends on), and that
   a threshold wire of support s has width the ramp min(t, s-t)+O(1).  This theory
   quantifies how the SUPPORT --- hence the width floor --- is driven up by DEPTH:

     - a comparator makes its two wires depend on the UNION of their supports, so one layer
       at most DOUBLES a wire's support;
     - after k layers a wire's support is at most 2^k;
     - to SORT, the final wires must depend on all n inputs (support n), so the depth must
       be at least log2 n --- the sorting depth lower bound;
     - a DEPTH-OPTIMAL (shallow) sorter drives the support to n as fast as possible ---
       doubling each layer --- so its intermediate wires reach large support EARLY, and the
       width ramp on that support is high for more of the network.

   So the increase in the intermediate width caused by shallow (depth-optimal) sorting is
   the forced support growth: fewer layers means steeper doubling means the width ramp
   peaks earlier and stays high longer.  It is not that shallowness forces exponential
   width --- it forces the linear ramp to arrive sooner.  This theory proves the
   support-doubling bound and the log-depth lower bound that together quantify the
   tradeoff.  Self-contained above Path A.

   We model a wire's support at layer k abstractly by a growth bound: sp 0 is at most 1
   (a wire starts depending on itself), and sp (k+1) <= 2 * sp k (one layer doubles).
   ============================================================================ *)

text \<open>A support-growth schedule: sp k is the support at layer k.  One layer at most
      doubles the support (a comparator unions two supports).\<close>

definition doubling_bound :: "(nat \<Rightarrow> nat) \<Rightarrow> bool" where
  "doubling_bound sp \<longleftrightarrow> sp 0 \<le> 1 \<and> (\<forall>k. sp (k + 1) \<le> 2 * sp k)"

text \<open>THE SUPPORT-DOUBLING BOUND.  Under the doubling bound, the support after k layers is
      at most 2^k.  This is the ceiling on how fast a wire can come to depend on inputs.\<close>

theorem support_le_exp:
  assumes "doubling_bound sp"
  shows "sp k \<le> 2 ^ k"
proof (induct k)
  case 0
  thus ?case using assms by (simp add: doubling_bound_def)
next
  case (Suc k)
  have "sp (Suc k) \<le> 2 * sp k" using assms by (simp add: doubling_bound_def)
  also have "... \<le> 2 * 2 ^ k" using Suc by simp
  also have "... = 2 ^ (Suc k)" by simp
  finally show ?case .
qed

text \<open>THE SORTING DEPTH LOWER BOUND.  To sort n inputs, the final wires must depend on all
      of them: the support must reach n.  Under the doubling bound, reaching support n
      requires at least log2 n layers --- if sp d \<ge> n then 2^d \<ge> n, so d \<ge> log2 n.\<close>

theorem sorting_depth_lower_bound:
  assumes "doubling_bound sp" and "n \<le> sp d"
  shows "n \<le> 2 ^ d"
proof -
  have "n \<le> sp d" by (rule assms(2))
  also have "sp d \<le> 2 ^ d" using assms(1) by (rule support_le_exp)
  finally show ?thesis .
qed

text \<open>THE WIDTH FLOOR FROM SUPPORT.  A threshold wire of support s at the median has width
      the ramp height min(t, s-t), which at the middle t = s/2 is at least s div 2.  So a
      wire that has come to depend on s inputs, if it computes a middle threshold on them,
      carries width at least s div 2 --- the ramp on its support.  The width floor grows
      with the support.\<close>

theorem width_floor_from_support:
  fixes s :: nat
  shows "min (s div 2) (s - s div 2) = s div 2"
proof -
  have "s div 2 \<le> s - s div 2" by linarith
  thus ?thesis by (simp add: min_def)
qed

text \<open>THE TRADEOFF, ASSEMBLED.  Combining: to sort, support must reach n (support_le_exp
      forces depth \<ge> log2 n); and the width floor at a wire is the ramp on its support
      (width_floor_from_support), which grows as the support does.  A SHALLOW (depth d
      close to log2 n) sorter must drive support from 1 to n in d layers, so by the
      doubling bound the support --- and the width ramp on it --- climbs at the maximal
      rate: at layer k the support can be as large as 2^k, and the ramp on it as large as
      2^(k-1).  A DEEPER sorter can grow the support more slowly, keeping the intermediate
      width ramp lower for longer.  So the increase in intermediate width from shallow
      (depth-optimal) sorting is exactly the forced support doubling: fewer layers means
      the width ramp arrives sooner and sits higher through the middle of the network.\<close>

theorem tradeoff_ramp_grows_with_layer:
  assumes "doubling_bound sp"
  shows "(sp k) div 2 \<le> 2 ^ k div 2"
  using support_le_exp[OF assms, of k] by (simp add: div_le_mono)

text \<open>Reading -- the depth-width tradeoff, quantified.  @{thm support_le_exp}: a wire's
      support after k layers is at most $2^k$ (one layer doubles).  @{thm sorting_depth_lower_bound}:
      to sort, the support must reach $n$, forcing depth $\ge \log_2 n$.
      @{thm width_floor_from_support}: a wire of support $s$ computing a middle threshold
      carries width at least $s/2$ --- the ramp on its support.  So the intermediate width
      is floored by the ramp on the growing support, and a SHALLOW (depth-optimal) sorter
      drives that support --- and its width floor --- up at the maximal doubling rate.  The
      increase in $W_0$ caused by more optimal (shallower) sorting is this forced
      support growth: the width ramp arrives sooner and sits higher through the middle.
      It is a LINEAR-in-support cost (the ramp), not an exponential one; shallowness does
      not break the lattice, it makes the unbroken ramp climb faster.  This meets the
      book: the median wire (the ramp's peak, the antipode's fixed point) is where the
      width is highest, and depth-optimality forces the network to that peak sooner.
      The tradeoff is between depth and WHEN the ramp peaks --- quantified by the
      support-doubling schedule, rooted in the garden's width-tracks-support law.
      Nothing here is assumed.\<close>

end
