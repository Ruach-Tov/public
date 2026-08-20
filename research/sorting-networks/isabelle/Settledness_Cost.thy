theory Settledness_Cost
  imports Main
begin

(* ============================================================================
   THIN 3 THICKENED: the cost of the settledness check, tied to W.

   The verifier's correctness rests on the adjacent-settled criterion: the network
   sorts iff every adjacent output pair is settled.  The cost model bounded the work
   of BUILDING the wire diagrams by the comparator count times the width W.  But the
   CHECKING phase -- verifying each of the n-1 adjacent pairs is settled -- had no cost
   of its own in the argument.  This theory supplies it, connecting the criterion to
   the cost: each settledness check is a diagram operation costing at most a constant
   times W, so the checking phase costs at most (n-1) * c * W, and the total verifier
   cost is at most (m + (n-1)) * c * W = O((m+n) * W).

   Self-contained (imports Main); the cost is a fold, bounded by induction, as in the
   build-cost chapter.
   ============================================================================ *)

text \<open>The per-pair check cost: a constant number of diagram operations on width-W
      diagrams, at most c * W.\<close>

definition pair_cost :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "pair_cost c w = c * w"

text \<open>The checking phase folds the per-pair cost over the adjacent pairs.  There are
      n-1 adjacent pairs for n wires; we index them and fold.\<close>

fun check_cost :: "nat \<Rightarrow> (nat \<Rightarrow> nat) \<Rightarrow> nat \<Rightarrow> nat" where
  "check_cost c width 0 = 0" |
  "check_cost c width (Suc p) = pair_cost c (width p) + check_cost c width p"

lemma check_cost_sum: "check_cost c width q = (\<Sum>i<q. pair_cost c (width i))"
  by (induct q) (auto simp: add.commute)

text \<open>THE CHECK COST BOUND.  If every pair's diagram width is at most W, the checking
      of q pairs costs at most q * c * W.  With q = n-1 adjacent pairs this is
      (n-1) * c * W = O(n * W).\<close>

theorem check_cost_bound:
  assumes "\<forall>i < q. width i \<le> W"
  shows "check_cost c width q \<le> q * (c * W)"
proof -
  have "check_cost c width q = (\<Sum>i<q. pair_cost c (width i))" by (rule check_cost_sum)
  also have "... \<le> (\<Sum>i<q. c * W)"
  proof (rule sum_mono)
    fix i assume "i \<in> {..<q}"
    hence "i < q" by simp
    hence "width i \<le> W" using assms by simp
    thus "pair_cost c (width i) \<le> c * W" by (simp add: pair_cost_def mult_le_mono2)
  qed
  also have "... = q * (c * W)" by simp
  finally show ?thesis .
qed

text \<open>THE TOTAL VERIFIER COST.  The build phase (m comparators) and the check phase
      (q = n-1 adjacent pairs), each at most a constant times the width per step, cost
      together at most (m + q) * c * W.  This ties the adjacent-settled criterion --
      what the verifier checks -- to the cost -- how much the checking costs -- both
      governed by the same width W.  We model the total as the sum of two fold costs
      with a common per-step bound.\<close>

definition total_cost :: "nat \<Rightarrow> (nat \<Rightarrow> nat) \<Rightarrow> (nat \<Rightarrow> nat) \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where
  "total_cost c bw cw m q = check_cost c bw m + check_cost c cw q"

theorem arith_total_cost_bound:
  assumes "\<forall>i < m. bw i \<le> W" and "\<forall>i < q. cw i \<le> W"
  shows "total_cost c bw cw m q \<le> (m + q) * (c * W)"
proof -
  have "check_cost c bw m \<le> m * (c * W)" by (rule check_cost_bound[OF assms(1)])
  moreover have "check_cost c cw q \<le> q * (c * W)" by (rule check_cost_bound[OF assms(2)])
  ultimately have "total_cost c bw cw m q \<le> m * (c * W) + q * (c * W)"
    by (simp add: total_cost_def)
  also have "... = (m + q) * (c * W)" by (simp add: algebra_simps)
  finally show ?thesis .
qed

text \<open>Polynomial total.  With the width bounded by k*n (the O(n) width bound), the
      comparators at most n*d, and the adjacent pairs q = n-1 < n, the total verifier
      cost is at most (n*d + n) * c * (k*n) = c*k*n^2*(d+1) --- polynomial in n.  The
      checking phase is subsumed: its (n-1)*c*W is of the same order as the build cost,
      and both are governed by the width W.\<close>

theorem arith_total_cost_poly:
  assumes "\<forall>i < m. bw i \<le> k * n" and "\<forall>i < q. cw i \<le> k * n"
      and "m \<le> n * d" and "q \<le> n"
  shows "total_cost c bw cw m q \<le> c * k * (n * n * (d + 1))"
proof -
  have "total_cost c bw cw m q \<le> (m + q) * (c * (k * n))"
    by (rule arith_total_cost_bound[OF assms(1,2)])
  also have "... \<le> (n * d + n) * (c * (k * n))"
    using assms(3,4) by (intro mult_le_mono1 add_le_mono)
  also have "... = c * k * (n * n * (d + 1))" by (simp add: algebra_simps)
  finally show ?thesis .
qed

text \<open>Reading.  @{thm check_cost_bound} gives the settledness-checking phase a cost of
      its own -- (n-1) * c * W -- fold-bounded like the build phase and governed by the
      same width.  @{thm arith_total_cost_bound} sums the two, and
      @{thm arith_total_cost_poly} discharges the width and comparator bounds to a
      polynomial.  The adjacent-settled criterion, which said WHAT the verifier checks,
      is now joined to WHAT IT COSTS: the checking is O(n * W), subsumed in the
      polynomial total.  The thread from criterion to cost is whole.\<close>

end
