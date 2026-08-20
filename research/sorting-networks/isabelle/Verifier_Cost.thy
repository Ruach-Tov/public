theory Verifier_Cost
  imports Main
begin

(* ============================================================================
   THE COST OF THE ORDER-ONLY VERIFIER (closing Gap 4).

   The book claimed, in prose, that verifying a network by the order-only method
   costs O(comparators * W), and hence -- with the width bound -- polynomially many
   steps.  This theory machine-checks the SHAPE of that claim.

   The verifier processes the comparators one at a time.  For each it performs a
   bounded amount of diagram work: two Boolean operations on the wire functions and
   one settledness check, each costing at most a constant times the current diagram
   width.  We model the total work as a fold over the comparator list and prove:

       the total cost is at most (number of comparators) * c * (peak width).

   Substituting the proven width bound (W = O(n) for a sorter) and the comparator
   count (m = O(n * depth)) yields a polynomial total.  This is Option B of the cost
   analysis: an honest recursive cost model, bounded by induction, with no cube and
   no name clash (imports Main only).
   ============================================================================ *)

text \<open>The per-comparator work: a constant number @{term c} of diagram operations,
      each costing at most the diagram width at that step.  We take the width at a
      step as a parameter (a function of the step index), and bound the whole run.\<close>

definition step_cost :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "step_cost c w = c * w"

text \<open>The total cost is the fold of per-step costs over the comparator list.  We
      index the comparators by position; @{term "width i"} is the diagram width when
      processing comparator @{term i}.\<close>

fun run_cost :: "nat \<Rightarrow> (nat \<Rightarrow> nat) \<Rightarrow> nat \<Rightarrow> nat" where
  "run_cost c width 0 = 0" |
  "run_cost c width (Suc m) = step_cost c (width m) + run_cost c width m"

text \<open>The cost is a sum of per-step costs.\<close>

lemma run_cost_sum: "run_cost c width m = (\<Sum>i<m. step_cost c (width i))"
  by (induct m) (auto simp: add.commute)

text \<open>THE COST BOUND.  If every step's width is at most the peak @{term W}, then the
      total cost is at most @{term "m * c * W"} -- the O(m*W) claim, made precise.\<close>

theorem run_cost_bound:
  assumes "\<forall>i < m. width i \<le> W"
  shows "run_cost c width m \<le> m * (c * W)"
proof -
  have "run_cost c width m = (\<Sum>i<m. step_cost c (width i))"
    by (rule run_cost_sum)
  also have "... \<le> (\<Sum>i<m. c * W)"
  proof (rule sum_mono)
    fix i assume "i \<in> {..<m}"
    hence "i < m" by simp
    hence "width i \<le> W" using assms by simp
    thus "step_cost c (width i) \<le> c * W"
      by (simp add: step_cost_def mult_le_mono2)
  qed
  also have "... = m * (c * W)" by simp
  finally show ?thesis .
qed

text \<open>Corollary: the peak-width form.  Writing @{term W} for the peak width over the
      run, the cost is at most @{term "m * c * W"}.  This is exactly "cost is
      O(comparators * W)".\<close>

corollary arith_cost_le_mW:
  assumes "\<forall>i < m. width i \<le> W"
  shows "run_cost c width m \<le> m * c * W"
  using run_cost_bound[OF assms] by (simp add: mult.assoc)

text \<open>THE ASSEMBLY.  Substituting the proven pieces closes the polynomial claim.  If
      the number of comparators is at most @{term "n * d"} (depth d) and the peak
      width is at most @{term "k * n"} (the width bound, W = O(n) for a sorter), then
      the total cost is at most @{term "c * k * (n * n * d)"} -- polynomial in n.\<close>

theorem arith_cost_poly:
  assumes width_bound: "\<forall>i < m. width i \<le> k * n"
      and comparator_bound: "m \<le> n * d"
  shows "run_cost c width m \<le> c * k * (n * n * d)"
proof -
  have "run_cost c width m \<le> m * (c * (k * n))"
    using run_cost_bound[OF width_bound] .
  also have "... \<le> (n * d) * (c * (k * n))"
    using comparator_bound by (rule mult_le_mono1)
  also have "... = c * k * (n * n * d)" by (simp add: algebra_simps)
  finally show ?thesis .
qed

text \<open>Reading.  @{thm arith_cost_le_mW} is the O(m*W) statement Gap 4 asked to be
      machine-checked: the verifier's total work is at most the number of comparators
      times a constant times the peak diagram width.  @{thm arith_cost_poly} then
      assembles it with the two proven bounds -- the width bound (the threshold
      chain gives width at most k*n) and the comparator count (at most n*d) -- into a polynomial
      total.  The cost model is a fold over the comparators; the bound is by
      induction; nothing enumerates the cube.\<close>

end
