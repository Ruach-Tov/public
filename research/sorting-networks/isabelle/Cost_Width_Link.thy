theory Cost_Width_Link
  imports Main
begin

(* ============================================================================
   THE ARITHMETIC OF THE COST FOLD (schematic; see Cost_Honest for the closed form).

   This theory proves the ARITHMETIC fact that a sum of m terms, each at most c*W, is
   at most m*c*W.  Its `width` is a FREE PARAMETER: the theorems here are correct about
   sequences of naturals, but they say nothing about an actual network -- a hypothesis
   `width i <= n+2` is met by CHOOSING a width, not by proving a bound.  Instantiating a
   variable is not discharging an assumption.  The HONEST, network-grounded headline --
   width DEFINED from the network, resting on a named `sorry` for the intermediate-wire
   bound -- is in Cost_Honest.thy.  This theory is retained only for the underlying
   arithmetic lemma run_cost_bound.

   Self-contained (imports Main) to avoid name clashes; the cost fold and the width
   fact are re-stated minimally.  The end-to-end statement is
   arith_cost_at_width_np2: with the width bounded by n+2, the verifier's cost is
   bounded by m*c*(n+2).
   ============================================================================ *)

text \<open>The per-comparator work and the cost fold, as in the cost chapter.\<close>

definition step_cost :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "step_cost c w = c * w"

fun run_cost :: "nat \<Rightarrow> (nat \<Rightarrow> nat) \<Rightarrow> nat \<Rightarrow> nat" where
  "run_cost c width 0 = 0" |
  "run_cost c width (Suc m) = step_cost c (width m) + run_cost c width m"

lemma run_cost_sum: "run_cost c width m = (\<Sum>i<m. step_cost c (width i))"
  by (induct m) (auto simp: add.commute)

text \<open>The cost bound, re-proved here so the theory is self-contained.\<close>

lemma run_cost_bound:
  assumes "\<forall>i < m. width i \<le> W"
  shows "run_cost c width m \<le> m * (c * W)"
proof -
  have "run_cost c width m = (\<Sum>i<m. step_cost c (width i))" by (rule run_cost_sum)
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

text \<open>THE WELD.  For a sorting network the per-step diagram width is at most n+2
      (the cofactor set is a chain of at most n+2 thresholds --- the threshold route
      and the count theorem) -- but ONLY for the FINAL wires.  Here the width is a free
      parameter and the bound is ASSUMED, not proved for a network; this is arithmetic, not a
      network theorem.  The premise is met by instantiating W := n+2, and proves nothing about cs.\<close>

theorem arith_cost_at_width_np2:
  assumes width_le: "\<forall>i < m. width i \<le> n + 2"
  shows "run_cost c width m \<le> m * (c * (n + 2))"
  using run_cost_bound[OF width_le] .

text \<open>Polynomial form.  With the comparator count at most n*d (depth d), the cost is
      at most n*d * c * (n+2), which is at most c * ((n+2) * (n * d)) --- a polynomial
      in n (degree two in n, linear in the depth).\<close>

theorem arith_cost_poly_np2:
  assumes width_le: "\<forall>i < m. width i \<le> n + 2"
      and comps_le: "m \<le> n * d"
  shows "run_cost c width m \<le> c * ((n + 2) * (n * d))"
proof -
  have "run_cost c width m \<le> m * (c * (n + 2))"
    using arith_cost_at_width_np2[OF width_le] .
  also have "... \<le> (n * d) * (c * (n + 2))"
    using comps_le by (rule mult_le_mono1)
  also have "... = c * ((n + 2) * (n * d))" by (simp add: algebra_simps)
  finally show ?thesis .
qed

text \<open>Reading, honestly.  @{thm arith_cost_at_width_np2} instantiates the free width
      parameter with W := n+2; it proves nothing about a network, because `width` is a free
      symbol a caller supplies.  These theorems are correct arithmetic about sequences of
      naturals and nothing more; they do not mention a network, a comparator, or a
      cofactor.  The network-grounded headline -- width DEFINED from the network,
      resting on the named `sorry` intermediate_wire_width -- is
      \texttt{Cost\_Honest.verification\_cost\_bound}.  This theory is kept for the arithmetic
      lemma @{thm run_cost_bound} alone; its `sorter_*` theorems are schematic and should
      not be read as network results.\<close>

end
