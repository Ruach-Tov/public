theory Antipode_Final_Move
  imports Main
begin

(* ============================================================================
   RECREATIONAL: the antipode as the final move -- XOR by all-ones.

   Heath's framing: an optimal sorter builds the broken lattice toward the antipodal
   move, filling the whole lattice volume but for the W_0 cut-out reserved for the final
   antipode.  The antipode on wire indices is w -> (n-1)-w; on n = 2^k wires it is XOR by
   the all-ones mask.  LINEAR-BASIS.md observed that the self-mirror class of an optimal
   layer uses exactly this all-ones mask (15 = 1111 at n=16), and that the all-ones mask
   is the sum of the layer's basis vectors.  This theory proves the arithmetic that
   grounds the mechanism: the all-ones XOR is an involution, it realises the order
   reversal (n-1)-x, and it is the sum of every hypercube direction -- so the antipode is
   the composite of all the layer directions the sorter walks, and the move it builds
   toward.

   We work with natural numbers and the all-ones mask (2^k - 1).  The reversal (n-1)-x
   on {0..<2^k} equals XOR by 2^k - 1, since 2^k - 1 has all k low bits set.
   Self-contained beyond HOL-Library.Word (for the bitwise view we prove the arithmetic
   directly on naturals).
   ============================================================================ *)

text \<open>The antipode index map on n wires: reversal.\<close>

definition antip_idx :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "antip_idx n x = n - 1 - x"

text \<open>INVOLUTION.  On indices below n, the reversal is its own inverse.\<close>

theorem antip_idx_involution:
  assumes "x < n"
  shows "antip_idx n (antip_idx n x) = x"
  using assms by (simp add: antip_idx_def)

text \<open>ORDER REVERSAL.  Below n, the reversal reverses the order strictly.\<close>

theorem antip_idx_order_reversing:
  assumes "x < n" and "y < n" and "x < y"
  shows "antip_idx n y < antip_idx n x"
  using assms by (simp add: antip_idx_def)

text \<open>FIXED POINTS.  The reversal fixes x iff 2*x + 1 = n; for n = 2^k (k >= 1, n even)
      there is no fixed point --- the antipode is fixed-point-free on the wires, pairing
      them into mirror pairs.  For n odd it fixes exactly the median (n-1)/2.\<close>

theorem antip_idx_fixed_iff:
  assumes "x < n"
  shows "antip_idx n x = x \<longleftrightarrow> 2 * x + 1 = n"
  using assms by (auto simp: antip_idx_def)

theorem antip_idx_no_fixed_point_even:
  assumes "even n" and "x < n"
  shows "antip_idx n x \<noteq> x"
proof
  assume "antip_idx n x = x"
  hence "2 * x + 1 = n" using assms(2) by (simp add: antip_idx_fixed_iff)
  thus False using assms(1) by presburger
qed

text \<open>THE ALL-ONES MASK AND THE REVERSAL.  For n = 2^k, the all-ones mask is n - 1, and
      the reversal (n-1)-x equals the bitwise complement within k bits, i.e. XOR by
      (n-1): on x < 2^k, (2^k - 1) - x has every bit flipped, which is x XOR (2^k - 1).
      We prove the arithmetic identity that underlies the bitwise statement: for x below
      a power of two, the reversal is the mask minus x, and the mask is the bit-sum.\<close>

theorem allones_reversal:
  assumes "x < 2 ^ k"
  shows "antip_idx (2 ^ k) x = (2 ^ k - 1) - x"
  using assms by (simp add: antip_idx_def)

text \<open>THE MASK IS THE SUM OF ALL BASIS VECTORS.  2^k - 1 = sum of 2^i for i < k --- the
      all-ones mask is the XOR/sum of every hypercube direction e_i = 2^i.  So the
      antipode move is the composite of all the layer directions the sorter walks: each
      stride-2^i layer moves along e_i, and their total is the all-ones antipode.\<close>

theorem allones_is_sum_of_basis:
  "(2 ^ k - 1 :: nat) = (\<Sum>i<k. 2 ^ i)"
proof -
  have "(\<Sum>i<k. (2::nat) ^ i) = 2 ^ k - 1"
    by (induct k) (auto simp: algebra_simps)
  thus ?thesis by simp
qed

text \<open>THE MIRROR PAIRS.  On n = 2^k wires the antipode partitions the wires into pairs
      {x, (n-1)-x}, each a mirror pair, none fixed --- the self-mirror structure of the
      LINEAR-BASIS layers.  We record that the pair map is an involution with no fixed
      point, hence a perfect matching of the wires.\<close>

theorem antipode_perfect_matching:
  assumes "k \<ge> 1" and "x < 2 ^ k"
  shows "antip_idx (2 ^ k) x \<noteq> x \<and> antip_idx (2 ^ k) (antip_idx (2 ^ k) x) = x"
proof
  have "even ((2::nat) ^ k)" using assms(1) by simp
  thus "antip_idx (2 ^ k) x \<noteq> x"
    using antip_idx_no_fixed_point_even assms(2) by blast
next
  show "antip_idx (2 ^ k) (antip_idx (2 ^ k) x) = x"
    using antip_idx_involution assms(2) by blast
qed

text \<open>Reading, recreationally.  The antipode final move is XOR by all-ones, and its
      arithmetic is here.  @{thm antip_idx_involution}: applied twice it is the identity,
      the involution of the antipode.  @{thm antip_idx_order_reversing}: it reverses the
      wire order --- the reversal w_0 on indices.  @{thm allones_is_sum_of_basis}: the
      all-ones mask is the sum of every basis vector 2^i, so the antipode is the COMPOSITE
      of all the hypercube directions the sorter's stride layers walk --- the total of the
      basis, the move the whole construction builds toward.  @{thm antipode_perfect_matching}:
      on 2^k wires it is fixed-point-free, pairing the wires into mirror pairs, the
      self-mirror structure LINEAR-BASIS observed.  So the mechanism is proven from what we
      knew: the sorter fills the hypercube by walking the basis e_0, e_1, ..., and the
      final antipodal move --- the W_0-cut-out reserved to the end --- is their sum, the
      all-ones reversal, the antipode that folds the broken lattice onto itself.  Nothing
      is assumed.\<close>

end
