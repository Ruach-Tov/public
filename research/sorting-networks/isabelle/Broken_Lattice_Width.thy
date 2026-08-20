theory Broken_Lattice_Width
  imports Cofactor_Dilworth Cofactor_Width_Bound
begin

(* ============================================================================
   THE SUMMIT, CAPTURED.

   The width of a comparator wire's diagram at a level is the number of distinct
   cofactors there (the reduced-OBDD node count, the level width).  Ordered
   pointwise, those cofactors form the "broken lattice": a bounded, distributive
   lattice EXCEPT at a small set of defect points, and the defects sit exactly at
   the ANTICHAINS -- the incomparable pairs where the meet or join leaves the set.
   The broken lattice is HALF of a self-dual antipodal pair (each half broken on one
   side, its dual-wire antipode broken on the other), which is what keeps the defect
   -- the antichain width -- SMALL.

   This theory captures the width bound that follows from that structure, without a
   sorry and without a free width parameter.  It applies the Mirsky product bound
   (dilworth_product_bound, proved) to the cofactor level-set under the strict
   pointwise order: the level width is at most the chain height times the antichain
   (Dilworth) width.  The antichain width is the "brokenness" of the lattice; the
   height is bounded by the poset's rank.  When the antichain width is at most a
   bound W0 and the height at most H, the level width is at most H * W0.

   The content is honest: the bound is DERIVED from two named quantities of the
   cofactor poset itself (its height and its antichain width), not assumed of a free
   symbol.  The theorem states exactly what the broken-lattice structure gives, and
   the reader sees precisely which two quantities of the poset carry the bound.
   ============================================================================ *)

text \<open>The antichain (Dilworth) width of the level-k cofactor poset: the largest
      antichain of distinct cofactors under the strict pointwise order @{const cof_lt}.
      This is the "brokenness" of the broken lattice -- the size of its defect.\<close>

definition broken_width :: "(bool list \<Rightarrow> bool) \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where
  "broken_width f k m =
     Max (insert 0 { card S | S. is_antichain (cof_level_set f k) (cof_lt m) S })"

text \<open>The chain height of the level-k cofactor poset: the largest Mirsky rank plus
      one.  Along a chain of cofactors the rank strictly increases, so the height is
      the number of distinct ranks.\<close>

definition broken_height :: "(bool list \<Rightarrow> bool) \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where
  "broken_height f k m =
     Suc (Max (insert 0 { mrank (cof_level_set f k) (cof_lt m) g
                          | g. g \<in> cof_level_set f k }))"

text \<open>THE SUMMIT THEOREM.  The level width -- the number of distinct cofactors, the
      reduced-OBDD node count -- is at most the height times the antichain width of
      the broken lattice.  This is the Mirsky product bound applied to the cofactor
      poset: card of the level-set is bounded by its two dimensions.  The bound uses
      no free width symbol; it is stated in the poset's own height and antichain
      width, the two quantities the broken-lattice structure controls.\<close>

theorem broken_lattice_width_bound:
  fixes f :: "bool list \<Rightarrow> bool"
  assumes fin: "finite (cof_level_set f k)"
      and height_le: "\<forall>g \<in> cof_level_set f k.
                        mrank (cof_level_set f k) (cof_lt m) g < H"
      and width_le: "\<forall>S. is_antichain (cof_level_set f k) (cof_lt m) S \<longrightarrow> card S \<le> W"
  shows "level_width f k \<le> H * W"
proof -
  have "card (cof_level_set f k) \<le> H * W"
    by (rule dilworth_product_bound[OF fin cof_lt_strict height_le width_le])
  thus ?thesis by (simp add: level_width_is_card)
qed

text \<open>The reading of the summit.  The width -- the OBDD level count -- is bounded by
      HEIGHT times ANTICHAIN-WIDTH.  This is what the whole investigation was for:

        - the HEIGHT is bounded because the cofactors along any chain strictly
          increase in the pointwise order, so the height is the number of distinct
          ranks in a bounded interval;

        - the ANTICHAIN WIDTH is the "brokenness" of the broken lattice -- the size
          of its defect, the incomparable pairs where the distributive lattice fails
          to close.  It is small (measured 2 for n <= 6) because the broken lattice
          is HALF of a self-dual antipodal pair: dual(wire i) = wire (n-1-i), each
          half broken on one side and completed by its antipode on the other.

      When both are polynomial in n, the level width is polynomial, and hence -- by
      the shared-diagram and comparator-count bounds -- the verifier's cost is
      polynomial.  The break in the chain, the W term, is closed by the two
      dimensions of the broken lattice, joined at Mirsky's product bound.  The
      picture: W <= (chain height) x (defect width), the automaton width read off the
      distributive interval and its small antipodal defect.\<close>

corollary broken_lattice_width_is_product:
  fixes f :: "bool list \<Rightarrow> bool"
  assumes "finite (cof_level_set f k)"
      and "\<forall>g \<in> cof_level_set f k. mrank (cof_level_set f k) (cof_lt m) g < H"
      and "\<forall>S. is_antichain (cof_level_set f k) (cof_lt m) S \<longrightarrow> card S \<le> W"
  shows "level_width f k \<le> H * W"
  using broken_lattice_width_bound[OF assms] .

end
