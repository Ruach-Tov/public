theory Cofactor_Width_Bound
  imports Cofactor_Automaton Cofactor_Dilworth
begin

(* ============================================================================
   A SEAM MADE PLAIN: the automaton width IS bounded by the poset dimensions.

   Two proven theorems have sat adjacent without shaking hands.  Cofactor_Automaton
   defines the level width as the number of distinct cofactors -- the automaton's
   state count.  Cofactor_Dilworth proves that a finite poset with chain height at
   most H and antichain width at most W has at most H*W elements.  This theory makes
   the connection the book described in prose: the level width, ordered pointwise, is
   at most the height times the Dilworth width of the cofactor set.

   The two source theories share no constant names, so they may be imported together
   without the duplicate-constant slowdown.  The composition is a short application:
   take A to be the cofactor image at a level, r the strict pointwise order, and the
   product bound delivers level_width <= H*W.
   ============================================================================ *)

text \<open>The strict pointwise order on cofactors, as functions on bool lists of a
      given residual length.  We compare cofactors by their values on the residual
      inputs: g is strictly below h if g implies h everywhere and they differ.\<close>

definition cof_lt :: "nat \<Rightarrow> ((bool list \<Rightarrow> bool) \<times> (bool list \<Rightarrow> bool)) set" where
  "cof_lt m = {(g,h). (\<forall>w. length w = m \<longrightarrow> g w \<longrightarrow> h w)
                     \<and> (\<exists>w. length w = m \<and> g w \<noteq> h w)}"

text \<open>The set of distinct cofactors at level k, as an explicit finite set.\<close>

definition cof_level_set :: "(bool list \<Rightarrow> bool) \<Rightarrow> nat \<Rightarrow> (bool list \<Rightarrow> bool) set" where
  "cof_level_set f k = (\<lambda>p. cof f p) ` {p. length p = k}"

text \<open>The level width is the cardinality of that set (matching @{const level_width}).\<close>

lemma level_width_is_card:
  "level_width f k = card (cof_level_set f k)"
  by (simp add: level_width_def cof_level_set_def)

text \<open>The order @{const cof_lt} is strict (irreflexive and transitive) on any set of
      cofactors of a fixed residual length m.\<close>

lemma cof_lt_strict:
  "strict_on A (cof_lt m)"
  unfolding strict_on_def
proof (intro conjI ballI allI impI)
  fix x assume "x \<in> A"
  show "(x,x) \<notin> cof_lt m" by (auto simp: cof_lt_def)
next
  fix x y z assume "x\<in>A" "y\<in>A" "z\<in>A" and "(x,y)\<in>cof_lt m \<and> (y,z)\<in>cof_lt m"
  hence xy: "(x,y)\<in>cof_lt m" and yz: "(y,z)\<in>cof_lt m" by auto
  have imp: "\<And>w. length w = m \<Longrightarrow> x w \<longrightarrow> z w"
    using xy yz by (auto simp: cof_lt_def)
  have "\<exists>w. length w = m \<and> x w \<noteq> z w"
  proof -
    from xy obtain w where lw: "length w = m" and diff: "x w \<noteq> y w"
      by (auto simp: cof_lt_def)
    have "x w \<longrightarrow> y w" using xy lw by (auto simp: cof_lt_def)
    hence "\<not> x w" and "y w" using diff by auto
    moreover have "y w \<longrightarrow> z w" using yz lw by (auto simp: cof_lt_def)
    ultimately have "\<not> x w" and "z w" by auto
    hence "x w \<noteq> z w" by auto
    thus ?thesis using lw by blast
  qed
  thus "(x,z) \<in> cof_lt m" using imp by (auto simp: cof_lt_def)
qed

text \<open>THE SEAM.  If the cofactor set at level k is finite, every chain has length
      at most H (equivalently every Mirsky rank is below H), and every antichain has
      size at most W, then the level width is at most H*W.  This is the automaton
      width bounded by the poset dimensions --- the Dilworth keystone applied to the
      level width, as one theorem.\<close>

theorem level_width_le_height_times_width:
  fixes f :: "bool list \<Rightarrow> bool"
  assumes fin: "finite (cof_level_set f k)"
      and height: "\<forall>g \<in> cof_level_set f k. mrank (cof_level_set f k) (cof_lt m) g < H"
      and width: "\<forall>S. is_antichain (cof_level_set f k) (cof_lt m) S \<longrightarrow> card S \<le> W"
  shows "level_width f k \<le> H * W"
proof -
  have "card (cof_level_set f k) \<le> H * W"
    by (rule dilworth_product_bound[OF fin cof_lt_strict height width])
  thus ?thesis by (simp add: level_width_is_card)
qed

text \<open>Reading.  The middle chapters said the OBDD level width is bounded by the
      height times the Dilworth width of the cofactor poset.  Here that is one
      theorem: @{thm level_width_le_height_times_width} composes the automaton's
      width (the cofactor count, @{thm level_width_is_card}) with the poset's product
      bound (@{thm dilworth_product_bound}) over the strict pointwise order
      @{const cof_lt}.  The two structures --- the decision diagram and the broken
      lattice --- meet, and the seam is now a theorem, not a sentence.\<close>

end
