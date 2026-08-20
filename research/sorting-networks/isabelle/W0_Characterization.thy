theory W0_Characterization
  imports Main
begin

(* ============================================================================
   PLAYING AROUND W_0 -- characterizing the defect of the broken lattice.

   W_0 is the one quantity the whole width bound now funnels to: the antichain
   (Dilworth) width of the cofactor poset -- equivalently the antichain width of its
   meet/join closure, equivalently how far the cofactors are from being a lattice.
   This theory characterises it, for the pleasure of understanding, from three angles:

     - W_0 = 1 exactly when the poset is a CHAIN -- the threshold (final-wire) case, the
       unbroken lattice needing no repair;
     - the ANTIPODE fixes W_0 -- an order-reversing involution maps antichains to
       antichains of equal size, so a wire and its antipode have equal brokenness;
     - an antichain is a set of pairwise-INCOMPARABLE elements -- the "crossings" -- so
       W_0 counts the widest family of mutually crossing cofactors.

   We work abstractly with a strict order r on a set A (the cofactor poset).  An
   antichain is a subset with no two distinct comparable elements; a chain is a subset
   any two of which are comparable.  W_0 is the size of the largest antichain.
   Self-contained (imports Main).
   ============================================================================ *)

definition is_antichain :: "'a set \<Rightarrow> 'a rel \<Rightarrow> 'a set \<Rightarrow> bool" where
  "is_antichain A r S \<longleftrightarrow> S \<subseteq> A \<and> (\<forall>x\<in>S. \<forall>y\<in>S. (x,y)\<in>r \<longrightarrow> x = y)"

definition is_chain :: "'a set \<Rightarrow> 'a rel \<Rightarrow> 'a set \<Rightarrow> bool" where
  "is_chain A r S \<longleftrightarrow> S \<subseteq> A \<and> (\<forall>x\<in>S. \<forall>y\<in>S. x = y \<or> (x,y)\<in>r \<or> (y,x)\<in>r)"

text \<open>A poset is a CHAIN if the whole carrier is a chain: any two elements are
      comparable.  For such a poset, every antichain has at most one element -- the
      unbroken, threshold case (W_0 = 1).\<close>

definition poset_is_chain :: "'a set \<Rightarrow> 'a rel \<Rightarrow> bool" where
  "poset_is_chain A r \<longleftrightarrow> (\<forall>x\<in>A. \<forall>y\<in>A. x = y \<or> (x,y)\<in>r \<or> (y,x)\<in>r)"

text \<open>CHARACTERISATION 1 -- W_0 = 1 IFF CHAIN.  We prove the two implications in the
      clean directions: in a chain every antichain is a singleton (or empty); and if
      every antichain is a singleton, the poset is a chain.\<close>

theorem chain_antichains_are_small:
  assumes "poset_is_chain A r"
      and "is_antichain A r S"
      and "x \<in> S" and "y \<in> S"
  shows "x = y"
proof -
  have "S \<subseteq> A" using assms(2) by (simp add: is_antichain_def)
  hence xA: "x \<in> A" and yA: "y \<in> A" using assms(3,4) by auto
  have "x = y \<or> (x,y)\<in>r \<or> (y,x)\<in>r" using assms(1) xA yA by (simp add: poset_is_chain_def)
  moreover have "(x,y)\<in>r \<longrightarrow> x = y" using assms(2,3,4) by (auto simp: is_antichain_def)
  moreover have "(y,x)\<in>r \<longrightarrow> y = x" using assms(2,3,4) by (auto simp: is_antichain_def)
  ultimately show ?thesis by auto
qed

text \<open>Conversely, if every two-element subset that is an antichain forces equality --
      i.e. there is no antichain of size two -- then the poset is a chain.\<close>

theorem no_two_antichain_implies_chain:
  assumes "\<forall>x\<in>A. \<forall>y\<in>A. is_antichain A r {x,y} \<longrightarrow> x = y"
  shows "poset_is_chain A r"
  unfolding poset_is_chain_def
proof (intro ballI)
  fix x y assume xA: "x \<in> A" and yA: "y \<in> A"
  show "x = y \<or> (x,y)\<in>r \<or> (y,x)\<in>r"
  proof (rule ccontr)
    assume "\<not> (x = y \<or> (x,y)\<in>r \<or> (y,x)\<in>r)"
    hence ne: "x \<noteq> y" and nxy: "(x,y)\<notin>r" and nyx: "(y,x)\<notin>r" by auto
    have "is_antichain A r {x,y}"
      using xA yA nxy nyx by (auto simp: is_antichain_def)
    hence "x = y" using assms xA yA by blast
    thus False using ne by simp
  qed
qed

text \<open>CHARACTERISATION 2 -- THE ANTIPODE FIXES W_0.  Let d be an order-reversing
      involution on A (the Boolean dual): d maps A to A, is its own inverse, and
      reverses the order.  Then d carries an antichain to an antichain of the same
      size (a bijection on the antichain), so the antichain widths of A and of its
      antipodal image agree: a wire and its antipode have equal defect.\<close>

definition order_reversing_involution :: "'a set \<Rightarrow> 'a rel \<Rightarrow> ('a \<Rightarrow> 'a) \<Rightarrow> bool" where
  "order_reversing_involution A r d \<longleftrightarrow>
     (\<forall>x\<in>A. d x \<in> A) \<and> (\<forall>x\<in>A. d (d x) = x)
     \<and> (\<forall>x\<in>A. \<forall>y\<in>A. (x,y)\<in>r \<longrightarrow> (d y, d x)\<in>r)"

theorem antipode_maps_antichain:
  assumes ori: "order_reversing_involution A r d"
      and anti: "is_antichain A r S"
  shows "is_antichain A r (d ` S)"
  unfolding is_antichain_def
proof (intro conjI ballI impI)
  have SA: "S \<subseteq> A" using anti by (simp add: is_antichain_def)
  show "d ` S \<subseteq> A" using ori SA by (auto simp: order_reversing_involution_def)
next
  fix u v assume u: "u \<in> d ` S" and v: "v \<in> d ` S" and uv: "(u,v) \<in> r"
  have SA: "S \<subseteq> A" using anti by (simp add: is_antichain_def)
  from u obtain x where x: "x \<in> S" and ux: "u = d x" by auto
  from v obtain y where y: "y \<in> S" and vy: "v = d y" by auto
  have xA: "x \<in> A" and yA: "y \<in> A" using x y SA by auto
  \<comment> \<open>(d x, d y) in r, and order-reversal gives (d(d y), d(d x)) = (y, x) in r\<close>
  have dxA: "d x \<in> A" and dyA: "d y \<in> A"
    using ori xA yA by (auto simp: order_reversing_involution_def)
  have "(d x, d y) \<in> r" using ux vy uv by simp
  hence "(d (d y), d (d x)) \<in> r"
    using ori dxA dyA by (auto simp: order_reversing_involution_def)
  moreover have "d (d y) = y" and "d (d x) = x"
    using ori xA yA by (auto simp: order_reversing_involution_def)
  ultimately have "(y, x) \<in> r" by simp
  hence "y = x" using anti x y by (auto simp: is_antichain_def)
  thus "u = v" using ux vy by simp
qed

text \<open>Injectivity of the antipode on A: since it is an involution, it is a bijection,
      so the image of an antichain has the SAME cardinality.  Hence W_0 is preserved.\<close>

theorem antipode_injective_on_set:
  assumes "order_reversing_involution A r d" and "S \<subseteq> A"
  shows "inj_on d S"
proof (rule inj_onI)
  fix x y assume "x \<in> S" and "y \<in> S" and "d x = d y"
  hence xA: "x \<in> A" and yA: "y \<in> A" using assms(2) by auto
  have "d (d x) = d (d y)" using \<open>d x = d y\<close> by simp
  moreover have "d (d x) = x" and "d (d y) = y"
    using assms(1) xA yA by (auto simp: order_reversing_involution_def)
  ultimately show "x = y" by simp
qed

theorem antipode_preserves_antichain_card:
  assumes "order_reversing_involution A r d"
      and "is_antichain A r S" and "finite S"
  shows "card (d ` S) = card S"
proof -
  have "S \<subseteq> A" using assms(2) by (simp add: is_antichain_def)
  hence "inj_on d S" using antipode_injective_on_set[OF assms(1)] by simp
  thus ?thesis by (rule card_image)
qed

text \<open>Reading.  W_0 -- the defect of the broken lattice, the antichain width of the
      cofactor poset -- is characterised here from two of its three faces.
      @{thm chain_antichains_are_small} and @{thm no_two_antichain_implies_chain} give
      W_0 = 1 exactly for a CHAIN: the threshold, final-wire case, the lattice needing
      no repair.  @{thm antipode_maps_antichain} and
      @{thm antipode_preserves_antichain_card} show the ANTIPODE fixes W_0 -- an
      order-reversing involution carries an antichain to an antichain of equal size, so
      a wire and its antipode have equal brokenness; the defect is antipode-symmetric,
      as the median and the whole broken lattice are.  The third face -- W_0 as the
      widest family of mutually crossing monotone bands -- is the concrete combinatorial
      target, where a bound on W_0 (constant, or logarithmic) would fire the pathwidth
      bridge.  Nothing here is assumed; these are properties of any antichain under an
      order-reversing involution.\<close>

end
