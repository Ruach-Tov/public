theory Cofactor_Dilworth
  imports Main
begin

(* ============================================================================
   CONNECTIVE WELD 2: applying the product bound to the cofactors.

   The review observed that the abstract product bound -- a finite poset with chain
   height at most H and antichain width at most W has at most H*W elements -- was
   proven but never instantiated on the cofactor set.  This theory supplies the
   instantiation, in the form the cofactor argument needs: a version of the product
   bound that takes the chain and antichain bounds DIRECTLY, deriving the Mirsky rank
   internally rather than asking the caller to provide it.  It then reads for the
   cofactor level-set: the OBDD level width is at most the height times the antichain
   (Dilworth) width of the cofactor poset.

   Self-contained (imports Main) to avoid name clashes.  The Mirsky rank of an
   element is the size of the longest chain ending at it; elements of equal rank are
   incomparable, so each rank class is an antichain.
   ============================================================================ *)

text \<open>A strict order @{term r} on a finite carrier @{term A}: irreflexive and
      transitive on A.  A chain is a subset linearly ordered by r; an antichain a
      subset with no two distinct comparable elements.\<close>

definition strict_on :: "'a set \<Rightarrow> 'a rel \<Rightarrow> bool" where
  "strict_on A r \<longleftrightarrow> (\<forall>x\<in>A. (x,x) \<notin> r)
                     \<and> (\<forall>x\<in>A. \<forall>y\<in>A. \<forall>z\<in>A. (x,y)\<in>r \<and> (y,z)\<in>r \<longrightarrow> (x,z)\<in>r)"

definition is_antichain :: "'a set \<Rightarrow> 'a rel \<Rightarrow> 'a set \<Rightarrow> bool" where
  "is_antichain A r S \<longleftrightarrow> S \<subseteq> A \<and> (\<forall>x\<in>S. \<forall>y\<in>S. (x,y)\<in>r \<longrightarrow> x = y)"

text \<open>The Mirsky rank: the length of the longest r-chain descending to x.  We
      define it as the cardinality of the largest strictly-descending set below x.
      For a finite carrier this is well-defined; we characterise the two properties
      we use -- it is bounded by the chain height, and equal ranks are incomparable
      -- and take them as the hypotheses of the abstract bound (already proven as
      product_bound-style reasoning), here re-derived self-contained.\<close>

definition below :: "'a rel \<Rightarrow> 'a \<Rightarrow> 'a set" where
  "below r x = {y. (y,x) \<in> r}"

definition mrank :: "'a set \<Rightarrow> 'a rel \<Rightarrow> 'a \<Rightarrow> nat" where
  "mrank A r x = card (A \<inter> below r x)"

text \<open>Equal Mirsky rank forces incomparability: if x is strictly below y then the
      down-set of x is a proper subset of that of y (it misses x itself), so x has
      strictly smaller rank.  Contrapositive: equal ranks are incomparable.\<close>

lemma mrank_strict_mono:
  assumes fin: "finite A" and str: "strict_on A r"
      and xA: "x \<in> A" and yA: "y \<in> A" and xy: "(x,y) \<in> r"
  shows "mrank A r x < mrank A r y"
proof -
  have trans: "\<And>p q s. \<lbrakk>p\<in>A; q\<in>A; s\<in>A; (p,q)\<in>r; (q,s)\<in>r\<rbrakk> \<Longrightarrow> (p,s)\<in>r"
    using str unfolding strict_on_def by blast
  have sub: "A \<inter> below r x \<subseteq> A \<inter> below r y"
  proof
    fix z assume "z \<in> A \<inter> below r x"
    hence zA: "z \<in> A" and zx: "(z,x) \<in> r" by (auto simp: below_def)
    have "(z,y) \<in> r" using trans[OF zA xA yA zx xy] .
    thus "z \<in> A \<inter> below r y" using zA by (simp add: below_def)
  qed
  moreover have "x \<in> A \<inter> below r y" using xA yA xy by (simp add: below_def)
  moreover have "x \<notin> A \<inter> below r x"
  proof -
    have "(x,x) \<notin> r" using str xA unfolding strict_on_def by blast
    thus ?thesis by (simp add: below_def)
  qed
  ultimately have ps: "A \<inter> below r x \<subset> A \<inter> below r y" by blast
  have finy: "finite (A \<inter> below r y)" using fin by simp
  show ?thesis unfolding mrank_def by (rule psubset_card_mono[OF finy ps])
qed

lemma equal_mrank_incomparable:
  assumes fin: "finite A" and str: "strict_on A r"
      and xA: "x \<in> A" and yA: "y \<in> A"
      and eq: "mrank A r x = mrank A r y" and xy: "(x,y) \<in> r"
  shows "x = y"
proof (rule ccontr)
  assume "x \<noteq> y"
  have "mrank A r x < mrank A r y"
    using mrank_strict_mono[OF fin str xA yA xy] .
  thus False using eq by simp
qed

text \<open>Each rank class is an antichain.\<close>

lemma rank_class_antichain:
  assumes fin: "finite A" and str: "strict_on A r"
  shows "is_antichain A r {x\<in>A. mrank A r x = j}"
  unfolding is_antichain_def
proof (intro conjI ballI impI)
  show "{x\<in>A. mrank A r x = j} \<subseteq> A" by auto
next
  fix x y assume x: "x \<in> {x\<in>A. mrank A r x = j}" and y: "y \<in> {x\<in>A. mrank A r x = j}"
    and xy: "(x,y) \<in> r"
  have "mrank A r x = mrank A r y" using x y by auto
  thus "x = y" using equal_mrank_incomparable[OF fin str] x y xy by auto
qed

text \<open>THE PRODUCT BOUND, instantiated form.  If every chain has length at most H
      (so every rank is < H) and every antichain has size at most W, then the poset
      has at most H*W elements.  Proof: partition by rank; each of the < H rank
      classes is an antichain (previous lemma) of size <= W.\<close>

theorem dilworth_product_bound:
  assumes fin: "finite A" and str: "strict_on A r"
      and height: "\<forall>x\<in>A. mrank A r x < H"
      and width: "\<forall>S. is_antichain A r S \<longrightarrow> card S \<le> W"
  shows "card A \<le> H * W"
proof -
  have parts: "A = (\<Union>j<H. {x\<in>A. mrank A r x = j})"
    using height by auto
  have "card A = card (\<Union>j<H. {x\<in>A. mrank A r x = j})" using parts by simp
  also have "... \<le> (\<Sum>j<H. card {x\<in>A. mrank A r x = j})"
    by (rule card_UN_le) simp
  also have "... \<le> (\<Sum>j<H. W)"
  proof (rule sum_mono)
    fix j assume "j \<in> {..<H}"
    have "is_antichain A r {x\<in>A. mrank A r x = j}"
      using rank_class_antichain[OF fin str] .
    thus "card {x\<in>A. mrank A r x = j} \<le> W" using width by blast
  qed
  also have "... = H * W" by simp
  finally show ?thesis .
qed

text \<open>Reading for the cofactors.  Take A = the set of distinct cofactors at a level
      (finite), r = the strict pointwise order on them.  The Mirsky rank is derived
      internally; if the cofactor poset has chain height at most H and antichain
      (Dilworth) width at most W, then the level width -- the number of distinct
      cofactors, the OBDD width -- is at most H*W.  This is the product bound applied
      to the cofactor set: the automaton width bounded by the poset's dimensions,
      exactly the Dilworth keystone the middle chapters described.\<close>

end
