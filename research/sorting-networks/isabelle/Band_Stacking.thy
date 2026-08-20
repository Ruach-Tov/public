theory Band_Stacking
  imports Main
begin

(* ============================================================================
   REACHING FOR THE BAND STACKING.

   The level-k width is the number of distinct cofactors obtained by fixing a
   length-k prefix.  Each single variable's dependence is a monotone "band" (proved in
   Wire_Dependence); the width is how those bands STACK as several variables are fixed.
   This theory reaches for that, and finds the clean frame: the map from a prefix to
   its cofactor is MONOTONE, so the width is the size of a MONOTONE IMAGE of the
   k-cube, and its antichain -- the defect Mirsky needs -- is bounded by the antichains
   the monotone map can carry from the cube.

   The honest ceiling reached from monotonicity alone is the cube's own antichain
   (Sperner) -- exponential; beating it needs the specific band structure.  But the
   monotone-image frame is exactly right, and the facts here are the bridge: the
   cofactor map is monotone, incomparable images come only from incomparable prefixes,
   and equal cofactors are an equivalence whose classes count the width.

   We work abstractly: a cofactor map is a monotone function phi from a prefix domain
   (ordered by pleq) into a value poset (ordered by vle).  Self-contained (Main).
   ============================================================================ *)

text \<open>Prefixes ordered pointwise, and an abstract value order.\<close>

definition pleq :: "bool list \<Rightarrow> bool list \<Rightarrow> bool" (infix "\<preceq>" 50) where
  "pleq p q \<longleftrightarrow> length p = length q \<and> (\<forall>i < length p. p!i \<longrightarrow> q!i)"

text \<open>A cofactor map phi is MONOTONE if it respects the prefix order into the value
      order (given as a relation vle).  This is the content of Shannon-ordering lifted
      to whole prefixes: fixing more inputs to True can only raise the cofactor.\<close>

definition cof_monotone_map :: "(bool list \<Rightarrow> 'v) \<Rightarrow> 'v rel \<Rightarrow> nat \<Rightarrow> bool" where
  "cof_monotone_map phi vle k \<longleftrightarrow>
     (\<forall>p q. length p = k \<and> length q = k \<and> p \<preceq> q \<longrightarrow> (phi p, phi q) \<in> vle)"

text \<open>FACT 1 -- INCOMPARABLE IMAGES COME ONLY FROM INCOMPARABLE PREFIXES.  If two
      cofactors phi p, phi q are incomparable in the value order, then the prefixes p,
      q are incomparable in the prefix order.  (Contrapositive of monotonicity: a
      comparable pair of prefixes maps to a comparable pair of values.)  So an
      antichain of cofactors pulls back to an antichain of prefixes.\<close>

theorem incomparable_image_needs_incomparable_prefix:
  assumes mono: "cof_monotone_map phi vle k"
      and lp: "length p = k" and lq: "length q = k"
      and inc: "(phi p, phi q) \<notin> vle \<and> (phi q, phi p) \<notin> vle"
  shows "\<not> (p \<preceq> q) \<and> \<not> (q \<preceq> p)"
proof -
  have m: "\<And>a b. \<lbrakk>length a = k; length b = k; a \<preceq> b\<rbrakk> \<Longrightarrow> (phi a, phi b) \<in> vle"
    using mono unfolding cof_monotone_map_def by blast
  have "p \<preceq> q \<Longrightarrow> (phi p, phi q) \<in> vle" using m[OF lp lq] .
  moreover have "q \<preceq> p \<Longrightarrow> (phi q, phi p) \<in> vle" using m[OF lq lp] .
  ultimately show ?thesis using inc by blast
qed

text \<open>The cofactor image at level k: the set of distinct cofactor values.  The width
      is its cardinality.\<close>

definition cof_image :: "(bool list \<Rightarrow> 'v) \<Rightarrow> nat \<Rightarrow> 'v set" where
  "cof_image phi k = phi ` {p. length p = k}"

text \<open>FACT 2 -- THE WIDTH IS A MONOTONE-IMAGE SIZE, BOUNDED BY THE PREFIX COUNT.  The
      cofactor image is the image of the (finite) set of length-k prefixes, so its size
      is at most the number of prefixes, 2^k.  This is the cube ceiling: honest, and
      honestly exponential -- the frame within which any sharper bound must live.\<close>

lemma finite_prefixes: "finite {p::bool list. length p = k}"
proof (induct k)
  case 0
  have "{p::bool list. length p = 0} = {[]}" by auto
  thus ?case by simp
next
  case (Suc k)
  have "{p::bool list. length p = Suc k}
          \<subseteq> (\<lambda>(b,p). b # p) ` (UNIV \<times> {p. length p = k})"
    by (auto simp: image_iff) (metis length_Suc_conv)
  moreover have "finite ((\<lambda>(b,p). b # p) ` (UNIV \<times> {p::bool list. length p = k}))"
    using Suc by simp
  ultimately show ?case by (rule finite_subset)
qed

theorem width_finite_and_bounded:
  "finite (cof_image phi k) \<and> card (cof_image phi k) \<le> card {p::bool list. length p = k}"
proof
  show "finite (cof_image phi k)"
    unfolding cof_image_def using finite_prefixes by (rule finite_imageI)
  show "card (cof_image phi k) \<le> card {p::bool list. length p = k}"
    unfolding cof_image_def by (rule card_image_le[OF finite_prefixes])
qed

text \<open>FACT 3 -- AN ANTICHAIN OF COFACTORS PULLS BACK TO AN ANTICHAIN OF PREFIXES.
      Given a set of prefixes whose images form a value-antichain (pairwise
      incomparable and distinct), the prefixes themselves are pairwise incomparable.
      So the cofactor antichain width is at most the prefix antichain width -- the
      antichain the monotone map carries up from the cube.  This is the exact place
      the defect is bounded: by the antichains of the k-cube (Sperner), and, for the
      specific bands, potentially less.\<close>

definition prefix_antichain :: "bool list set \<Rightarrow> bool" where
  "prefix_antichain Q \<longleftrightarrow> (\<forall>p \<in> Q. \<forall>q \<in> Q. p \<preceq> q \<longrightarrow> p = q)"

theorem cofactor_antichain_pulls_back:
  assumes mono: "cof_monotone_map phi vle k"
      and Qk: "\<forall>p \<in> Q. length p = k"
      and anti: "\<forall>p \<in> Q. \<forall>q \<in> Q. p \<noteq> q
                   \<longrightarrow> (phi p, phi q) \<notin> vle \<and> (phi q, phi p) \<notin> vle"
  shows "prefix_antichain Q"
  unfolding prefix_antichain_def
proof (intro ballI impI)
  fix p q assume p: "p \<in> Q" and q: "q \<in> Q" and le: "p \<preceq> q"
  show "p = q"
  proof (rule ccontr)
    assume ne: "p \<noteq> q"
    have notin: "(phi p, phi q) \<notin> vle" using anti p q ne by blast
    have "(phi p, phi q) \<in> vle"
      using mono unfolding cof_monotone_map_def
      using Qk p q le by blast
    thus False using notin by blast
  qed
qed

text \<open>Reading, honestly.  The band stacking, reached as far as it cleanly goes.  The
      width is the size of the image of the monotone cofactor map on the k-cube
      (@{thm width_finite_and_bounded}), and any antichain of cofactors -- the broken
      lattice's defect -- pulls back to an antichain of prefixes
      (@{thm cofactor_antichain_pulls_back}, via
      @{thm incomparable_image_needs_incomparable_prefix}).  So the defect width is at
      most the antichain width of the k-cube.  From monotonicity alone that ceiling is
      Sperner's --- exponential --- and this is the honest wall: to bound the defect
      polynomially one must use the SPECIFIC band structure of the cofactors of an
      intermediate wire -- which are NOT thresholds, so the threshold count-collapse
      does NOT apply and must be re-established for them from their own structure.  The
      collapse we proved for the final (threshold) wires is not inherited here.  The frame is now exact -- width = monotone image,
      defect = pulled-back antichain -- and the remaining task, bounding the image
      antichain for the specific bands, is the last pitch, clearly seen.  Nothing here
      is assumed beyond the monotonicity of the cofactor map, which is proved elsewhere.\<close>

end
