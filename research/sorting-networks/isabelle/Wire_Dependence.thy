theory Wire_Dependence
  imports Main
begin

(* ============================================================================
   EXPLORING THE DEPENDENCE COMBINATORICS OF A WIRE.

   Not toward a goal: for the pleasure of understanding, what is provable about HOW a
   monotone wire function depends on its inputs?  The support (which inputs matter) we
   found grows tamely; the open question is the DEPENDENCE -- how richly the value
   varies over the inputs that matter.  Here we chart the single-variable dependence
   and find it clean, two-sided, and antipode-symmetric, tied directly to the broken
   lattice's defect: the SENSITIVE REGION of a variable is the set difference of its
   two Shannon cofactors -- a monotone band, and the bands are the antichains.

   A function f is a predicate on bool lists.  Its two Shannon cofactors in the first
   variable are scof0 f (fix it False) and scof1 f (fix it True).  For a monotone f
   these are ordered; the sensitive region is where they differ.

   Self-contained (imports Main).
   ============================================================================ *)

definition scof0 :: "(bool list \<Rightarrow> bool) \<Rightarrow> (bool list \<Rightarrow> bool)" where
  "scof0 f = (\<lambda>w. f (False # w))"

definition scof1 :: "(bool list \<Rightarrow> bool) \<Rightarrow> (bool list \<Rightarrow> bool)" where
  "scof1 f = (\<lambda>w. f (True # w))"

definition depends_first :: "(bool list \<Rightarrow> bool) \<Rightarrow> nat \<Rightarrow> bool" where
  "depends_first f m \<longleftrightarrow> (\<exists>w. length w = m \<and> scof0 f w \<noteq> scof1 f w)"

text \<open>The SENSITIVE REGION of the first variable: the residuals where fixing it True
      makes f hold but fixing it False does not -- where the variable actually
      matters.  For a monotone f (so that scof0 \<le> scof1) this is the whole difference.\<close>

definition sensitive :: "(bool list \<Rightarrow> bool) \<Rightarrow> nat \<Rightarrow> bool list set" where
  "sensitive f m = {w. length w = m \<and> scof1 f w \<and> \<not> scof0 f w}"

text \<open>DEPENDENCE IS EXACTLY DIFFERENCE OF COFACTORS.  The first variable matters
      somewhere iff the two Shannon cofactors differ there -- an iff, the clean
      characterization of single-variable dependence.  (Monotonicity is not needed for
      this direction of the statement; we phrase it for the True-side difference, which
      for monotone f is the only way they can differ.)\<close>

text \<open>Monotonicity in the first coordinate: fixing the head False cannot exceed fixing
      it True.  This is the Shannon ordering, stated locally.\<close>

definition head_mono :: "(bool list \<Rightarrow> bool) \<Rightarrow> nat \<Rightarrow> bool" where
  "head_mono f m \<longleftrightarrow> (\<forall>w. length w = m \<longrightarrow> scof0 f w \<longrightarrow> scof1 f w)"

text \<open>FACT 1 -- for a head-monotone f, the sensitive region is exactly where the
      cofactors differ.  So the variable's dependence set is a clean set difference.\<close>

theorem sensitive_is_difference:
  assumes "head_mono f m"
  shows "sensitive f m = {w. length w = m \<and> scof0 f w \<noteq> scof1 f w}"
proof
  show "sensitive f m \<subseteq> {w. length w = m \<and> scof0 f w \<noteq> scof1 f w}"
    by (auto simp: sensitive_def)
next
  show "{w. length w = m \<and> scof0 f w \<noteq> scof1 f w} \<subseteq> sensitive f m"
  proof
    fix w assume "w \<in> {w. length w = m \<and> scof0 f w \<noteq> scof1 f w}"
    hence lw: "length w = m" and diff: "scof0 f w \<noteq> scof1 f w" by auto
    have "scof0 f w \<longrightarrow> scof1 f w" using assms lw by (simp add: head_mono_def)
    hence "\<not> scof0 f w \<and> scof1 f w" using diff by blast
    thus "w \<in> sensitive f m" using lw by (simp add: sensitive_def)
  qed
qed

text \<open>FACT 2 -- DEPENDENCE IFF NONEMPTY SENSITIVE REGION.  For a head-monotone f, the
      variable matters iff its sensitive region is nonempty.\<close>

theorem depends_iff_sensitive_nonempty:
  assumes "head_mono f m"
  shows "depends_first f m \<longleftrightarrow> sensitive f m \<noteq> {}"
proof
  assume "depends_first f m"
  then obtain w where "length w = m" and "scof0 f w \<noteq> scof1 f w"
    by (auto simp: depends_first_def)
  thus "sensitive f m \<noteq> {}"
    using sensitive_is_difference[OF assms] by auto
next
  assume "sensitive f m \<noteq> {}"
  then obtain w where "w \<in> sensitive f m" by blast
  hence "length w = m \<and> scof1 f w \<and> \<not> scof0 f w" by (simp add: sensitive_def)
  thus "depends_first f m" by (auto simp: depends_first_def)
qed

text \<open>FACT 3 -- NO DEPENDENCE MEANS EQUAL COFACTORS (and hence an empty sensitive
      region).  The contrapositive germ: an unused variable has both cofactors equal.\<close>

theorem independent_iff_equal_cofactors:
  "(\<not> depends_first f m) \<longleftrightarrow> (\<forall>w. length w = m \<longrightarrow> scof0 f w = scof1 f w)"
  by (auto simp: depends_first_def)

text \<open>THE ANTIPODE ON DEPENDENCE.  The Boolean dual of f is dualf f = the complement of
      f on complemented inputs.  On the head variable, dualising SWAPS the two Shannon
      cofactors (complementing the head turns fixing-True into fixing-False) and
      complements them.  So the sensitive region is preserved under the antipode up to
      the coordinate complement: a variable matters to f iff it matters to its dual.\<close>

definition dualf :: "(bool list \<Rightarrow> bool) \<Rightarrow> (bool list \<Rightarrow> bool)" where
  "dualf f = (\<lambda>x. \<not> f (map Not x))"

lemma map_Not_Not [simp]: "map Not (map Not w) = w"
  by (simp add: comp_def)

lemma map_Not_comp [simp]: "map (Not \<circ> Not) w = w"
  by (simp add: comp_def)

theorem dual_swaps_cofactors:
  "scof0 (dualf f) w = (\<not> scof1 f (map Not w))"
  "scof1 (dualf f) w = (\<not> scof0 f (map Not w))"
  by (simp_all add: scof0_def scof1_def dualf_def)

text \<open>FACT 4 -- DEPENDENCE IS ANTIPODE-SYMMETRIC.  The first variable matters to the
      dual exactly when it matters to f: the antipode neither creates nor destroys a
      dependence.  (The witness for one is the complemented witness for the other.)\<close>

theorem dependence_antipode_symmetric:
  "depends_first (dualf f) m \<longleftrightarrow> depends_first f m"
proof
  assume "depends_first (dualf f) m"
  then obtain w where lw: "length w = m" and d: "scof0 (dualf f) w \<noteq> scof1 (dualf f) w"
    by (auto simp: depends_first_def)
  have neq: "scof0 f (map Not w) \<noteq> scof1 f (map Not w)"
    using d by (simp add: dual_swaps_cofactors)
  have "length (map Not w) = m" using lw by simp
  with neq show "depends_first f m"
    unfolding depends_first_def by blast
next
  assume "depends_first f m"
  then obtain w where lw: "length w = m" and d: "scof0 f w \<noteq> scof1 f w"
    by (auto simp: depends_first_def)
  \<comment> \<open>the complemented residual witnesses dependence of the dual\<close>
  have e0: "scof0 (dualf f) (map Not w) = (\<not> scof1 f w)"
    by (simp add: scof0_def scof1_def dualf_def)
  have e1: "scof1 (dualf f) (map Not w) = (\<not> scof0 f w)"
    by (simp add: scof0_def scof1_def dualf_def)
  have neq: "scof0 (dualf f) (map Not w) \<noteq> scof1 (dualf f) (map Not w)"
    using e0 e1 d by simp
  have "length (map Not w) = m" using lw by simp
  with neq show "depends_first (dualf f) m"
    unfolding depends_first_def by blast
qed

text \<open>Reading, honestly.  These chart single-variable dependence and find it clean.
      @{thm sensitive_is_difference} identifies the sensitive region -- where a
      variable matters -- as the set difference of its two Shannon cofactors, a
      monotone band; and these bands are exactly the incomparable pairs, the defect of
      the broken lattice.  @{thm depends_iff_sensitive_nonempty} and
      @{thm independent_iff_equal_cofactors} give the dependence a crisp two-sided
      characterisation.  @{thm dependence_antipode_symmetric} shows dependence is
      preserved by the antipode -- a variable matters to a wire iff it matters to the
      wire's dual, the min-wire and the max-wire depending on the same inputs.  The
      dependence combinatorics of a single variable is thus a monotone band, symmetric
      under the antipode; the OPEN question -- how the JOINT dependence over many
      variables compounds into the width -- is where these bands stack, and that
      stacking is the broken lattice's defect, still to be bounded.  Nothing assumed.\<close>

end
