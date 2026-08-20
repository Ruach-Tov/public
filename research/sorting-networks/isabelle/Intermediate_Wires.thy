theory Intermediate_Wires
  imports Main
begin

(* ============================================================================
   EXPLORING THE INTERMEDIATE-WIRE VICINITY (non-goal-directed).

   A reviewer rightly noted that the width bounds of the count chapters are proved
   for THRESHOLD wire functions -- symmetric, depending only on how many inputs are
   true -- which is the form a sorter's FINAL wires take.  The INTERMEDIATE wire
   functions, after only some of the comparators, are still monotone (comparators
   preserve monotonicity) but are NOT in general thresholds.  This theory does not
   claim the width bound for them; it charts what IS true in the vicinity, exploring
   rather than arguing.

   The germ of the matter is SUPPORT: the set of input variables a function actually
   depends on.  A sorter's intermediate wire depends only on the inputs that have
   reached it through the comparator graph; early on, few have, so the support is
   small.  A variable outside the support contributes no branching to the diagram --
   its two Shannon cofactors coincide.  So the diagram's branching is governed by the
   support, and the threshold form is the special case of full, symmetric support.

   Self-contained (imports Main).  These are honest facts about arbitrary Boolean
   functions and their supports, charting the region the reviewer opened.
   ============================================================================ *)

text \<open>A function depends on its first variable if some residual input is classified
      differently by fixing that variable to False versus True.\<close>

definition depends_first :: "(bool list \<Rightarrow> bool) \<Rightarrow> nat \<Rightarrow> bool" where
  "depends_first f m \<longleftrightarrow> (\<exists>w. length w = m \<and> f (False # w) \<noteq> f (True # w))"

text \<open>The two Shannon cofactors (restrict the first variable).\<close>

definition scof0 :: "(bool list \<Rightarrow> bool) \<Rightarrow> (bool list \<Rightarrow> bool)" where
  "scof0 f = (\<lambda>w. f (False # w))"

definition scof1 :: "(bool list \<Rightarrow> bool) \<Rightarrow> (bool list \<Rightarrow> bool)" where
  "scof1 f = (\<lambda>w. f (True # w))"

text \<open>THE SUPPORT GERM.  If a function does NOT depend on its first variable (on
      residual inputs of length m), its two Shannon cofactors agree on those inputs.
      So an unused variable contributes no distinct cofactor -- no branching.\<close>

theorem no_dependence_equal_cofactors:
  assumes "\<not> depends_first f m"
  shows "\<forall>w. length w = m \<longrightarrow> scof0 f w = scof1 f w"
  using assms by (auto simp: depends_first_def scof0_def scof1_def)

text \<open>Contrapositive, stated for use: distinct Shannon cofactors witness a genuine
      dependence.  So the level-one branching (two distinct cofactors rather than one)
      occurs exactly when the variable is in the support.\<close>

theorem distinct_cofactors_imply_dependence:
  assumes "\<exists>w. length w = m \<and> scof0 f w \<noteq> scof1 f w"
  shows "depends_first f m"
  using assms by (auto simp: depends_first_def scof0_def scof1_def)

text \<open>THE THRESHOLD IS THE SYMMETRIC SPECIAL CASE.  A function is SYMMETRIC if it is
      invariant under permuting its inputs -- equivalently, on bool lists, it depends
      only on the count of trues.  The threshold functions are symmetric; the
      intermediate wire functions in general are not.  We record the defining property
      of symmetry that the threshold analysis used, to mark precisely where that
      analysis applies and where it does not.\<close>

definition count_true :: "bool list \<Rightarrow> nat" where
  "count_true x = length (filter id x)"

definition symmetric_fn :: "(bool list \<Rightarrow> bool) \<Rightarrow> bool" where
  "symmetric_fn f \<longleftrightarrow> (\<forall>x y. count_true x = count_true y \<and> length x = length y \<longrightarrow> f x = f y)"

text \<open>A threshold is symmetric: it depends only on the count.  (The witness that the
      width analysis of the count chapters applies exactly to the symmetric functions,
      and the intermediate wires need their own account when they are not symmetric.)\<close>

theorem threshold_is_symmetric:
  "symmetric_fn (\<lambda>x. t \<le> count_true x)"
  by (simp add: symmetric_fn_def)

text \<open>A symmetric function's Shannon cofactors are related by a count shift: fixing a
      variable to True is like lowering the threshold in the symmetric case.  For a
      general (non-symmetric) function this need not hold -- which is why the
      intermediate wires, lacking symmetry, are not captured by the threshold count.\<close>

theorem symmetric_cofactor_shift:
  assumes "symmetric_fn f"
  shows "\<forall>w w'. count_true w = count_true w' \<and> length w = length w'
                 \<longrightarrow> scof1 f w = scof1 f w'"
proof (intro allI impI)
  fix w w' assume "count_true w = count_true w' \<and> length w = length w'"
  hence c: "count_true (True # w) = count_true (True # w')"
     and l: "length (True # w) = length (True # w')"
    by (simp_all add: count_true_def)
  show "scof1 f w = scof1 f w'"
    using assms c l by (simp add: scof1_def symmetric_fn_def)
qed

text \<open>Reading, honestly.  @{thm no_dependence_equal_cofactors} is the support germ: a
      variable outside a function's support gives no branching, so the diagram width
      is governed by the support, not the arity.  @{thm threshold_is_symmetric} and
      @{thm symmetric_cofactor_shift} mark where the count-based width analysis
      applies -- to the SYMMETRIC functions, of which the thresholds (a sorter's final
      wires) are examples.  The intermediate wires are monotone but not in general
      symmetric; the width bound of the count chapters is established for the final,
      symmetric wires, and the intermediate case, whose width the measurements show to
      grow with the support, is charted here but not closed.  This is the honest edge
      of the thesis: the bound is proven where the wires are thresholds, and the
      region beyond is mapped, not claimed.\<close>

end
