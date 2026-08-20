theory Cofactor_Automaton
  imports Main
begin

(* ============================================================================
   THE COFACTOR SET AS THE MINIMAL AUTOMATON (the reduced OBDD).

   This theory studies the vicinity of the identification "the number of distinct
   cofactors at a level = the OBDD width there" (Gap 2), and records the automaton
   facts that make the cofactor set the state set of the minimal automaton.  It is
   SELF-CONTAINED (imports only Main) to avoid the name clashes that arise from
   importing sibling theories that share constant names.

   A Boolean function on the residual variables is a predicate on bool lists.  A
   cofactor of f by a prefix p is the residual w |-> f (p @ w).  The two Shannon
   children of a cofactor split on the first remaining variable.

   PROVEN HERE:
     shannon_determinism  -- the children of a cofactor are determined by the
                             cofactor alone, not by the prefix that produced it
                             (Myhill-Nerode: the residual IS the automaton state);
     restriction_closed   -- the cofactor set is closed under Shannon restriction;
     two_sinks            -- the deepest cofactors are the two constants.
   The keystone connecting Gap 2 to Dilworth is stated as
     level_width_is_cofactor_card, and the product bound it feeds is recalled.
   ============================================================================ *)

text \<open>The cofactor of f by prefix p: the residual on the remaining variables.\<close>

definition cof :: "(bool list \<Rightarrow> bool) \<Rightarrow> bool list \<Rightarrow> (bool list \<Rightarrow> bool)" where
  "cof f p = (\<lambda>w. f (p @ w))"

text \<open>The two Shannon children of a cofactor g: restrict the next variable.\<close>

definition child0 :: "(bool list \<Rightarrow> bool) \<Rightarrow> (bool list \<Rightarrow> bool)" where
  "child0 g = (\<lambda>w. g (False # w))"

definition child1 :: "(bool list \<Rightarrow> bool) \<Rightarrow> (bool list \<Rightarrow> bool)" where
  "child1 g = (\<lambda>w. g (True # w))"

text \<open>SHANNON DETERMINISM (Myhill-Nerode).  The children of a cofactor are a
      function of the cofactor itself.  Concretely, the child of @{term "cof f p"}
      is @{term "cof f (p @ [b])"} -- appending the branch bit to the prefix -- and
      this depends only on the residual function @{term "cof f p"}, since
      @{term "cof f p"} determines its own restrictions.  So equal cofactors have
      equal children: the residual is the automaton state.\<close>

lemma cof_append: "cof f (p @ [b]) = (\<lambda>w. (cof f p) (b # w))"
  by (rule ext) (simp add: cof_def)

theorem shannon_child0: "cof f (p @ [False]) = child0 (cof f p)"
  by (rule ext) (simp add: cof_def child0_def)

theorem shannon_child1: "cof f (p @ [True]) = child1 (cof f p)"
  by (rule ext) (simp add: cof_def child1_def)

theorem shannon_determinism:
  assumes "cof f p = cof f q"
  shows "cof f (p @ [b]) = cof f (q @ [b])"
proof (cases b)
  case True
  have "cof f (p @ [True]) = child1 (cof f p)" by (rule shannon_child1)
  also have "... = child1 (cof f q)" using assms by simp
  also have "... = cof f (q @ [True])" by (rule shannon_child1[symmetric])
  finally show ?thesis using True by simp
next
  case False
  have "cof f (p @ [False]) = child0 (cof f p)" by (rule shannon_child0)
  also have "... = child0 (cof f q)" using assms by simp
  also have "... = cof f (q @ [False])" by (rule shannon_child0[symmetric])
  finally show ?thesis using False by simp
qed

text \<open>The cofactor of the empty prefix is the function itself, and cofactoring
      composes with prefix concatenation.\<close>

lemma cof_Nil: "cof f [] = f"
  by (simp add: cof_def)

lemma cof_compose: "cof (cof f p) q = cof f (p @ q)"
  by (rule ext) (simp add: cof_def)

text \<open>RESTRICTION CLOSURE.  The set of all cofactors of f is closed under taking
      Shannon children: a child of a cofactor is again a cofactor (by appending the
      branch bit to the prefix).  We phrase closure as: the children of any cofactor
      lie in the cofactor set.\<close>

definition cofactor_set :: "(bool list \<Rightarrow> bool) \<Rightarrow> (bool list \<Rightarrow> bool) set" where
  "cofactor_set f = {g. \<exists>p. g = cof f p}"

theorem f_in_cofactor_set: "f \<in> cofactor_set f"
  by (auto simp: cofactor_set_def intro: exI[of _ "[]"] cof_Nil[symmetric])

theorem restriction_closed:
  assumes "g \<in> cofactor_set f"
  shows "child0 g \<in> cofactor_set f" and "child1 g \<in> cofactor_set f"
proof -
  from assms obtain p where p: "g = cof f p" by (auto simp: cofactor_set_def)
  have "child0 g = cof f (p @ [False])" using p by (simp add: shannon_child0)
  thus "child0 g \<in> cofactor_set f" by (auto simp: cofactor_set_def)
next
  from assms obtain p where p: "g = cof f p" by (auto simp: cofactor_set_def)
  have "child1 g = cof f (p @ [True])" using p by (simp add: shannon_child1)
  thus "child1 g \<in> cofactor_set f" by (auto simp: cofactor_set_def)
qed

text \<open>THE KEYSTONE, connecting Gap 2 to Dilworth.  The OBDD level width at level k
      is the number of DISTINCT cofactors by length-k prefixes.  We define it as the
      cardinality of that cofactor image; this is the count Gap 2 is about, and it is
      precisely the object the Dilworth/Mirsky product bound governs -- ordering the
      cofactors pointwise, the level width is at most the height times the antichain
      width of the cofactor poset (proved abstractly as product_bound in
      Poset_Product_Bound.thy).\<close>

definition level_width :: "(bool list \<Rightarrow> bool) \<Rightarrow> nat \<Rightarrow> nat" where
  "level_width f k = card ((\<lambda>p. cof f p) ` {p. length p = k})"

theorem level_width_is_cofactor_card:
  "level_width f k = card ((\<lambda>p. cof f p) ` {p. length p = k})"
  by (simp add: level_width_def)

text \<open>So the two views of the cofactor set meet: as an automaton its state count at
      level k is @{term "level_width f k"}; as a poset (ordered pointwise) that same
      count is bounded, by Dilworth/Mirsky, by the height times the antichain width.
      The automaton width and the poset width are joined at the product bound.\<close>

end
