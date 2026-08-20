theory Cofactor_Nature
  imports Main
begin

(* ============================================================================
   THE NATURE OF THE COFACTORS.

   The verifier tracks Boolean wire functions; the number of DISTINCT cofactors
   (Shannon residuals) of a function at each level is the OBDD width there.  This
   theory records provable facts about the NATURE of those cofactors, for a
   MONOTONE function -- which the wire functions are (Comparator_Monotone.thy).

   A Boolean function on length-n inputs is a predicate on bool lists.  Fixing the
   first k variables to a prefix p gives a cofactor: the residual function on the
   remaining n-k variables, w |-> f (p @ w).

   PROVEN HERE:
     P1  cof_monotone      -- a cofactor of a monotone function is monotone.
     P2  shannon_ordered   -- the two Shannon cofactors (split on the first
                              variable) are ordered: the True-cofactor pointwise
                              dominates the False-cofactor.

   These were discovered exploratorily (tools/cofactor_nature.py); alongside them
   the measured (not yet proven) facts are: the cofactor set at each level is a
   poset of small ANTICHAIN WIDTH (observed 2 for n<=6), which by Dilworth would
   give a per-wire cofactor count of O(width * n) -- the route to the width bound.
   ============================================================================ *)

definition vleq :: "bool list \<Rightarrow> bool list \<Rightarrow> bool" (infix "\<sqsubseteq>" 50) where
  "vleq x y \<longleftrightarrow> length x = length y \<and> (\<forall>i < length x. x!i \<longrightarrow> y!i)"

definition mono_on :: "(bool list \<Rightarrow> bool) \<Rightarrow> nat \<Rightarrow> bool" where
  "mono_on f n \<longleftrightarrow> (\<forall>x y. length x = n \<and> length y = n \<and> x \<sqsubseteq> y \<longrightarrow> f x \<longrightarrow> f y)"

definition cof :: "(bool list \<Rightarrow> bool) \<Rightarrow> bool list \<Rightarrow> (bool list \<Rightarrow> bool)" where
  "cof f p = (\<lambda>w. f (p @ w))"

lemma cof_apply: "cof f p w = f (p @ w)"
  by (simp add: cof_def)

text \<open>Appending a common prefix preserves the product order.\<close>

lemma append_vleq:
  assumes "length w1 = length w2" and "w1 \<sqsubseteq> w2"
  shows "(p @ w1) \<sqsubseteq> (p @ w2)"
  unfolding vleq_def
proof safe
  show "length (p @ w1) = length (p @ w2)" using assms(1) by simp
next
  fix i assume i: "i < length (p @ w1)" and pi: "(p @ w1)!i"
  show "(p @ w2)!i"
  proof (cases "i < length p")
    case True thus ?thesis using pi by (simp add: nth_append)
  next
    case False hence ge: "\<not> i < length p" by simp
    let ?j = "i - length p"
    have j1: "?j < length w1" using i ge by (simp add: nth_append)
    have "w1!?j" using pi ge by (simp add: nth_append)
    hence "w2!?j" using assms(2) j1 by (simp add: vleq_def)
    thus ?thesis using ge by (simp add: nth_append)
  qed
qed

lemma prefix_vleq:
  assumes "length p1 = length p2" and "p1 \<sqsubseteq> p2"
  shows "(p1 @ w) \<sqsubseteq> (p2 @ w)"
  unfolding vleq_def
proof safe
  show "length (p1 @ w) = length (p2 @ w)" using assms(1) by simp
next
  fix i assume i: "i < length (p1 @ w)" and pi: "(p1 @ w)!i"
  show "(p2 @ w)!i"
  proof (cases "i < length p1")
    case True
    hence "p1!i" using pi by (simp add: nth_append)
    hence "p2!i" using assms True by (simp add: vleq_def)
    thus ?thesis using True assms(1) by (simp add: nth_append)
  next
    case False hence ge: "\<not> i < length p1" by simp
    hence "(p1 @ w)!i = w!(i - length p1)" by (simp add: nth_append)
    moreover have "(p2 @ w)!i = w!(i - length p2)"
      using ge assms(1) by (simp add: nth_append)
    ultimately show ?thesis using pi assms(1) by simp
  qed
qed

text \<open>P1: a cofactor of a monotone function is monotone (on the residual arity).\<close>

theorem cof_monotone:
  assumes "mono_on f n" and "length p = k" and "k \<le> n"
  shows "mono_on (cof f p) (n - k)"
proof (unfold mono_on_def, intro allI impI)
  fix w1 w2
  assume H: "length w1 = n - k \<and> length w2 = n - k \<and> w1 \<sqsubseteq> w2" and c1: "cof f p w1"
  hence l1: "length w1 = n - k" and l2: "length w2 = n - k" and le: "w1 \<sqsubseteq> w2" by auto
  have lp1: "length (p @ w1) = n" using assms(2,3) l1 by simp
  have lp2: "length (p @ w2) = n" using assms(2,3) l2 by simp
  have vl: "(p @ w1) \<sqsubseteq> (p @ w2)" using append_vleq[OF _ le] l1 l2 by simp
  have "f (p @ w1)" using c1 by (simp add: cof_apply)
  hence "f (p @ w2)" using assms(1) lp1 lp2 vl unfolding mono_on_def by blast
  thus "cof f p w2" by (simp add: cof_apply)
qed

text \<open>P2: the two Shannon cofactors of a monotone function, splitting on the first
      variable, are ordered -- the True-cofactor pointwise dominates the False one.\<close>

theorem shannon_ordered:
  assumes "mono_on f n" and "n \<ge> 1" and "length w = n - 1"
  shows "(cof f [False]) w \<longrightarrow> (cof f [True]) w"
proof
  assume "(cof f [False]) w"
  hence fF: "f (False # w)" by (simp add: cof_apply)
  have lF: "length (False # w) = n" using assms(2,3) by simp
  have lT: "length (True # w) = n" using assms(2,3) by simp
  have "w \<sqsubseteq> w" by (simp add: vleq_def)
  hence "(False # w) \<sqsubseteq> (True # w)"
    by (simp add: vleq_def nth_Cons' split: nat.split)
  hence "f (True # w)" using assms(1) lF lT fF unfolding mono_on_def by blast
  thus "(cof f [True]) w" by (simp add: cof_apply)
qed

text \<open>C: the EXTREMAL cofactors.  Among all length-k prefixes, the all-False
      prefix gives the pointwise-smallest cofactor and the all-True prefix the
      pointwise-largest.  So the cofactor poset at each level is BOUNDED, with
      bounds realised by the constant prefixes.  (This structurally explains why
      each level's cofactor set has a min and a max.)\<close>

lemma const_false_least:
  "length p = k \<Longrightarrow> (replicate k False) \<sqsubseteq> p"
  by (simp add: vleq_def)

lemma const_true_greatest:
  "length p = k \<Longrightarrow> p \<sqsubseteq> (replicate k True)"
  by (simp add: vleq_def)

theorem cofactor_extremal:
  assumes "mono_on f n" and "length p = k" and "k \<le> n" and "length w = n - k"
  shows "(cof f (replicate k False)) w \<longrightarrow> (cof f p) w"
    and "(cof f p) w \<longrightarrow> (cof f (replicate k True)) w"
proof -
  \<comment> \<open>lower bound: all-False prefix cofactor is below the p cofactor\<close>
  have lF: "length (replicate k False @ w) = n" using assms(2,3,4) by simp
  have lp: "length (p @ w) = n" using assms(2,3,4) by simp
  have "(replicate k False @ w) \<sqsubseteq> (p @ w)"
    using prefix_vleq[OF _ const_false_least[OF assms(2)]] assms(2) by simp
  hence "f (replicate k False @ w) \<longrightarrow> f (p @ w)"
    using assms(1) lF lp unfolding mono_on_def by blast
  thus "(cof f (replicate k False)) w \<longrightarrow> (cof f p) w" by (simp add: cof_apply)
next
  \<comment> \<open>upper bound: p cofactor is below the all-True prefix cofactor\<close>
  have lp: "length (p @ w) = n" using assms(2,3,4) by simp
  have lT: "length (replicate k True @ w) = n" using assms(2,3,4) by simp
  have "(p @ w) \<sqsubseteq> (replicate k True @ w)"
    using prefix_vleq[OF _ const_true_greatest[OF assms(2)]] assms(2) by simp
  hence "f (p @ w) \<longrightarrow> f (replicate k True @ w)"
    using assms(1) lp lT unfolding mono_on_def by blast
  thus "(cof f p) w \<longrightarrow> (cof f (replicate k True)) w" by (simp add: cof_apply)
qed

text \<open>THE ANTIPODE.  Boolean duality is the antipode of the monotone-function
      structure: an order-REVERSING INVOLUTION.  For a function on bool lists,
      @{term "dualf f x = (\<not> f (map Not x))"}.  This captures, at the level of a
      single wire function, the min<->max antipodal symmetry a sorting network
      carries (dual(wire i) = wire (n-1-i) for a sorter).\<close>

definition dualf :: "(bool list \<Rightarrow> bool) \<Rightarrow> (bool list \<Rightarrow> bool)" where
  "dualf f = (\<lambda>x. \<not> f (map Not x))"

text \<open>Complementing a list is an involution and reverses the product order.\<close>

lemma Not_Not [simp]: "Not \<circ> Not = id"
  by auto
lemma map_Not_Not [simp]: "map Not (map Not x) = x"
  by (simp add: comp_def)

lemma length_map_Not [simp]: "length (map Not x) = length x"
  by simp

lemma vleq_map_Not:
  assumes "x \<sqsubseteq> y"
  shows "(map Not y) \<sqsubseteq> (map Not x)"
  using assms unfolding vleq_def by auto

text \<open>The antipode is an INVOLUTION.\<close>

theorem dualf_involution: "dualf (dualf f) = f"
  by (simp add: dualf_def comp_def)

text \<open>The antipode REVERSES the pointwise (implication) order on functions of a
      fixed arity: if f is below g everywhere, then dualf g is below dualf f.\<close>

theorem dualf_order_reversing:
  assumes "\<forall>x. length x = n \<longrightarrow> f x \<longrightarrow> g x"
  shows "\<forall>x. length x = n \<longrightarrow> dualf g x \<longrightarrow> dualf f x"
proof (intro allI impI)
  fix x assume lx: "length x = n" and dg: "dualf g x"
  have "\<not> g (map Not x)" using dg by (simp add: dualf_def)
  moreover have "length (map Not x) = n" using lx by simp
  ultimately have "\<not> f (map Not x)" using assms by blast
  thus "dualf f x" by (simp add: dualf_def)
qed

text \<open>The antipode PRESERVES monotonicity: the dual of a monotone function is
      monotone.  (So the antipode maps the cofactor world to itself.)\<close>

theorem dualf_mono:
  assumes "mono_on f n"
  shows "mono_on (dualf f) n"
  unfolding mono_on_def
proof (intro allI impI)
  fix x y
  assume H: "length x = n \<and> length y = n \<and> x \<sqsubseteq> y" and dx: "dualf f x"
  hence lx: "length x = n" and ly: "length y = n" and le: "x \<sqsubseteq> y" by auto
  have "\<not> f (map Not x)" using dx by (simp add: dualf_def)
  moreover have "(map Not y) \<sqsubseteq> (map Not x)" using vleq_map_Not[OF le] .
  moreover have "length (map Not y) = n" "length (map Not x) = n" using lx ly by simp_all
  ultimately have "\<not> f (map Not y)"
    using assms unfolding mono_on_def by blast
  thus "dualf f y" by (simp add: dualf_def)
qed

text \<open>THE FORM OF THE BROKEN LATTICE.  The cofactors live in the ambient lattice
      of bool lists under the pointwise (product) order, whose meet and join are
      the pointwise conjunction and disjunction.  That ambient lattice is
      DISTRIBUTIVE.  The cofactor set is a sub-POSET of it -- not in general a
      sub-lattice (the ambient meet/join can leave the set: the 'break') -- but it
      sits inside the distributive INTERVAL bounded by the constant-prefix
      cofactors.\<close>

definition vmeet :: "bool list \<Rightarrow> bool list \<Rightarrow> bool list" where
  "vmeet x y = map2 (\<and>) x y"

definition vjoin :: "bool list \<Rightarrow> bool list \<Rightarrow> bool list" where
  "vjoin x y = map2 (\<or>) x y"

lemma length_vmeet [simp]: "length x = length y \<Longrightarrow> length (vmeet x y) = length x"
  by (simp add: vmeet_def)

lemma length_vjoin [simp]: "length x = length y \<Longrightarrow> length (vjoin x y) = length x"
  by (simp add: vjoin_def)

lemma nth_vmeet: "\<lbrakk>length x = length y; i < length x\<rbrakk> \<Longrightarrow> (vmeet x y)!i = (x!i \<and> y!i)"
  by (simp add: vmeet_def)

lemma nth_vjoin: "\<lbrakk>length x = length y; i < length x\<rbrakk> \<Longrightarrow> (vjoin x y)!i = (x!i \<or> y!i)"
  by (simp add: vjoin_def)

text \<open>vmeet is the greatest lower bound and vjoin the least upper bound for the
      product order: they make the bool-list order a LATTICE.\<close>

lemma vmeet_lb: "\<lbrakk>length x = length y\<rbrakk> \<Longrightarrow> (vmeet x y) \<sqsubseteq> x \<and> (vmeet x y) \<sqsubseteq> y"
  by (auto simp: vleq_def nth_vmeet)

lemma vmeet_greatest:
  "\<lbrakk>length x = length y; z \<sqsubseteq> x; z \<sqsubseteq> y\<rbrakk> \<Longrightarrow> z \<sqsubseteq> (vmeet x y)"
  by (auto simp: vleq_def nth_vmeet)

lemma vjoin_ub: "\<lbrakk>length x = length y\<rbrakk> \<Longrightarrow> x \<sqsubseteq> (vjoin x y) \<and> y \<sqsubseteq> (vjoin x y)"
  by (auto simp: vleq_def nth_vjoin)

lemma vjoin_least:
  "\<lbrakk>length x = length y; x \<sqsubseteq> z; y \<sqsubseteq> z\<rbrakk> \<Longrightarrow> (vjoin x y) \<sqsubseteq> z"
  by (auto simp: vleq_def nth_vjoin)

text \<open>THE AMBIENT LATTICE IS DISTRIBUTIVE: meet distributes over join (pointwise,
      because conjunction distributes over disjunction).\<close>

theorem vlattice_distributive:
  assumes "length x = n" and "length y = n" and "length z = n"
  shows "vmeet x (vjoin y z) = vjoin (vmeet x y) (vmeet x z)"
proof (rule nth_equalityI)
  show "length (vmeet x (vjoin y z)) = length (vjoin (vmeet x y) (vmeet x z))"
    using assms by (simp add: vmeet_def vjoin_def)
next
  fix i assume "i < length (vmeet x (vjoin y z))"
  hence i: "i < n" using assms by (simp add: vmeet_def vjoin_def)
  have lyz: "length (vjoin y z) = n" using assms by (simp add: vjoin_def)
  have lxy: "length (vmeet x y) = n" using assms by (simp add: vmeet_def)
  have lxz: "length (vmeet x z) = n" using assms by (simp add: vmeet_def)
  have "(vmeet x (vjoin y z))!i = (x!i \<and> ((vjoin y z)!i))"
    using assms lyz i by (simp add: nth_vmeet)
  also have "... = (x!i \<and> (y!i \<or> z!i))"
    using assms i by (simp add: nth_vjoin)
  also have "... = ((x!i \<and> y!i) \<or> (x!i \<and> z!i))" by blast
  also have "... = ((vmeet x y)!i \<or> (vmeet x z)!i)"
    using assms i by (simp add: nth_vmeet)
  also have "... = (vjoin (vmeet x y) (vmeet x z))!i"
    using lxy lxz i by (simp add: nth_vjoin)
  finally show "(vmeet x (vjoin y z))!i = (vjoin (vmeet x y) (vmeet x z))!i" .
qed

text \<open>INTERVAL CONTAINMENT (the structural home of the broken lattice).  Every
      cofactor lies between the all-False-prefix cofactor (bottom) and the
      all-True-prefix cofactor (top).  So on any residual input, the whole cofactor
      set is sandwiched in the interval determined by the two constant prefixes --
      a DISTRIBUTIVE interval of the ambient lattice.\<close>

theorem cofactors_in_interval:
  assumes "mono_on f n" and "length p = k" and "k \<le> n" and "length w = n - k"
  shows "(cof f (replicate k False)) w \<longrightarrow> (cof f p) w"
    and "(cof f p) w \<longrightarrow> (cof f (replicate k True)) w"
  using cofactor_extremal[OF assms] by blast+

end
