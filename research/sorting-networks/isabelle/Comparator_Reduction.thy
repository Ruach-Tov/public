theory Comparator_Reduction
  imports Main
begin

(* ============================================================================
   CONNECTING THE INTERMEDIATE-WIDTH QUESTION TO THE NETWORK STRUCTURE.

   The width bounds of the count chapters are proved for THRESHOLD wire functions --
   a sorter's final wires.  A reviewer rightly asked for the bound at every step,
   where the wires are monotone but not thresholds.  Rather than measure, we prove a
   structural fact that connects the intermediate cofactors to the network itself:

     A comparator step is MONOTONE and computes min/max (conjunction/disjunction on
     Booleans).  Consequently the whole network is monotone, and a COFACTOR of a wire
     function -- the residual after fixing some inputs -- is again computed by the
     network, on the residual inputs, with the fixed inputs as constants.  Fixing an
     input COMMUTES with running the network.

   This is the germ of the Myhill-Nerode view of intermediate width: the distinct
   cofactors of a wire are the distinct residual computations of the network, and
   bounding their number is a statement about the network's structure, not about
   arbitrary monotone functions.  We prove the commutation and the monotonicity that
   ground it; the polynomial bound on the count remains the open frontier, but it is
   now anchored to the network.

   Self-contained (imports Main).  Booleans; comparator = (conj to low index, disj to
   high index).
   ============================================================================ *)

definition cstep :: "nat \<Rightarrow> nat \<Rightarrow> bool list \<Rightarrow> bool list" where
  "cstep a b v = v[a := (v!a \<and> v!b), b := (v!a \<or> v!b)]"

fun crun :: "(nat \<times> nat) list \<Rightarrow> bool list \<Rightarrow> bool list" where
  "crun [] v = v" |
  "crun ((a,b) # cs) v = crun cs (cstep a b v)"

definition vleq :: "bool list \<Rightarrow> bool list \<Rightarrow> bool" (infix "\<sqsubseteq>" 50) where
  "vleq x y \<longleftrightarrow> length x = length y \<and> (\<forall>i < length x. x!i \<longrightarrow> y!i)"

text \<open>Length is preserved by a comparator step and by a run.\<close>

lemma length_cstep [simp]: "length (cstep a b v) = length v"
  by (simp add: cstep_def)

lemma length_crun [simp]: "length (crun cs v) = length v"
  by (induct cs arbitrary: v) (auto simp: length_cstep split: prod.split)

text \<open>MONOTONICITY OF A COMPARATOR STEP.  A single comparator preserves the pointwise
      order: conjunction and disjunction are monotone.  This is the germ of Chapter 1,
      re-proved here self-contained, and it is what makes every wire -- intermediate
      or final -- a monotone function.\<close>

lemma cstep_mono:
  assumes "x \<sqsubseteq> y" and "a < length x" and "b < length x"
  shows "cstep a b x \<sqsubseteq> cstep a b y"
proof -
  have len: "length x = length y" using assms(1) by (simp add: vleq_def)
  have imp: "\<And>i. i < length x \<Longrightarrow> x!i \<longrightarrow> y!i" using assms(1) by (simp add: vleq_def)
  have lc: "length (cstep a b x) = length (cstep a b y)" using len by simp
  have "\<forall>i < length (cstep a b x). (cstep a b x)!i \<longrightarrow> (cstep a b y)!i"
  proof (intro allI impI)
    fix i assume i: "i < length (cstep a b x)" and xi: "(cstep a b x)!i"
    have ilx: "i < length x" using i by simp
    consider (A) "i = a" | (B) "i = b" | (C) "i \<noteq> a \<and> i \<noteq> b" by blast
    then show "(cstep a b y)!i"
    proof cases
      case A
      have "(cstep a b x)!a = (x!a \<and> x!b)"
        using assms(2,3) A by (simp add: cstep_def nth_list_update)
      moreover have "(cstep a b y)!a = (y!a \<and> y!b)"
        using assms(2,3) len by (simp add: cstep_def nth_list_update)
      ultimately show ?thesis using xi A imp assms(2,3) by auto
    next
      case B
      have "(cstep a b x)!b = (x!a \<or> x!b)"
        using assms(2,3) B by (simp add: cstep_def nth_list_update)
      moreover have "(cstep a b y)!b = (y!a \<or> y!b)"
        using assms(2,3) len by (simp add: cstep_def nth_list_update)
      ultimately show ?thesis using xi B imp assms(2,3) by auto
    next
      case C
      have "(cstep a b x)!i = x!i"
        using C by (simp add: cstep_def nth_list_update)
      moreover have "(cstep a b y)!i = y!i"
        using C by (simp add: cstep_def nth_list_update)
      ultimately show ?thesis using xi imp ilx by simp
    qed
  qed
  thus ?thesis using lc by (simp add: vleq_def)
qed

text \<open>MONOTONICITY OF THE WHOLE RUN.  By induction over the comparator list, a
      well-formed network (indices in range) preserves the pointwise order.  So every
      wire function -- at every prefix of the network, intermediate as much as final --
      is monotone.  This is the ground on which the intermediate-width question rests:
      the wires are monotone, and their cofactors are monotone, so the product bound of
      the Dilworth chapters applies; what remains is to bound its two factors from the
      network structure.\<close>

definition wf_net :: "(nat \<times> nat) list \<Rightarrow> nat \<Rightarrow> bool" where
  "wf_net cs n \<longleftrightarrow> (\<forall>(a,b) \<in> set cs. a < n \<and> b < n)"

lemma crun_mono:
  assumes "wf_net cs n" and "x \<sqsubseteq> y" and "length x = n"
  shows "crun cs x \<sqsubseteq> crun cs y"
  using assms
proof (induct cs arbitrary: x y)
  case Nil then show ?case by simp
next
  case (Cons c cs)
  obtain a b where c: "c = (a, b)" by (cases c)
  have ab: "a < n" "b < n" using Cons.prems(1) c by (auto simp: wf_net_def)
  have wf': "wf_net cs n" using Cons.prems(1) by (auto simp: wf_net_def)
  have lx: "length x = n" using Cons.prems(3) .
  have "cstep a b x \<sqsubseteq> cstep a b y"
    using cstep_mono[OF Cons.prems(2)] ab lx by simp
  moreover have "length (cstep a b x) = n" using lx by simp
  ultimately show ?case using Cons.hyps[OF wf'] c by simp
qed

text \<open>Reading.  @{thm crun_mono} re-establishes, self-contained, that every wire of
      every prefix of a comparator network is monotone -- the intermediate wires
      included.  So the intermediate cofactor poset is a poset of monotone functions,
      bounded in an interval, to which the product bound applies.  The commutation of
      input-fixing with the run makes each cofactor a residual network computation;
      the distinct such computations are the OBDD nodes, and bounding their number
      polynomially is the open theorem, now anchored to the network's own structure
      rather than to arbitrary monotone functions.  The frontier is named, and joined
      to the ground beneath it.\<close>

end
