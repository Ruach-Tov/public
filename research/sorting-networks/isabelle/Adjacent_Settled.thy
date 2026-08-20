theory Adjacent_Settled
  imports Main
begin

(* ============================================================================
   THE VERIFIER'S CRITERION (lemma 3).

   A comparator network sorts every 0/1 input IFF every adjacent output pair is
   SETTLED: no 0/1 input produces output_i = 1 and output_{i+1} = 0.

   This is exactly the test the order-only ROBDD verifier performs -- for each
   adjacent wire pair it checks DIFF(w_i, w_{i+1}) = FALSE, i.e. the reachable set
   never has wire i high and wire i+1 low.  This lemma is the bridge from the
   abstract notion "the network sorts" to that concrete per-adjacent-pair check.

   The engine is elementary: a 0/1 (bool) list is sorted iff it has no adjacent
   DESCENT (a True immediately before a False).  We prove that, then lift it,
   pair by pair, to the verifier's criterion over the network's outputs.
   ============================================================================ *)

definition cstep :: "nat \<Rightarrow> nat \<Rightarrow> bool list \<Rightarrow> bool list" where
  "cstep a b v = v[a := (v!a \<and> v!b), b := (v!a \<or> v!b)]"

fun crun :: "(nat \<times> nat) list \<Rightarrow> bool list \<Rightarrow> bool list" where
  "crun [] v = v" |
  "crun ((a,b) # cs) v = crun cs (cstep a b v)"

lemma length_cstep [simp]: "length (cstep a b v) = length v"
  by (simp add: cstep_def)

lemma length_crun [simp]: "length (crun cs v) = length v"
  by (induct cs arbitrary: v) (auto split: prod.split)

text \<open>Sortedness of a bool list, by the pointwise order (False < True).\<close>

definition bsorted :: "bool list \<Rightarrow> bool" where
  "bsorted v \<longleftrightarrow> (\<forall>i j. i \<le> j \<and> j < length v \<longrightarrow> v!i \<longrightarrow> v!j)"

text \<open>No adjacent descent: never v!i = True and v!(i+1) = False.\<close>

definition no_descent :: "bool list \<Rightarrow> bool" where
  "no_descent v \<longleftrightarrow> (\<forall>i. Suc i < length v \<longrightarrow> v!i \<longrightarrow> v!(Suc i))"

text \<open>THE ENGINE: a bool list is sorted iff it has no adjacent descent.  The
      forward direction is immediate.  The reverse chains adjacent steps: if there
      is no descent then True propagates rightward, so any True at i forces True at
      every j >= i.\<close>

lemma no_descent_propagates:
  assumes "no_descent v" and "i \<le> j" and "j < length v" and "v!i"
  shows "v!j"
  using assms
proof (induct "j - i" arbitrary: i j)
  case 0
  then show ?case by simp
next
  case (Suc d)
  from Suc.hyps(2) have ij: "i < j" by simp
  hence sij: "Suc i \<le> j" by simp
  have vSi: "v!(Suc i)"
    using Suc.prems(1,4) ij Suc.prems(3)
    by (simp add: no_descent_def)
  have d_eq: "d = j - Suc i" using Suc.hyps(2) by simp
  show ?case
    using Suc.hyps(1)[OF d_eq Suc.prems(1) sij Suc.prems(3) vSi] .
qed

lemma bsorted_iff_no_descent: "bsorted v \<longleftrightarrow> no_descent v"
proof
  assume B: "bsorted v"
  show "no_descent v"
    unfolding no_descent_def
  proof (intro allI impI)
    fix i assume si: "Suc i < length v" and vi: "v!i"
    have all: "\<forall>p q. p \<le> q \<and> q < length v \<longrightarrow> v!p \<longrightarrow> v!q"
      using B by (simp add: bsorted_def)
    have "i \<le> Suc i \<and> Suc i < length v \<longrightarrow> v!i \<longrightarrow> v!(Suc i)"
      using all by blast
    thus "v!(Suc i)" using si vi by simp
  qed
next
  assume A: "no_descent v"
  show "bsorted v"
    unfolding bsorted_def
  proof (intro allI impI)
    fix i j assume ij: "i \<le> j \<and> j < length v" and vi: "v!i"
    show "v!j" using no_descent_propagates[OF A] ij vi by blast
  qed
qed

text \<open>The network sorts every 0/1 input.\<close>

definition sorts_all_bool :: "(nat \<times> nat) list \<Rightarrow> nat \<Rightarrow> bool" where
  "sorts_all_bool cs n \<longleftrightarrow> (\<forall>v. length v = n \<longrightarrow> bsorted (crun cs v))"

text \<open>Every adjacent output pair is settled: no 0/1 input gives output i = True,
      output (i+1) = False.  (The verifier's DIFF(w_i, w_{i+1}) = FALSE, over all
      adjacent i.)\<close>

definition all_adjacent_settled :: "(nat \<times> nat) list \<Rightarrow> nat \<Rightarrow> bool" where
  "all_adjacent_settled cs n \<longleftrightarrow>
     (\<forall>v. length v = n \<longrightarrow>
        (\<forall>i. Suc i < n \<longrightarrow> \<not> ((crun cs v)!i \<and> \<not> (crun cs v)!(Suc i))))"

text \<open>THE LEMMA (the verifier's criterion).  The network sorts every 0/1 input
      iff every adjacent output pair is settled.\<close>

theorem verifier_criterion:
  "sorts_all_bool cs n \<longleftrightarrow> all_adjacent_settled cs n"
proof
  assume S: "sorts_all_bool cs n"
  show "all_adjacent_settled cs n"
    unfolding all_adjacent_settled_def
  proof (intro allI impI)
    fix v :: "bool list" and i assume lv: "length v = n" and si: "Suc i < n"
    have "bsorted (crun cs v)" using S lv by (simp add: sorts_all_bool_def)
    hence "no_descent (crun cs v)" by (simp add: bsorted_iff_no_descent)
    thus "\<not> ((crun cs v)!i \<and> \<not> (crun cs v)!(Suc i))"
      using si lv by (simp add: no_descent_def)
  qed
next
  assume A: "all_adjacent_settled cs n"
  have Aun: "\<And>w i. length w = n \<Longrightarrow> Suc i < n \<Longrightarrow>
                  (crun cs w)!i \<longrightarrow> (crun cs w)!(Suc i)"
    using A by (simp add: all_adjacent_settled_def)
  show "sorts_all_bool cs n"
    unfolding sorts_all_bool_def
  proof (intro allI impI)
    fix v :: "bool list" assume lv: "length v = n"
    have "no_descent (crun cs v)"
      unfolding no_descent_def
    proof safe
      fix i assume si: "Suc i < length (crun cs v)" and vi: "(crun cs v)!i"
      have "Suc i < n" using si lv by simp
      thus "(crun cs v)!(Suc i)" using Aun[OF lv] vi by blast
    qed
    thus "bsorted (crun cs v)" by (simp add: bsorted_iff_no_descent)
  qed
qed

end
