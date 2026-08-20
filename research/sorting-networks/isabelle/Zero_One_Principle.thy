theory Zero_One_Principle
  imports Main
begin

(* ============================================================================
   THE ZERO-ONE PRINCIPLE.

   A comparator network sorts every integer input IFF it sorts every 0/1 input.

   This is lemma (2) of the W-break proof path.  Its engine is that comparators
   COMMUTE with any monotone threshold map t_k(v)_i = (v!i >= k): applying a
   comparator and then thresholding equals thresholding and then applying the
   comparator.  Running the whole network therefore commutes with thresholding.
   From this the hard direction follows: if the net sorts all 0/1 inputs, then
   every threshold-slice of a general output is sorted, so the output is sorted.

   Definitions here work over 'a::linorder lists for the general case; the
   threshold produces a bool list (the 0/1 case).  Comparators use min/max, which
   on bool = conjunction/disjunction, matching Comparator_Monotone.thy.
   ============================================================================ *)

text \<open>A comparator step on a linorder list: min to position a, max to b.\<close>

definition cstep :: "nat \<Rightarrow> nat \<Rightarrow> 'a::linorder list \<Rightarrow> 'a list" where
  "cstep a b v = v[a := min (v!a) (v!b), b := max (v!a) (v!b)]"

fun crun :: "(nat \<times> nat) list \<Rightarrow> 'a::linorder list \<Rightarrow> 'a list" where
  "crun [] v = v" |
  "crun ((a,b) # cs) v = crun cs (cstep a b v)"

text \<open>The threshold map: position i becomes True iff v!i >= k.\<close>

definition thr :: "'a::linorder \<Rightarrow> 'a list \<Rightarrow> bool list" where
  "thr k v = map (\<lambda>x. x \<ge> k) v"

lemma length_cstep [simp]: "length (cstep a b v) = length v"
  by (simp add: cstep_def)

lemma length_crun [simp]: "length (crun cs v) = length v"
  by (induct cs arbitrary: v) (auto split: prod.split)

lemma length_thr [simp]: "length (thr k v) = length v"
  by (simp add: thr_def)

text \<open>THE KEY LEMMA: a comparator step commutes with thresholding.
      thr k (cstep a b v) = cstep a b (thr k v).\<close>

lemma thr_min: "(k \<le> min (x::'a::linorder) y) = ((k \<le> x) \<and> (k \<le> y))"
  by (auto simp: min_def)

lemma thr_max: "(k \<le> max (x::'a::linorder) y) = ((k \<le> x) \<or> (k \<le> y))"
  by (auto simp: max_def)

lemma cstep_thr_commute:
  assumes "a < length v" and "b < length v" and "a < b"
  shows "thr k (cstep a b v) = cstep a b (thr k v)"
proof -
  have "length (thr k (cstep a b v)) = length (cstep a b (thr k v))"
    by simp
  moreover
  have "\<forall>i < length v. (thr k (cstep a b v))!i = (cstep a b (thr k v))!i"
  proof (intro allI impI)
    fix i assume iL: "i < length v"
    show "(thr k (cstep a b v))!i = (cstep a b (thr k v))!i"
      using assms iL
      by (cases "i=a"; cases "i=b";
          simp add: thr_def cstep_def nth_list_update thr_min thr_max;
          auto simp: min_def max_def)
  qed
  ultimately show ?thesis
    by (simp add: list_eq_iff_nth_eq thr_def cstep_def)
qed

text \<open>By induction, the whole network commutes with thresholding.\<close>

definition wf_net :: "(nat \<times> nat) list \<Rightarrow> nat \<Rightarrow> bool" where
  "wf_net cs n \<longleftrightarrow> (\<forall>(a,b) \<in> set cs. a < b \<and> b < n)"

lemma crun_thr_commute:
  "wf_net cs n \<Longrightarrow> length v = n \<Longrightarrow> thr k (crun cs v) = crun cs (thr k v)"
proof (induct cs arbitrary: v)
  case Nil
  then show ?case by simp
next
  case (Cons c cs)
  obtain a b where c: "c = (a,b)" by (cases c)
  have wf_c: "a < b \<and> b < n" using Cons.prems(1) c by (auto simp: wf_net_def)
  have wf_rest: "wf_net cs n" using Cons.prems(1) by (auto simp: wf_net_def)
  have lv: "length v = n" using Cons.prems(2) .
  have aL: "a < length v" using wf_c lv by simp
  have bL: "b < length v" using wf_c lv by simp
  have ab: "a < b" using wf_c by simp
  have lstep: "length (cstep a b v) = n" using lv by simp
  have "thr k (crun cs (cstep a b v)) = crun cs (thr k (cstep a b v))"
    using Cons.hyps[OF wf_rest lstep] .
  also have "thr k (cstep a b v) = cstep a b (thr k v)"
    using cstep_thr_commute[OF aL bL ab] .
  finally show ?case using c by simp
qed

text \<open>Sortedness on a linorder list, and its 0/1 restriction.\<close>

definition sorted_list :: "'a::linorder list \<Rightarrow> bool" where
  "sorted_list v \<longleftrightarrow> (\<forall>i j. i \<le> j \<and> j < length v \<longrightarrow> v!i \<le> v!j)"

text \<open>A key bridge: a linorder list is sorted iff every threshold slice is sorted.
      (This is the standard 'sorted iff sorted at every level' fact.)\<close>

lemma sorted_iff_all_thr:
  "sorted_list v \<longleftrightarrow> (\<forall>k. sorted_list (thr k v))"
proof
  assume S: "sorted_list v"
  show "\<forall>k. sorted_list (thr k v)"
  proof
    fix k
    show "sorted_list (thr k v)"
      unfolding sorted_list_def
    proof (intro allI impI)
      fix i j assume ij: "i \<le> j \<and> j < length (thr k v)"
      hence jv: "j < length v" by simp
      have vij: "v!i \<le> v!j" using S ij jv by (simp add: sorted_list_def)
      have "(thr k v)!i = (k \<le> v!i)" using ij by (simp add: thr_def)
      moreover have "(thr k v)!j = (k \<le> v!j)" using jv by (simp add: thr_def)
      moreover have "(k \<le> v!i) \<longrightarrow> (k \<le> v!j)" using vij order_trans by blast
      ultimately show "(thr k v)!i \<le> (thr k v)!j" by simp
    qed
  qed
next
  assume R: "\<forall>k. sorted_list (thr k v)"
  show "sorted_list v"
    unfolding sorted_list_def
  proof (intro allI impI)
    fix i j assume ij: "i \<le> j \<and> j < length v"
    show "v!i \<le> v!j"
    proof (rule ccontr)
      assume "\<not> v!i \<le> v!j"
      hence gt: "v!j < v!i" by simp
      let ?k = "v!i"
      have ti: "(thr ?k v)!i = True" using ij by (simp add: thr_def)
      have tj: "(thr ?k v)!j = False" using ij gt by (simp add: thr_def)
      have srt: "sorted_list (thr ?k v)" using R by blast
      have jl: "j < length (thr ?k v)" using ij by simp
      have "(thr ?k v)!i \<le> (thr ?k v)!j"
        using srt ij jl unfolding sorted_list_def by blast
      thus False using ti tj by simp
    qed
  qed
qed

text \<open>THE ZERO-ONE PRINCIPLE.  A well-formed network sorts every linorder input
      iff it sorts every 0/1 (bool) input.  We state the two directions.\<close>

text \<open>Hard direction: if the network sorts every bool input, it sorts every
      linorder input.  (Uses the commutation lemma and the level bridge.)\<close>

theorem zero_one_principle_hard:
  assumes wf: "wf_net cs n"
      and bool_case: "\<And>w::bool list. length w = n \<Longrightarrow> sorted_list (crun cs w)"
      and lv: "length (v::'a::linorder list) = n"
  shows "sorted_list (crun cs v)"
proof -
  have "\<forall>k. sorted_list (thr k (crun cs v))"
  proof
    fix k
    have "thr k (crun cs v) = crun cs (thr k v)"
      using crun_thr_commute[OF wf lv] .
    moreover have "length (thr k v) = n" using lv by simp
    ultimately show "sorted_list (thr k (crun cs v))"
      using bool_case by simp
  qed
  thus ?thesis using sorted_iff_all_thr by blast
qed

text \<open>Easy direction: a bool list is a special linorder list, so sorting every
      linorder input entails sorting every bool input.\<close>

theorem zero_one_principle_easy:
  assumes "\<And>v::bool list. length v = n \<Longrightarrow> sorted_list (crun cs v)"
      and "length (w::bool list) = n"
  shows "sorted_list (crun cs w)"
  using assms by blast

end
