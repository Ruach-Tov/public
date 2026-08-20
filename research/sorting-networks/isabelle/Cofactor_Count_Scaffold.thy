theory Cofactor_Count_Scaffold
  imports Main
begin

(* ============================================================================
   PROVING AROUND THE TIGHT FORMULA: the scaffolding.

   Heath's plan: prove around the tight width formula first, then the formula, then
   the loose bound, then contrast.  This theory supplies the scaffolding -- the
   supporting facts on which the tight (and loose) results rest.  Self-contained
   (imports Main); everything symbolic in the count and the parameter.

   A threshold T_t on m variables is true iff at least t of them are true.  Its
   normal-form parameter on length-m inputs is clamp s m = max 0 (min s (m+1)):
   below 1 the threshold is constantly true, above m constantly false.

   SCAFFOLD A  threshold normal form: T_s and T_{s'} agree on length-m inputs iff
               clamp s m = clamp s' m.  (So the distinct thresholds are indexed by
               {0, ..., m+1}.)
   SCAFFOLD B  cofactor form: the head cofactors of a threshold are thresholds --
               fixing the first variable to False keeps T_t, to True gives T_{t-1}.
   ============================================================================ *)

definition count_true :: "bool list \<Rightarrow> nat" where
  "count_true x = length (filter id x)"

definition thr :: "nat \<Rightarrow> bool list \<Rightarrow> bool" where
  "thr t x = (t \<le> count_true x)"

definition clamp :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "clamp s m = max 0 (min s (Suc m))"

text \<open>Basic bounds on the count.\<close>

lemma count_true_le: "count_true x \<le> length x"
  unfolding count_true_def by (rule length_filter_le)

text \<open>SCAFFOLD A.  On inputs of length m, a threshold is constant outside the range
      1..m: below 1 it is always true, above m always false.  So T_s on length-m
      inputs is determined by clamp s m, and two thresholds agree iff their clamps
      agree.  We prove the two directions that are used downstream: a threshold with
      parameter 0 is constantly true; with parameter > m, constantly false.\<close>

theorem threshold_zero_true:
  assumes "t = 0"
  shows "thr t x"
  using assms by (simp add: thr_def)

theorem threshold_over_false:
  assumes "length x = m" and "m < t"
  shows "\<not> thr t x"
proof -
  have "count_true x \<le> m" using assms(1) count_true_le[of x] by simp
  thus ?thesis using assms(2) by (simp add: thr_def)
qed

text \<open>The clamp normalises the parameter: on length-m inputs, thr t agrees with
      thr (clamp t m).\<close>

theorem thr_clamp_agrees:
  assumes "length x = m"
  shows "thr t x = thr (clamp t m) x"
proof (cases "t \<le> Suc m")
  case True
  hence "clamp t m = t" by (simp add: clamp_def)
  thus ?thesis by simp
next
  case False
  hence gt: "Suc m < t" by simp
  have "count_true x \<le> m" using assms count_true_le[of x] by simp
  hence "\<not> thr t x" and "\<not> thr (Suc m) x" using gt by (simp_all add: thr_def)
  moreover have "clamp t m = Suc m" using False by (simp add: clamp_def)
  ultimately show ?thesis by simp
qed

text \<open>Two thresholds agree on all length-m inputs iff their clamps agree.  Forward:
      distinct clamps are separated by the input of the appropriate weight.  Reverse:
      equal clamps give equal thresholds by the normalisation.\<close>

theorem thr_eq_iff_clamp_eq:
  "(\<forall>x. length x = m \<longrightarrow> thr s x = thr s' x) \<longleftrightarrow> (clamp s m = clamp s' m)"
proof
  assume L: "\<forall>x. length x = m \<longrightarrow> thr s x = thr s' x"
  show "clamp s m = clamp s' m"
  proof (rule ccontr)
    assume ne: "clamp s m \<noteq> clamp s' m"
    \<comment> \<open>wlog clamp s m < clamp s' m; the input with exactly (clamp s' m - 1) trues
        separates them\<close>
    have "\<exists>c. c \<le> m \<and> ((clamp s m \<le> c) \<noteq> (clamp s' m \<le> c))"
    proof -
      have cs: "clamp s m \<le> Suc m" "clamp s' m \<le> Suc m" by (simp_all add: clamp_def)
      show ?thesis
      proof (cases "clamp s m < clamp s' m")
        case True
        let ?c = "clamp s' m - 1"
        have "?c \<le> m" using cs by (auto simp: clamp_def)
        moreover have "clamp s m \<le> ?c" using True by simp
        moreover have "\<not> clamp s' m \<le> ?c" using True cs by (auto simp: clamp_def)
        ultimately show ?thesis by blast
      next
        case False
        hence "clamp s' m < clamp s m" using ne by simp
        let ?c = "clamp s m - 1"
        have "?c \<le> m" using cs by (auto simp: clamp_def)
        moreover have "clamp s' m \<le> ?c" using \<open>clamp s' m < clamp s m\<close> by simp
        moreover have "\<not> clamp s m \<le> ?c" using \<open>clamp s' m < clamp s m\<close> cs by (auto simp: clamp_def)
        ultimately show ?thesis by blast
      qed
    qed
    then obtain c where cm: "c \<le> m" and sep: "(clamp s m \<le> c) \<noteq> (clamp s' m \<le> c)" by blast
    let ?x = "replicate c True @ replicate (m - c) False"
    have lx: "length ?x = m" using cm by simp
    have ct: "count_true ?x = c" by (simp add: count_true_def)
    have "thr s ?x = (clamp s m \<le> c)"
      using lx ct thr_clamp_agrees[of ?x m s] by (simp add: thr_def)
    moreover have "thr s' ?x = (clamp s' m \<le> c)"
      using lx ct thr_clamp_agrees[of ?x m s'] by (simp add: thr_def)
    ultimately have "thr s ?x \<noteq> thr s' ?x" using sep by simp
    thus False using L lx by blast
  qed
next
  assume R: "clamp s m = clamp s' m"
  show "\<forall>x. length x = m \<longrightarrow> thr s x = thr s' x"
  proof (intro allI impI)
    fix x :: "bool list" assume lx: "length x = m"
    have "thr s x = thr (clamp s m) x" using thr_clamp_agrees[OF lx] .
    also have "... = thr (clamp s' m) x" using R by simp
    also have "... = thr s' x" using thr_clamp_agrees[OF lx] by simp
    finally show "thr s x = thr s' x" .
  qed
qed

text \<open>SCAFFOLD B.  Cofactors of a threshold are thresholds: the head cofactors.\<close>

lemma count_true_Cons [simp]:
  "count_true (b # xs) = (if b then Suc (count_true xs) else count_true xs)"
  by (simp add: count_true_def)

theorem cofactor_false: "thr t (False # w) = thr t w"
  by (simp add: thr_def)

theorem cofactor_true: "thr t (True # w) = thr (t - 1) w"
  by (cases t) (simp_all add: thr_def)

text \<open>Iterating: fixing a prefix p to specific values gives the threshold shifted
      down by the number of Trues in p.  We record the single-variable steps; the
      general form (thr t of (p @ w) = thr (t - weight p) w) follows by induction and
      is used in the level-count development.\<close>

theorem cofactor_prefix_weight:
  "thr t (replicate j True @ replicate i False @ w) = thr (t - j) w"
proof (induct j arbitrary: t)
  case 0 then show ?case by (induct i) (simp_all add: cofactor_false)
next
  case (Suc j)
  have "thr t (replicate (Suc j) True @ replicate i False @ w)
        = thr t (True # (replicate j True @ replicate i False @ w))" by simp
  also have "... = thr (t - 1) (replicate j True @ replicate i False @ w)"
    by (rule cofactor_true)
  also have "... = thr (t - 1 - j) w" using Suc by simp
  also have "... = thr (t - Suc j) w" by simp
  finally show ?case .
qed

text \<open>Reading.  These are the scaffolding around the tight formula: threshold normal
      form (@{thm thr_eq_iff_clamp_eq}) fixes the distinct thresholds on m variables
      to the clamp range, and the cofactor form (@{thm cofactor_false},
      @{thm cofactor_true}, @{thm cofactor_prefix_weight}) shows the cofactors of a
      threshold are thresholds shifted by the prefix weight.  On them the level count,
      the tight width, and the loose bound will rest.\<close>

end
