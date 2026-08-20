theory Cofactor_Count_Real
  imports Cofactor_Count_Tight
begin

\<comment> \<open>Re-state locally (self-contained, avoiding the duplicate-constant clash from importing
    the sibling threshold theories): count, threshold, the normal-form lemmas, and the
    general-prefix cofactor.\<close>

definition count_true :: "bool list \<Rightarrow> nat" where
  "count_true x = length (filter id x)"

definition thr :: "nat \<Rightarrow> bool list \<Rightarrow> bool" where
  "thr t x = (t \<le> count_true x)"

lemma count_true_le: "count_true x \<le> length x"
  unfolding count_true_def by (rule length_filter_le)

lemma count_true_append: "count_true (p @ w) = count_true p + count_true w"
  by (simp add: count_true_def)

lemma cofactor_general_prefix: "thr t (p @ w) = thr (t - count_true p) w"
proof -
  have "thr t (p @ w) = (t \<le> count_true p + count_true w)"
    by (simp add: thr_def count_true_append)
  also have "... = (t - count_true p \<le> count_true w)" by linarith
  also have "... = thr (t - count_true p) w" by (simp add: thr_def)
  finally show ?thesis .
qed

lemma thr_clamp_agrees:
  assumes "length x = m" shows "thr t x = thr (clamp t m) x"
proof (cases "t \<le> Suc m")
  case True hence "clamp t m = t" by (simp add: clamp_def)
  thus ?thesis by simp
next
  case False hence gt: "Suc m < t" by simp
  have "count_true x \<le> m" using assms count_true_le[of x] by simp
  hence "\<not> thr t x" and "\<not> thr (Suc m) x" using gt by (simp_all add: thr_def)
  moreover have "clamp t m = Suc m" using False by (simp add: clamp_def)
  ultimately show ?thesis by simp
qed

lemma thr_eq_iff_clamp_eq:
  "(\<forall>x. length x = m \<longrightarrow> thr s x = thr s' x) \<longleftrightarrow> (clamp s m = clamp s' m)"
proof
  assume L: "\<forall>x. length x = m \<longrightarrow> thr s x = thr s' x"
  show "clamp s m = clamp s' m"
  proof (rule ccontr)
    assume ne: "clamp s m \<noteq> clamp s' m"
    obtain c where cm: "c \<le> m" and sep: "(clamp s m \<le> c) \<noteq> (clamp s' m \<le> c)"
    proof -
      have cs: "clamp s m \<le> Suc m" "clamp s' m \<le> Suc m" by (simp_all add: clamp_def)
      show ?thesis
      proof (cases "clamp s m < clamp s' m")
        case True
        have "clamp s' m - 1 \<le> m" using cs by (auto simp: clamp_def)
        moreover have "clamp s m \<le> clamp s' m - 1" using True by simp
        moreover have "\<not> clamp s' m \<le> clamp s' m - 1" using True cs by (auto simp: clamp_def)
        ultimately show ?thesis using that by blast
      next
        case False hence "clamp s' m < clamp s m" using ne by simp
        have "clamp s m - 1 \<le> m" using cs by (auto simp: clamp_def)
        moreover have "clamp s' m \<le> clamp s m - 1" using \<open>clamp s' m < clamp s m\<close> by simp
        moreover have "\<not> clamp s m \<le> clamp s m - 1" using \<open>clamp s' m < clamp s m\<close> cs by (auto simp: clamp_def)
        ultimately show ?thesis using that by blast
      qed
    qed
    let ?x = "replicate c True @ replicate (m - c) False"
    have lx: "length ?x = m" using cm by simp
    have ct: "count_true ?x = c" by (simp add: count_true_def)
    have "thr s ?x = (clamp s m \<le> c)" using lx ct thr_clamp_agrees[of ?x m s] by (simp add: thr_def)
    moreover have "thr s' ?x = (clamp s' m \<le> c)" using lx ct thr_clamp_agrees[of ?x m s'] by (simp add: thr_def)
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

(* ============================================================================
   THIN 1 THICKENED: the level count IS the count of real cofactors.

   The count development worked with an abstract label set -- the clamped weights
   level_labels -- and bounded its cardinality.  To close the thread we show that
   cardinality equals the number of DISTINCT ACTUAL COFACTORS of the threshold wire
   at that level: the count machinery is about the real object cof f p, not a stand-in.

   The actual cofactor of T_t by a prefix p is, by the general-prefix theorem, the
   threshold T_{t - weight p} on the residual variables -- and on length-m inputs that
   is determined by its clamp (the normal form).  So the map
       (distinct cofactor function)  <->  (its clamped parameter)
   is a bijection between the actual cofactor set at level k and the label set
   level_labels.  Hence their cardinalities agree.

   Imports the tight-count and thickening theories (no name clash; both build on
   Cofactor_Count_Tight).  Symbolic throughout.
   ============================================================================ *)

text \<open>The actual cofactor of @{term "thr t"} by a length-k prefix, as a function on
      the residual inputs.  By @{thm cofactor_general_prefix} it equals
      @{term "thr (t - count_true p)"}; we work with the residual predicate directly.\<close>

definition real_cofactor :: "nat \<Rightarrow> bool list \<Rightarrow> (bool list \<Rightarrow> bool)" where
  "real_cofactor t p = (\<lambda>w. thr t (p @ w))"

lemma real_cofactor_is_threshold:
  "real_cofactor t p = thr (t - count_true p)"
  by (rule ext) (simp add: real_cofactor_def cofactor_general_prefix)

text \<open>The actual distinct cofactors at level k, restricted to residual inputs of
      length m = n-k (the relevant length), as a set of functions.  We index prefixes
      by all length-k bool lists.\<close>

definition real_cofactor_set :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> (bool list \<Rightarrow> bool) set" where
  "real_cofactor_set t k n =
     (\<lambda>p. \<lambda>w. if length w = n - k then thr (t - count_true p) w else undefined)
       ` {p. length p = k}"

text \<open>Map a cofactor (indexed by prefix weight) to its clamped label.  We show the
      real cofactor set is the image of the weight set under
      @{term "\<lambda>j. \<lambda>w. if length w = m then thr (clamp (t-j) m) w else undefined"},
      and that this is in bijection with the clamped labels.\<close>

text \<open>Two prefixes of the same weight give the same restricted cofactor; and the
      restricted cofactor is determined by the clamp of t - weight.  Hence the number
      of distinct restricted cofactors equals the number of distinct clamps -- the
      label count.\<close>

lemma restricted_cofactor_eq_clamp:
  fixes p :: "bool list"
  shows "(\<lambda>w. if length w = n - k then thr (t - count_true p) w else undefined)
       = (\<lambda>w. if length w = n - k then thr (clamp (t - count_true p) (n - k)) w else undefined)"
proof (rule ext)
  fix w :: "bool list"
  show "(if length w = n - k then thr (t - count_true p) w else undefined)
      = (if length w = n - k then thr (clamp (t - count_true p) (n - k)) w else undefined)"
  proof (cases "length w = n - k")
    case True
    then show ?thesis using thr_clamp_agrees[OF True, of "t - count_true p"] by simp
  qed simp
qed

text \<open>The restricted cofactor is an injective function of its clamp: distinct clamps
      give distinct restricted cofactors (they differ on the separating input).\<close>

lemma restricted_cofactor_inj_on_clamp:
  assumes "c \<le> Suc (n - k)" and "c' \<le> Suc (n - k)"
      and "(\<lambda>w. if length w = n - k then thr c w else undefined)
         = (\<lambda>w. if length w = n - k then thr c' w else undefined)"
  shows "c = c'"
proof -
  have "\<forall>w. length w = n - k \<longrightarrow> thr c w = thr c' w"
    using assms(3) by meson
  hence "clamp c (n - k) = clamp c' (n - k)"
    using thr_eq_iff_clamp_eq[of "n-k" c c'] by simp
  moreover have "clamp c (n - k) = c" using assms(1) by (simp add: clamp_def)
  moreover have "clamp c' (n - k) = c'" using assms(2) by (simp add: clamp_def)
  ultimately show ?thesis by simp
qed

text \<open>THE BIJECTION IN CARDINALITY.  The real cofactor set at level k and the label
      set level_labels have the same cardinality: both count the distinct clamped
      parameters clamp (t-j) (n-k) as j ranges over the prefix weights {0..k}.  Hence
      the number of distinct actual cofactors equals level_count.\<close>

theorem real_cofactor_count_eq_level_count:
  "card (real_cofactor_set t k n) = level_count t k n"
proof -
  \<comment> \<open>the real cofactor set is the image of the clamp-label set under the injective
      map c \<mapsto> (restricted threshold c); so their cardinalities agree\<close>
  define g where "g = (\<lambda>c::nat. (\<lambda>w. if length w = n - k then thr c w else undefined))"
  have img: "real_cofactor_set t k n = g ` (level_labels t k n)"
  proof
    show "real_cofactor_set t k n \<subseteq> g ` level_labels t k n"
    proof
      fix f assume "f \<in> real_cofactor_set t k n"
      then obtain p where lp: "length p = k"
        and f: "f = (\<lambda>w. if length w = n - k then thr (t - count_true p) w else undefined)"
        by (auto simp: real_cofactor_set_def)
      have "count_true p \<le> k" using lp count_true_le[of p] by simp
      hence wj: "clamp (t - count_true p) (n - k) \<in> level_labels t k n"
        by (auto simp: level_labels_def)
      have "f = g (clamp (t - count_true p) (n - k))"
        using f restricted_cofactor_eq_clamp[of n k t p] by (simp add: g_def)
      thus "f \<in> g ` level_labels t k n" using wj by blast
    qed
  next
    show "g ` level_labels t k n \<subseteq> real_cofactor_set t k n"
    proof
      fix f assume "f \<in> g ` level_labels t k n"
      then obtain j where j: "j \<le> k" and f: "f = g (clamp (t - j) (n - k))"
        by (auto simp: level_labels_def)
      let ?p = "replicate j True @ replicate (k - j) False"
      have lp: "length ?p = k" using j by simp
      have cp: "count_true ?p = j" by (simp add: count_true_def)
      have "(\<lambda>w. if length w = n - k then thr (t - count_true ?p) w else undefined)
              = g (clamp (t - j) (n - k))"
        using cp restricted_cofactor_eq_clamp[of n k t ?p] by (simp add: g_def)
      hence "f = (\<lambda>w. if length w = n - k then thr (t - count_true ?p) w else undefined)"
        using f by simp
      thus "f \<in> real_cofactor_set t k n" using lp by (auto simp: real_cofactor_set_def)
    qed
  qed
  have "inj_on g (level_labels t k n)"
  proof (rule inj_onI)
    fix c c' assume "c \<in> level_labels t k n" and "c' \<in> level_labels t k n"
      and "g c = g c'"
    have cbound: "c \<le> Suc (n - k)" and c'bound: "c' \<le> Suc (n - k)"
      using \<open>c \<in> level_labels t k n\<close> \<open>c' \<in> level_labels t k n\<close>
      by (auto simp: level_labels_def clamp_def)
    show "c = c'"
      using restricted_cofactor_inj_on_clamp[OF cbound c'bound] \<open>g c = g c'\<close>
      by (simp add: g_def)
  qed
  hence "card (g ` level_labels t k n) = card (level_labels t k n)"
    by (rule card_image)
  thus ?thesis using img by (simp add: level_count_def)
qed

text \<open>Reading.  @{thm real_cofactor_count_eq_level_count} closes the thread's deepest
      thin place: the level count that the tight and loose bounds constrain is not an
      abstract label count but the number of DISTINCT ACTUAL COFACTORS of the wire
      function at that level.  The bijection is the clamp: each cofactor is a threshold,
      determined on the residual inputs by its clamped parameter, and distinct clamps
      give distinct cofactors.  So the width bounds are bounds on the real object.\<close>

end
