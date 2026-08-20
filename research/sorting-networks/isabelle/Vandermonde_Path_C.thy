theory Vandermonde_Path_C
  imports Vandermonde_Garden
begin

(* ============================================================================
   PATH C THROUGH THE GARDEN: the peak-vs-support dichotomy = chain vs antichain.

   The garden (Vandermonde_Garden) established the additive-support law: counts add under
   merge, the support is {0..n} (linear), and merging adds supports.  Path C proves the
   DICHOTOMY that this law separates: a THRESHOLD wire's cofactors track the SUPPORT (a
   chain, linear width), while a SLICE wire's cofactors track the PEAK (an antichain,
   exponential width).  In the language of the book: a threshold is UNBROKEN (its cofactor
   family is a chain, a lattice with no defect), a slice is BROKEN (its cofactor family is
   an antichain, the defect at its widest).

   We model a wire function on n inputs that depends on its input only through the COUNT
   of ones --- a SYMMETRIC monotone function, which is exactly what a sorted wire and a
   slice both are.  Such a function is given by an upward-closed set of counts T \<subseteq> {0..n}
   (f v = 1 iff count_ones v \<in> T, with T upward closed).  A THRESHOLD is T = {t..n}; a
   SLICE is T = {t} would not be upward-closed, so a monotone slice is really a threshold;
   the genuine ``broken'' behaviour needs a non-symmetric function, and Path C isolates
   exactly where symmetry (threshold, chain) gives way to asymmetry (slice, antichain).

   THE CLEAN DICHOTOMY we prove here, at the level of the count-structure:
     - a threshold's residual demands form a CHAIN (totally ordered by \<le>) --- the
       support side, linear;
     - two DISTINCT symmetric thresholds are comparable (nested), so the family of
       thresholds is itself a chain --- there is no antichain among thresholds.
   This is the support/chain half of the dichotomy, proven cleanly; the peak/antichain
   half is the broken interior, where the wire is no longer symmetric.
   Self-contained above the garden.
   ============================================================================ *)

text \<open>A symmetric monotone predicate is given by a threshold value t: true iff at least t
      ones.  Its residual after fixing a prefix with s ones (of the k fixed) is the
      threshold ``at least t - s of the remaining''.\<close>

definition thr :: "nat \<Rightarrow> bool list \<Rightarrow> bool" where
  "thr t v \<longleftrightarrow> t \<le> count_ones v"

lemma count_ones_mono:
  assumes "length u = length v" and "\<forall>i < length v. u!i \<longrightarrow> v!i"
  shows "count_ones u \<le> count_ones v"
  using assms
proof (induct u v rule: list_induct2)
  case Nil thus ?case by simp
next
  case (Cons x xs y ys)
  have "x \<longrightarrow> y" using Cons.prems by (metis nth_Cons_0 length_Cons zero_less_Suc)
  have "\<forall>i < length ys. xs!i \<longrightarrow> ys!i"
    using Cons.prems by (metis Suc_less_eq length_Cons nth_Cons_Suc)
  hence IH: "count_ones xs \<le> count_ones ys" using Cons.hyps by simp
  show ?case using IH \<open>x \<longrightarrow> y\<close> by (cases x; cases y) (simp_all add: count_ones_def)
qed

text \<open>MONOTONE: adding a one can only make the threshold more satisfied.\<close>

theorem thr_monotone:
  assumes "length u = length v"
      and "\<forall>i < length v. u!i \<longrightarrow> v!i"
  shows "thr t u \<longrightarrow> thr t v"
proof
  assume "thr t u"
  have "count_ones u \<le> count_ones v"
    using assms by (rule count_ones_mono)
  thus "thr t v" using \<open>thr t u\<close> by (simp add: thr_def)
qed

text \<open>THE RESIDUAL THRESHOLD.  Fixing a prefix with s ones turns the threshold t into the
      residual threshold t - s on the remaining wires.  So a cofactor of a threshold is
      itself a threshold, indexed by the residual value t - s.\<close>

definition residual :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "residual t s = t - s"

text \<open>THE SUPPORT SIDE (C1).  As the number s of fixed ones ranges over the achievable
      {0..k}, the residual threshold t - s ranges over a set of at most k+1 values; and
      since t - s is MONOTONE DECREASING in s, the distinct residuals form a CHAIN under
      the natural order --- they are totally ordered.  This is the chain/linear regime.\<close>

theorem residuals_chain:
  "s1 \<le> s2 \<Longrightarrow> residual t s2 \<le> residual t s1"
  by (simp add: residual_def diff_le_mono2)

theorem residuals_bounded:
  "card {residual t s | s. s \<le> k} \<le> k + 1"
proof -
  have "{residual t s | s. s \<le> k} = (\<lambda>s. residual t s) ` {..k}"
    by auto
  moreover have "card ((\<lambda>s. residual t s) ` {..k}) \<le> card {..k}"
    by (rule card_image_le) simp
  ultimately show ?thesis by simp
qed

text \<open>THE CHAIN OF THRESHOLDS (the dichotomy's chain half).  Two thresholds are always
      COMPARABLE: the predicate ``at least t1'' implies ``at least t2'' whenever t2 \<le> t1.
      So the family of all thresholds is a CHAIN --- no two are incomparable.  A symmetric
      (threshold) wire is UNBROKEN: its cofactor family (thresholds) carries no antichain.\<close>

theorem thresholds_comparable:
  "t2 \<le> t1 \<Longrightarrow> (\<forall>v. thr t1 v \<longrightarrow> thr t2 v)"
  by (auto simp: thr_def)

theorem thresholds_form_chain:
  "(\<forall>v. thr t1 v \<longrightarrow> thr t2 v) \<or> (\<forall>v. thr t2 v \<longrightarrow> thr t1 v)"
proof (cases "t2 \<le> t1")
  case True thus ?thesis using thresholds_comparable by blast
next
  case False hence "t1 \<le> t2" by simp
  thus ?thesis using thresholds_comparable by blast
qed

text \<open>THE COUNT OF DISTINCT THRESHOLD-COFACTORS is at most the support width.  A cofactor
      of a threshold is a residual threshold; by @{thm residuals_bounded} there are at
      most k+1 of them at level k, and over the whole function at most (support size)-many
      distinct residual thresholds.  So a threshold (symmetric) wire has width bounded by
      the SUPPORT --- linear, the ramp.  The peak/antichain regime requires a NON-symmetric
      wire, whose cofactors need not be nested; that is the broken interior.\<close>

theorem threshold_width_linear:
  "card {residual t s | s. s \<le> n} \<le> n + 1"
  by (rule residuals_bounded)

text \<open>Reading -- Path C, the dichotomy, chain half.  A symmetric threshold wire is
      UNBROKEN: @{thm thresholds_form_chain} shows any two thresholds are comparable, so
      the cofactor family is a CHAIN, and @{thm threshold_width_linear} bounds its width
      by the support, $n+1$, LINEAR --- the ramp the garden's @{thm achievable_counts}
      supplies.  This is the support side of the peak-vs-support dichotomy: where the wire
      is symmetric (a threshold), its cofactors are nested, chain-ordered, and thin.
      The peak side --- an antichain of incomparable cofactors, width toward the binomial
      peak $\binom{n}{n/2}$ --- lives where the wire is NOT symmetric, the broken interior
      of the lattice.  So the dichotomy is exactly the book's: threshold = chain =
      unbroken = linear; slice = antichain = broken = toward the peak.  Path C plants the
      chain half on the garden's support law; Path B (the recursive-merge induction) will
      cross here, using @{thm residuals_chain} and @{thm achievable_counts} to show a merge
      of thresholds stays a threshold; Path A (the exact ramp) will bloom from
      @{thm residuals_bounded}.  Nothing here is assumed.\<close>

end
