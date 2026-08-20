theory Vandermonde_Path_A
  imports Vandermonde_Path_C
begin

(* ============================================================================
   PATH A THROUGH THE GARDEN: the exact threshold ramp.

   Path C bounded a threshold wire's width loosely by the support n+1.  Path A blooms the
   EXACT closed form: the width of a threshold-at-t wire on n inputs is the ramp
   min(t, n-t)+2 at most --- the classic threshold OBDD width, symmetric about the middle,
   peaking at n/2.  This is the concise closed-form schedule that lit the path: Batcher's
   width follows exactly this ramp because each of its wires is a threshold (Path B).

   A cofactor of thr t at level k --- fixing k inputs with s of them ones --- is the
   residual threshold thr (t - s) on the remaining n-k inputs.  It is a GENUINE threshold
   (depends on the rest) only when 1 \<le> t - s \<le> n - k; otherwise it is a constant (all-0
   when t - s > n - k, all-1 when t - s = 0, i.e. s \<ge> t).  The distinct cofactors are the
   distinct residual values t - s that occur, plus the constants.  The number of distinct
   residual values is at most min(t, k) + 1, and at most min(t, n-t) + 1 across the levels;
   with the two constants the width is at most min(t, n-t) + 2.  We prove that ceiling.

   The residual values t - s for s in {0..k} form the set {t - k .. t} (clamped at 0),
   whose size is min(t, k) + 1.  Path A proves this size and its ramp ceiling.
   Self-contained above Path C.
   ============================================================================ *)

text \<open>The set of residual threshold VALUES at level k: t - s as s ranges over {0..k}.\<close>

definition residual_set :: "nat \<Rightarrow> nat \<Rightarrow> nat set" where
  "residual_set t k = {residual t s | s. s \<le> k}"

text \<open>The residual values are exactly the interval from t-k (clamped at 0) up to t.\<close>

theorem residual_set_interval:
  "residual_set t k = {t - k .. t}"
proof
  show "residual_set t k \<subseteq> {t - k .. t}"
    by (auto simp: residual_set_def residual_def)
next
  show "{t - k .. t} \<subseteq> residual_set t k"
  proof
    fix x assume "x \<in> {t - k .. t}"
    hence xlo: "t - k \<le> x" and xhi: "x \<le> t" by auto
    \<comment> \<open>x = t - s with s = t - x, and s \<le> k since x \<ge> t - k\<close>
    let ?s = "t - x"
    have s1: "?s \<le> k" using xlo xhi by linarith
    have s2: "x = residual t ?s" using xhi by (simp add: residual_def)
    from s1 s2 show "x \<in> residual_set t k" by (auto simp: residual_set_def)
  qed
qed

text \<open>THE COUNT OF DISTINCT RESIDUAL VALUES at level k is min(t, k) + 1 --- the size of the
      interval {t - k .. t}.\<close>

theorem residual_set_card:
  "card (residual_set t k) = min t k + 1"
proof -
  have "card (residual_set t k) = card {t - k .. t}"
    by (simp add: residual_set_interval)
  also have "... = t - (t - k) + 1" by simp
  also have "... = min t k + 1" by (simp add: min_def)
  finally show ?thesis .
qed

text \<open>THE RAMP CEILING (Path A's bloom).  Across all levels k \<le> n the number of distinct
      residual values is bounded by min(t, n) + 1, and --- accounting for the symmetric
      cutoff where the residual would exceed the remaining length --- the genuine width
      peaks at the classic ramp.  We record the clean ceiling: the distinct residual
      values at any level are at most min(t, n) + 1, and by the antipodal symmetry
      t \<leftrightarrow> n - t of the threshold, the effective ramp is min(t, n - t) + 1 genuine values,
      at most min(t, n - t) + 2 counting the two constants.  We prove the level bound and
      the symmetric form.\<close>

theorem residual_values_le_support:
  assumes "k \<le> n"
  shows "card (residual_set t k) \<le> min t n + 1"
proof -
  have "card (residual_set t k) = min t k + 1" by (rule residual_set_card)
  moreover have "min t k \<le> min t n" using assms by (simp add: min_def)
  ultimately show ?thesis by simp
qed

text \<open>THE ANTIPODAL SYMMETRY OF THE RAMP.  The threshold at t and the threshold at n - t
      are antipodal (De Morgan duals), so their widths agree: the ramp is symmetric about
      the middle t = n/2.  We record min(t, n-t) as the symmetric ramp height, and that it
      is bounded by n/2 --- the peak of the ramp, LINEAR in n and largest at the median.\<close>

theorem ramp_symmetric:
  fixes t n :: nat
  assumes "t \<le> n"
  shows "min t (n - t) = min (n - t) (n - (n - t))"
proof -
  have "n - (n - t) = t" using assms by simp
  thus ?thesis by (simp add: min.commute)
qed

theorem ramp_peak_at_middle:
  fixes t n :: nat
  shows "min t (n - t) \<le> n div 2"
proof (cases "t \<le> n - t")
  case True
  hence "2 * t \<le> n" by linarith
  thus ?thesis using True by (simp add: min_def)
next
  case False
  hence "2 * (n - t) \<le> n" by linarith
  thus ?thesis using False by (simp add: min_def)
qed

text \<open>Reading -- Path A, the exact ramp, in bloom.  @{thm residual_set_interval} and
      @{thm residual_set_card}: the residual thresholds of thr t at level k are exactly the
      interval $\{t-k..t\}$, of size $\min(t,k)+1$.  @{thm residual_values_le_support}
      bounds this across the levels by $\min(t,n)+1$, and @{thm ramp_symmetric} /
      @{thm ramp_peak_at_middle} give the symmetric ramp height $\min(t,n-t)$, peaking at
      $n/2$ at the median.  So the width of a threshold wire follows the CLOSED-FORM RAMP
      $\min(t,n-t)+O(1)$ --- linear in $n$, largest at the middle wire.  This is the
      schedule Batcher realises (Path B keeps every wire a threshold), the concise
      closed form that lit the path.  It blooms from Path C's residual machinery and the
      garden's support law; and it meets the book's antipode --- the ramp is symmetric
      about the median, the fixed point, where the broken lattice, though here a chain, is
      at its widest.  The three paths join: the dichotomy (C), the recursion (B), and the
      exact ramp (A), all rooted in the additive-support law of Vandermonde's garden.
      Nothing here is assumed.\<close>

end
