(* Closing gap (1): connect the concrete potential to strict_progress_closed,
   discharging progress_drops for the REAL reachable-image semantics.
   EXPERIMENT theory (non-destructive) — imports both halves and attempts the bridge.
   Iyun, 2026-07-29.

   The two facts the image_progress locale needs, for concrete potential:
     (A) pot_bound:      potential n S <= n*n            [have: potential_le_binom + card_pairs_below_le]
     (B) progress_drops: img_step c S <> S =>
                         potential n (img_step c S) < potential n S
                         [need: dual of strict_progress_closed, via settled/unsettled complement]

   SUBTLETY: ProgressBound's unsettled_pairs uses pairs_below = {i<j<n} (ONE direction);
   SettledConservation's settled_set uses {i<n,j<n,i<>j} (BOTH directions). We must reconcile
   the counting. And strict_progress_closed needs S = reach net & ascending net (not just abstract).
*)
theory ProgressClosed
  imports ProgressBound SettledConservation
begin

text \<open>pot_bound for the concrete potential (composing the existing lemmas).\<close>
lemma concrete_pot_bound: "potential n S \<le> n * n"
  using potential_le_binom[of n S] card_pairs_below_le[of n] by linarith

text \<open>Bridge attempt: does a non-idempotent comparator strictly DECREASE the potential
  (unsettled-pair count)?  This is the concrete progress_drops.  We try to derive it from
  strict_progress_closed (settled_set INCREASES) via the complement, under the reach/ascending
  hypotheses strict_progress_closed requires.\<close>

text \<open>First, the complement relationship between potential (unsettled, i<j) and settled_set
  (both directions).  We need: potential n S = card(pairs_below n) - card(settled-among-pairs_below).\<close>

lemma unsettled_is_complement:
  "unsettled_pairs n S = pairs_below n - {(i,j) \<in> pairs_below n. settled S i j}"
  by (auto simp: unsettled_pairs_def)

text \<open>The i<j-restricted settled pairs (ProgressBound's grain).\<close>
definition settled_lt :: "(nat \<Rightarrow> bool) set \<Rightarrow> nat \<Rightarrow> (nat \<times> nat) set" where
  "settled_lt S n = {(i,j) \<in> pairs_below n. settled S i j}"

lemma potential_via_settled_lt:
  "potential n S = card (pairs_below n) - card (settled_lt S n)"
proof -
  have "unsettled_pairs n S = pairs_below n - settled_lt S n"
    by (auto simp: unsettled_pairs_def settled_lt_def)
  moreover have "settled_lt S n \<subseteq> pairs_below n" by (auto simp: settled_lt_def)
  ultimately show ?thesis
    unfolding potential_def
    by (simp add: card_Diff_subset[OF finite_subset[OF _ finite_pairs_below]] finite_pairs_below)
qed


text \<open>CLEANER CLOSURE (2026-07-29): define the potential directly over settled_set (both
  directions), the same object strict_progress_closed speaks about, to avoid the one-direction
  vs both-direction mismatch.  Then progress_drops is immediate.\<close>

definition all_pairs :: "nat \<Rightarrow> (nat \<times> nat) set" where
  "all_pairs n = {(i,j). i < n \<and> j < n \<and> i \<noteq> j}"

lemma finite_all_pairs: "finite (all_pairs n)"
proof -
  have "all_pairs n \<subseteq> {0..<n} \<times> {0..<n}" by (auto simp: all_pairs_def)
  thus ?thesis by (rule finite_subset) auto
qed

lemma settled_set_subset_all: "settled_set n S \<subseteq> all_pairs n"
  by (auto simp: settled_set_def all_pairs_def)

definition potential2 :: "nat \<Rightarrow> (nat \<Rightarrow> bool) set \<Rightarrow> nat" where
  "potential2 n S = card (all_pairs n) - card (settled_set n S)"

text \<open>pot_bound for potential2: bounded by card(all_pairs n) = n(n-1) <= n*n.\<close>
lemma card_all_pairs_le: "card (all_pairs n) \<le> n * n"
proof -
  have "all_pairs n \<subseteq> {0..<n} \<times> {0..<n}" by (auto simp: all_pairs_def)
  hence "card (all_pairs n) \<le> card ({0..<n} \<times> {0..<n})" by (intro card_mono) auto
  thus ?thesis by simp
qed

lemma potential2_bound: "potential2 n S \<le> n * n"
  unfolding potential2_def using card_all_pairs_le[of n] by linarith

text \<open>progress_drops for potential2: IMMEDIATE from strict_progress_closed.\<close>
theorem potential2_drops:
  fixes S :: "(nat \<Rightarrow> bool) set"
  assumes c: "c = (a,b)" and ab: "a < b" and bn: "b < n"
      and nonidem: "img_step c S \<noteq> S"
      and Sdef: "S = reach net" and asc: "ascending net"
      and fin: "finite (settled_set n S)"
  shows "potential2 n (img_step c S) < potential2 n S"
proof -
  have strict: "card (settled_set n S) < card (settled_set n (img_step c S))"
    by (rule strict_progress_closed[OF c ab bn nonidem Sdef asc fin])
  have le1: "card (settled_set n S) \<le> card (all_pairs n)"
    by (rule card_mono[OF finite_all_pairs settled_set_subset_all])
  have le2: "card (settled_set n (img_step c S)) \<le> card (all_pairs n)"
    by (rule card_mono[OF finite_all_pairs settled_set_subset_all])
  show ?thesis unfolding potential2_def using strict le1 le2 by linarith
qed


section \<open>Full length bound on the real reachable-image run\<close>

text \<open>"effective net": along the run, every comparator changes the reachable image (no
  prefix-idempotent comparator), it is ascending, and its wires are in range [0,n).
  This is the well-formed class over which the polynomial bound holds.\<close>
definition wires_below :: "network \<Rightarrow> nat \<Rightarrow> bool" where
  "wires_below net n = (\<forall>c \<in> set net. fst c < snd c \<and> snd c < n)"

text \<open>effective_run: built by snoc — each appended comparator is non-idempotent on the
  image produced by the prefix.\<close>
definition effective_at :: "network \<Rightarrow> nat \<Rightarrow> bool" where
  "effective_at net k =
     (img_step (net ! k) (reach (take k net) :: (nat\<Rightarrow>bool) set) \<noteq> reach (take k net))"
definition effective_run :: "network \<Rightarrow> bool" where
  "effective_run net = (\<forall>k < length net. effective_at net k)"

text \<open>Each effective (non-idempotent, ascending, in-range) comparator strictly drops
  potential2 of the reachable image. Assembled from potential2_drops + reach_snoc.\<close>
lemma potential2_step_drop:
  fixes net :: network
  assumes ne: "img_step c (reach net :: (nat\<Rightarrow>bool) set) \<noteq> reach net"
      and c: "c = (a,b)" and ab: "a < b" and bn: "b < n"
      and asc: "ascending (net @ [c])"
      and fin: "finite (settled_set n (reach net :: (nat\<Rightarrow>bool) set))"
  shows "potential2 n (reach (net @ [c]) :: (nat\<Rightarrow>bool) set)
         < potential2 n (reach net :: (nat\<Rightarrow>bool) set)"
proof -
  have asc_net: "ascending net" using asc by (simp add: ascending_def)
  have "potential2 n (img_step c (reach net) :: (nat\<Rightarrow>bool) set)
        < potential2 n (reach net :: (nat\<Rightarrow>bool) set)"
    by (rule potential2_drops[OF c ab bn ne refl asc_net fin])
  thus ?thesis by (simp add: reach_snoc)
qed

text \<open>Finiteness of settled_set (settled_set n S subseteq all_pairs n, which is finite).\<close>
lemma finite_settled_set: "finite (settled_set n (S :: (nat\<Rightarrow>bool) set))"
  by (rule finite_subset[OF settled_set_subset_all finite_all_pairs])

text \<open>The length bound: an effective, ascending, in-range network has
  length <= potential2 of the initial (empty-prefix) image, hence <= n*n.
  Proof by snoc induction: the last comparator drops potential2 by at least 1.\<close>
lemma length_le_potential_drop:
  fixes net :: network
  assumes "effective_run net" and "ascending net" and "wires_below net n"
  shows "length net + potential2 n (reach net :: (nat\<Rightarrow>bool) set)
         \<le> potential2 n (reach [] :: (nat\<Rightarrow>bool) set)"
  using assms
proof (induct net rule: rev_induct)
  case Nil
  show ?case by simp
next
  case (snoc c net)
  have er_net: "effective_run net"
    unfolding effective_run_def effective_at_def
  proof (intro allI impI)
    fix k assume k: "k < length net"
    have "img_step ((net @ [c]) ! k) (reach (take k (net @ [c])) :: (nat\<Rightarrow>bool) set)
          \<noteq> reach (take k (net @ [c]))"
      using snoc.prems(1) k
      by (simp add: effective_run_def effective_at_def)
    thus "img_step (net ! k) (reach (take k net) :: (nat\<Rightarrow>bool) set) \<noteq> reach (take k net)"
      using k by (simp add: nth_append take_append)
  qed
  have asc_net: "ascending net" using snoc.prems(2) by (simp add: ascending_def)
  have wb_net: "wires_below net n" using snoc.prems(3) by (simp add: wires_below_def)
  obtain a b where c: "c = (a,b)" by (cases c)
  have ab: "a < b" and bn: "b < n"
    using snoc.prems(3) c by (auto simp: wires_below_def)
  \<comment> \<open>the last comparator is effective on reach net\<close>
  have ne: "img_step c (reach net :: (nat\<Rightarrow>bool) set) \<noteq> reach net"
  proof -
    have er: "effective_at (net @ [c]) (length net)"
      using snoc.prems(1) unfolding effective_run_def by simp
    thus ?thesis
      unfolding effective_at_def by (simp add: nth_append)
  qed
  have drop: "potential2 n (reach (net @ [c]) :: (nat\<Rightarrow>bool) set)
              < potential2 n (reach net :: (nat\<Rightarrow>bool) set)"
    by (rule potential2_step_drop[OF ne c ab bn snoc.prems(2) finite_settled_set])
  have IH: "length net + potential2 n (reach net :: (nat\<Rightarrow>bool) set)
            \<le> potential2 n (reach [] :: (nat\<Rightarrow>bool) set)"
    by (rule snoc.hyps[OF er_net asc_net wb_net])
  show ?case using drop IH by simp
qed

text \<open>THE POLYNOMIAL LENGTH BOUND on the real reachable-image run — no locale assumptions.\<close>
theorem effective_length_bound:
  fixes net :: network
  assumes "effective_run net" and "ascending net" and "wires_below net n"
  shows "length net \<le> n * n"
proof -
  have "length net + potential2 n (reach net :: (nat\<Rightarrow>bool) set)
        \<le> potential2 n (reach [] :: (nat\<Rightarrow>bool) set)"
    by (rule length_le_potential_drop[OF assms])
  hence "length net \<le> potential2 n (reach [] :: (nat\<Rightarrow>bool) set)" by simp
  also have "\<dots> \<le> n * n" by (rule potential2_bound)
  finally show ?thesis .
qed

end
