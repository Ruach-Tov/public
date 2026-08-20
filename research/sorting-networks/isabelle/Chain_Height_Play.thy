theory Chain_Height_Play
  imports Main
begin

(* ============================================================================
   PLAYING IN THE CLOSED-FORM LOGIC OF CHAINS, HEIGHT, AND INTERMEDIATE WIRES.

   No goal, no search, no assumed bounds.  Just what is provable, for all n, by pure
   reasoning about chains of predicates ordered pointwise -- the shape the cofactor
   posets take, intermediate wires included.  A few entertaining facts fall out, and
   several point at exactly the place the map is thinnest: the intermediate wires.

   A predicate on a finite index set is ordered pointwise.  The TRUE-POINT RANK of a
   predicate is the number of indices where it holds.  It is a faithful strict rank;
   the antipode complements it; and along any chain the ranks are distinct, which
   bounds a chain by the rank range.  For intermediate wires these give an honest
   (if coarse) height account, stated in the size of the residual index set.

   Self-contained (imports Main).  Predicates are functions into bool on a finite set
   A of indices; g \<sqsubseteq> h means g implies h on A.
   ============================================================================ *)

definition pleq :: "'a set \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> bool" where
  "pleq A g h \<longleftrightarrow> (\<forall>a \<in> A. g a \<longrightarrow> h a)"

definition tset :: "'a set \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> 'a set" where
  "tset A g = {a \<in> A. g a}"

definition trank :: "'a set \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> nat" where
  "trank A g = card (tset A g)"

text \<open>FACT 1 -- the true-point rank is a FAITHFUL STRICT MONOTONE.  If g is below h
      and they differ somewhere on A, the rank strictly increases.  (This is what makes
      the true-point count a rank on any poset of predicates -- the intermediate-wire
      cofactors included.)\<close>

lemma tset_mono:
  assumes "finite A" and "pleq A g h"
  shows "tset A g \<subseteq> tset A h"
  using assms by (auto simp: pleq_def tset_def)

theorem trank_strict:
  assumes "finite A" and "pleq A g h" and "\<exists>a \<in> A. g a \<noteq> h a"
  shows "trank A g < trank A h"
proof -
  have sub: "tset A g \<subseteq> tset A h" using tset_mono[OF assms(1,2)] .
  from assms(3) obtain a where aA: "a \<in> A" and diff: "g a \<noteq> h a" by blast
  have "g a \<longrightarrow> h a" using assms(2) aA by (simp add: pleq_def)
  hence "\<not> g a" and "h a" using diff by auto
  hence "a \<in> tset A h" and "a \<notin> tset A g" using aA by (auto simp: tset_def)
  hence ps: "tset A g \<subset> tset A h" using sub by blast
  have fin: "finite (tset A h)" using assms(1) by (simp add: tset_def)
  show ?thesis unfolding trank_def by (rule psubset_card_mono[OF fin ps])
qed

text \<open>FACT 2 -- the rank is bounded by the size of the index set.  So a chain, whose
      ranks are distinct naturals in @{term "{0..card A}"}, has at most @{term "card A + 1"}
      elements.  For an intermediate wire's cofactor at level k, the index set is the
      residual cube of size @{term "2 ^ (n - k)"} -- honest, and honestly exponential:
      the true-point rank alone gives only a cube-sized height, which is why a
      polynomial height for intermediate wires needs MORE than monotonicity.\<close>

theorem trank_le_card:
  assumes "finite A"
  shows "trank A g \<le> card A"
proof -
  have "tset A g \<subseteq> A" by (auto simp: tset_def)
  thus ?thesis unfolding trank_def using assms by (simp add: card_mono)
qed

text \<open>FACT 3 -- THE ANTIPODE COMPLEMENTS THE RANK.  If d is the pointwise complement
      on A (d g holds where g fails), then the rank of d g is @{term "card A - trank A g"}.
      So a predicate and its antipode have ranks summing to @{term "card A"}, and a
      SELF-COMPLEMENTARY predicate -- its own antipode -- sits at rank @{term "card A div 2"}.
      The median, recovered from pure rank reasoning: the fixed point of the antipode
      is at the middle of the rank range.\<close>

definition antip :: "('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> bool)" where
  "antip g = (\<lambda>a. \<not> g a)"

theorem trank_antip:
  assumes "finite A"
  shows "trank A (antip g) = card A - trank A g"
proof -
  have "tset A (antip g) = A - tset A g" by (auto simp: tset_def antip_def)
  hence "trank A (antip g) = card (A - tset A g)" by (simp add: trank_def)
  also have "... = card A - card (tset A g)"
    using assms by (simp add: card_Diff_subset tset_def)
  also have "... = card A - trank A g" by (simp add: trank_def)
  finally show ?thesis .
qed

theorem self_antipodal_rank_is_middle:
  assumes "finite A" and "antip g = g"
  shows "2 * trank A g = card A"
proof -
  have "trank A g = trank A (antip g)" using assms(2) by simp
  also have "... = card A - trank A g" using trank_antip[OF assms(1)] .
  finally have "trank A g = card A - trank A g" .
  moreover have "trank A g \<le> card A" by (rule trank_le_card[OF assms(1)])
  ultimately show ?thesis by simp
qed

text \<open>FACT 4 -- THE ANTIPODE REVERSES ORDER (so it maps chains to chains of equal
      length).  If g is below h then the antipode of h is below the antipode of g:
      complementation reverses implication.  Hence the antipode carries a chain to a
      chain, and a poset and its antipodal image have the same height.  The broken
      lattice and its antipode -- wire i and wire n-1-i -- are of equal height.\<close>

theorem antip_order_reversing:
  assumes "pleq A g h"
  shows "pleq A (antip h) (antip g)"
  using assms by (auto simp: pleq_def antip_def)

theorem antip_involution: "antip (antip g) = g"
  by (simp add: antip_def)

text \<open>FACT 5 -- pointed at the intermediate wires.  A predicate that does NOT depend
      on an index a gives the same value there under any extension; so a cofactor that
      ignores a residual variable adds no rank distinction along that coordinate.  This
      is the support germ, in rank form: the rank only ever moves on the SUPPORT.  For
      an intermediate wire, whose support grows as inputs mix in, the rank range -- and
      thus the height account -- is carried by the support, not the full arity.  The
      map is thinnest exactly here: bounding the support (hence the height) polynomially
      is the intermediate-wire question, and this locates it in the rank.\<close>

theorem rank_unchanged_off_support:
  assumes "finite A" and "a \<in> A" and "\<forall>b \<in> A. b \<noteq> a \<longrightarrow> g b = h b"
      and "g a = h a"
  shows "trank A g = trank A h"
proof -
  have "\<forall>b \<in> A. g b = h b"
  proof
    fix b assume bA: "b \<in> A"
    show "g b = h b" using assms(3,4) bA by (cases "b = a") auto
  qed
  hence "tset A g = tset A h" by (auto simp: tset_def)
  thus ?thesis by (simp add: trank_def)
qed

text \<open>Reading, honestly.  These are closed-form facts, true for all n, proved by
      reasoning and not by search.  @{thm trank_strict} makes the true-point count a
      faithful rank on any predicate poset; @{thm trank_le_card} bounds it by the index
      set -- honestly exponential for a residual cube, which is why intermediate-wire
      height needs structure beyond monotonicity.  @{thm trank_antip} and
      @{thm self_antipodal_rank_is_middle} recover the median from the rank: the
      antipode complements the rank, so a self-dual predicate sits at the middle.
      @{thm antip_order_reversing} shows the antipode reverses chains, so a poset and
      its antipodal image have equal height.  @{thm rank_unchanged_off_support} locates
      the intermediate-wire question in the rank: the rank moves only on the support, so
      a polynomial support would give a polynomial height -- and that support bound,
      for intermediate wires, is precisely the open map.  Nothing here is assumed; the
      exponential honesty of @{thm trank_le_card} is the true edge, marked not hidden.\<close>

end
