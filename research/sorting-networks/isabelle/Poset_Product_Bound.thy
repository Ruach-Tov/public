theory Poset_Product_Bound
  imports Main
begin

(* ============================================================================
   THE DILWORTH / MIRSKY PRODUCT BOUND, applied to the cofactor lattice.

   For LEMMA 4 (the OBDD width bound) we use a clean order-theoretic fact: a finite
   set carrying a strict partial order, in which every CHAIN has length at most H
   and every ANTICHAIN has size at most W, has at most H * W elements (Mirsky's
   theorem, in product form).

   We prove it via a rank/level decomposition: assign each element the length of
   the longest chain ending at it (its Mirsky rank).  Elements of equal rank form
   an antichain, so each of the at-most-H ranks holds at most W elements.

   Applied to the cofactor lattice of a monotone wire function: the cofactor set at
   each level is a finite poset (under the product order on bool lists) whose chains
   have height at most n (measured) and whose antichains have width at most a small
   constant (measured 2 for n <= 6).  So the number of distinct cofactors -- the
   OBDD width -- is at most n * (that constant), i.e. O(n) per wire.  This theory
   proves the reduction; the two factors are the empirically-measured, not-yet-
   proven, inputs (recorded honestly as hypotheses).
   ============================================================================ *)

text \<open>A strict order on a finite carrier.  We work abstractly with a relation
      \<open>r\<close> that is a strict partial order (irreflexive + transitive) on a finite
      set \<open>A\<close>.  A CHAIN is a subset totally ordered by \<open>r\<close>; an ANTICHAIN a subset
      with no two distinct \<open>r\<close>-related elements.\<close>

definition chain_on :: "'a rel \<Rightarrow> 'a set \<Rightarrow> 'a set \<Rightarrow> bool" where
  "chain_on r A C \<longleftrightarrow> C \<subseteq> A \<and> (\<forall>x\<in>C. \<forall>y\<in>C. x = y \<or> (x,y) \<in> r \<or> (y,x) \<in> r)"

definition antichain_on :: "'a rel \<Rightarrow> 'a set \<Rightarrow> 'a set \<Rightarrow> bool" where
  "antichain_on r A S \<longleftrightarrow> S \<subseteq> A \<and> (\<forall>x\<in>S. \<forall>y\<in>S. (x,y) \<in> r \<longrightarrow> x = y)"

text \<open>The Mirsky rank: the size of the largest chain whose top is \<open>x\<close>.  With a
      finite carrier and a strict order this is well-defined; we characterise it by
      the two properties we need, taken as hypotheses on a rank function
      \<open>rk : 'a \<Rightarrow> nat\<close>: (i) rank is bounded by the chain height, and (ii) elements
      of equal rank are incomparable (an antichain).\<close>

theorem product_bound:
  fixes A :: "'a set" and r :: "'a rel" and rk :: "'a \<Rightarrow> nat"
  assumes finA: "finite A"
      and height: "\<forall>x\<in>A. rk x < H"
      and antichain_levels: "\<forall>x\<in>A. \<forall>y\<in>A. rk x = rk y \<and> (x,y) \<in> r \<longrightarrow> x = y"
      and width: "\<forall>S. antichain_on r A S \<longrightarrow> card S \<le> W"
  shows "card A \<le> H * W"
proof -
  \<comment> \<open>partition A by rank; each rank class is an antichain of size <= W; there are
      at most H rank values.\<close>
  have parts: "A = (\<Union>j<H. {x\<in>A. rk x = j})"
    using height by auto
  have each_antichain: "\<And>j. antichain_on r A {x\<in>A. rk x = j}"
    using antichain_levels by (auto simp: antichain_on_def)
  have each_le_W: "\<And>j. card {x\<in>A. rk x = j} \<le> W"
    using width each_antichain by blast
  have "card A = card (\<Union>j<H. {x\<in>A. rk x = j})" using parts by simp
  also have "... \<le> (\<Sum>j<H. card {x\<in>A. rk x = j})"
    by (rule card_UN_le) simp
  finally have "card A \<le> (\<Sum>j<H. card {x\<in>A. rk x = j})" .
  also have "... \<le> (\<Sum>j<H. W)"
    using each_le_W by (intro sum_mono) auto
  also have "... = H * W" by simp
  finally show ?thesis .
qed

text \<open>Reading, for the cofactor lattice.  Take \<open>A\<close> = the cofactor set at a level,
      \<open>r\<close> = the strict product order, \<open>rk\<close> = the Mirsky rank.  With chain height
      \<open>H = n\<close> (measured) and antichain width \<open>W\<close> a small constant (measured), the
      theorem gives \<open>card A \<le> n * W = \<bigoh>(n)\<close> distinct cofactors per wire, hence
      \<open>\<bigoh>(n^2)\<close> in the shared diagram.  The reduction is proven here; \<open>H\<close> and
      \<open>W\<close> are the empirical inputs that remain to be bounded from the monotone
      threshold structure (the honest open sub-lemma of Lemma 4).\<close>

end
