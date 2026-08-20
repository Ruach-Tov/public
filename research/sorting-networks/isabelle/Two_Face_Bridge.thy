theory Two_Face_Bridge
  imports Main
begin

(* ============================================================================
   THE TWO FACES OF THE DOOR: the backward shuffler bounds the forward defect.

   The width bound funnelled to the forward defect W_0 -- the antichain of the
   Demazure-reachable partial-sort states.  The backward reading of the same network
   is a shuffler over the Bruhat order, and it COMPUTES that reachable set.  This
   theory forges the bridge between the two faces, honestly:

     - an antichain is a subset, so W_0 is at most the SIZE of the reachable set;
     - the reachable-state poset is RANKED by Coxeter length -- each comparator fixes
       the length or raises it by one -- so its size is the sum, over lengths, of the
       number of reachable states of that length;
     - hence W_0 is at most that sum, and the door reduces to a COUNTING question the
       backward shuffler addresses: is the reachable Demazure orbit polynomial-sized?

   The move from ``bound the antichain'' to ``bound the reachable set'' is the bridge:
   the forward defect is bounded by the backward reachable count.  We prove the clean,
   correct facts -- antichain-at-most-total, and the rank decomposition -- and locate
   the reachable-set size as the sharpened, shuffler-facing target.

   Abstract: a finite set A (the reachable states) with a strict order r and a rank
   function len into the naturals.  Self-contained (imports Main).
   ============================================================================ *)

definition is_antichain :: "'a set \<Rightarrow> 'a rel \<Rightarrow> 'a set \<Rightarrow> bool" where
  "is_antichain A r S \<longleftrightarrow> S \<subseteq> A \<and> (\<forall>x\<in>S. \<forall>y\<in>S. (x,y)\<in>r \<longrightarrow> x = y)"

text \<open>THE HONEST BRIDGE.  An antichain is a subset of the carrier, so its size is at
      most the size of the whole reachable set.  Hence the defect W_0 -- the largest
      antichain -- is at most the number of reachable states.  Trivial, and exactly the
      reduction we want: the forward antichain is bounded by the backward reachable
      count.\<close>

theorem antichain_le_total:
  assumes "finite A" and "is_antichain A r S"
  shows "card S \<le> card A"
proof -
  have "S \<subseteq> A" using assms(2) by (simp add: is_antichain_def)
  thus ?thesis by (rule card_mono[OF assms(1)])
qed

text \<open>THE RANK DECOMPOSITION.  Give each reachable state a length len (its Coxeter
      length, the inversion count).  The reachable set is the disjoint union of its
      length-levels, so its size is the sum of the level sizes.  This is the backward,
      factoradic view: the reachable set counted by length.\<close>

definition level :: "'a set \<Rightarrow> ('a \<Rightarrow> nat) \<Rightarrow> nat \<Rightarrow> 'a set" where
  "level A len L = {x \<in> A. len x = L}"

theorem reachable_size_is_level_sum:
  assumes fin: "finite A" and bound: "\<forall>x\<in>A. len x \<le> N"
  shows "card A = (\<Sum>L\<le>N. card (level A len L))"
proof -
  have part: "A = (\<Union>L\<le>N. level A len L)"
    using bound by (auto simp: level_def)
  have disj: "\<And>L L'. L \<noteq> L' \<Longrightarrow> level A len L \<inter> level A len L' = {}"
    by (auto simp: level_def)
  have finlev: "\<And>L. finite (level A len L)" using fin by (simp add: level_def)
  have "card A = card (\<Union>L\<le>N. level A len L)" using part by simp
  also have "... = (\<Sum>L\<le>N. card (level A len L))"
    by (rule card_UN_disjoint) (auto simp: finlev disj)
  finally show ?thesis .
qed

text \<open>THE BRIDGE, ASSEMBLED.  The defect W_0 (any antichain of the reachable set) is at
      most the sum over lengths of the level sizes.  So a polynomial bound on the
      reachable set -- polynomially many lengths, each with polynomially many states --
      gives a polynomial defect, hence a polynomial width, hence a polynomial verifier.
      The forward door is bounded by the backward count.\<close>

theorem defect_le_level_sum:
  assumes fin: "finite A" and bound: "\<forall>x\<in>A. len x \<le> N"
      and anti: "is_antichain A r S"
  shows "card S \<le> (\<Sum>L\<le>N. card (level A len L))"
proof -
  have "card S \<le> card A" using antichain_le_total[OF fin anti] .
  also have "card A = (\<Sum>L\<le>N. card (level A len L))"
    by (rule reachable_size_is_level_sum[OF fin bound])
  finally show ?thesis .
qed

text \<open>Reading.  This is the bridge between the two faces of the one Coxeter object.
      @{thm antichain_le_total}: the forward defect $W_0$ is at most the size of the
      reachable set -- an antichain is a subset.  @{thm reachable_size_is_level_sum}:
      the reachable set, ranked by Coxeter length, is the sum of its length-levels --
      the backward, factoradic count.  @{thm defect_le_level_sum}: so $W_0$ is at most
      the sum over lengths of the reachable-state count at each length.  The door --
      bounding the forward antichain $W_0$ -- is thereby turned to face the backward
      shuffler: it suffices that the Demazure-reachable set have polynomially many
      states (polynomially many lengths, each a polynomial level).  The reachable count
      is what the shuffler computes; the forward defect is bounded by it.  What remains
      open is the same one door -- now a COUNTING of the reachable Demazure orbit, the
      quantity the backward face was built to address.  Nothing here is assumed.\<close>

end
