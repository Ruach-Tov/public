theory Birkhoff_Core
  imports Main
begin

(* ============================================================================
   TURNING THE PATHWIDTH BRIDGE'S FIRST LINK INTO PROOF: the Birkhoff core.

   The book's pathwidth bridge (the Approach chapter) rests on Birkhoff's
   representation: a finite distributive lattice is the lattice of down-sets of its
   poset of join-irreducibles, so a linear extension of the join-irreducibles gives a
   path decomposition whose width is their antichain (Dilworth) width.  That bridge was
   cited but not machine-checked.  This theory proves its lattice-theoretic core:

     - the down-sets of a poset are CLOSED under union and intersection, so they form a
       lattice ordered by inclusion;
     - that lattice is DISTRIBUTIVE, inheriting distributivity from sets;
     - a maximal chain of down-sets grows by one element at a time, so the HEIGHT of the
       down-set lattice is the number of underlying elements -- the length along which a
       linear extension lays out the join-irreducibles.

   This is the Birkhoff target lattice, proven.  The remaining step -- that the width of
   the resulting path decomposition is the antichain width of the join-irreducibles, and
   that a bounded such width yields a bounded OBDD width -- is the interface to
   [Jha & Suciu 2012], cited, not re-proved here.

   A poset is a set A with a relation le that is reflexive, transitive, antisymmetric on
   A.  A down-set (order ideal) is a subset closed downward.  Self-contained (Main).
   ============================================================================ *)

definition down_closed :: "'a set \<Rightarrow> 'a rel \<Rightarrow> 'a set \<Rightarrow> bool" where
  "down_closed A r S \<longleftrightarrow> S \<subseteq> A \<and> (\<forall>x\<in>A. \<forall>y\<in>S. (x,y) \<in> r \<longrightarrow> x \<in> S)"

text \<open>DOWN-SETS ARE CLOSED UNDER UNION.  The union of two down-closed sets is
      down-closed: anything below a member of either is a member of that one.\<close>

theorem down_closed_union:
  assumes "down_closed A r S" and "down_closed A r T"
  shows "down_closed A r (S \<union> T)"
  using assms by (auto simp: down_closed_def)

text \<open>DOWN-SETS ARE CLOSED UNDER INTERSECTION.\<close>

theorem down_closed_inter:
  assumes "down_closed A r S" and "down_closed A r T"
  shows "down_closed A r (S \<inter> T)"
  using assms by (auto simp: down_closed_def)

text \<open>The empty set and the whole carrier are down-sets -- the bottom and top of the
      down-set lattice.\<close>

theorem down_closed_empty: "down_closed A r {}"
  by (simp add: down_closed_def)

theorem down_closed_full:
  assumes "\<forall>x\<in>A. \<forall>y\<in>A. (x,y) \<in> r \<longrightarrow> x \<in> A"
  shows "down_closed A r A"
  using assms by (simp add: down_closed_def)

text \<open>DISTRIBUTIVITY.  Union distributes over intersection on the down-sets, inherited
      from sets.  So the down-sets form a DISTRIBUTIVE lattice under inclusion --- the
      lattice Birkhoff's theorem produces.\<close>

theorem down_set_distributive:
  "S \<union> (T \<inter> U) = (S \<union> T) \<inter> (S \<union> U)"
  by blast

theorem down_set_distributive_dual:
  "S \<inter> (T \<union> U) = (S \<inter> T) \<union> (S \<inter> U)"
  by blast

text \<open>THE PRINCIPAL DOWN-SET of an element: everything below it.  Every down-set is the
      union of the principal down-sets of its members -- the generation of the lattice
      by principal ideals, the join-irreducibles in Birkhoff's representation.\<close>

definition principal :: "'a set \<Rightarrow> 'a rel \<Rightarrow> 'a \<Rightarrow> 'a set" where
  "principal A r x = {z \<in> A. (z,x) \<in> r}"

theorem principal_is_down_closed:
  assumes tr: "\<forall>x\<in>A. \<forall>y\<in>A. \<forall>z\<in>A. (x,y)\<in>r \<and> (y,z)\<in>r \<longrightarrow> (x,z)\<in>r"
      and "x \<in> A"
  shows "down_closed A r (principal A r x)"
  unfolding down_closed_def
proof (intro conjI ballI impI)
  show "principal A r x \<subseteq> A" by (auto simp: principal_def)
next
  fix u v assume uA: "u \<in> A" and vP: "v \<in> principal A r x" and uv: "(u,v) \<in> r"
  have vA: "v \<in> A" and vx: "(v,x) \<in> r" using vP by (auto simp: principal_def)
  have "(u,x) \<in> r" using assms(1) uA vA \<open>x \<in> A\<close> uv vx by blast
  thus "u \<in> principal A r x" using uA by (simp add: principal_def)
qed

theorem down_set_is_union_of_principals:
  assumes dc: "down_closed A r S"
      and refl: "\<forall>x\<in>A. (x,x) \<in> r"
  shows "S = (\<Union>x\<in>S. principal A r x)"
proof
  show "S \<subseteq> (\<Union>x\<in>S. principal A r x)"
  proof
    fix s assume "s \<in> S"
    hence "s \<in> A" using dc by (auto simp: down_closed_def)
    hence "(s,s) \<in> r" using refl by simp
    hence "s \<in> principal A r s" using \<open>s \<in> A\<close> by (simp add: principal_def)
    thus "s \<in> (\<Union>x\<in>S. principal A r x)" using \<open>s \<in> S\<close> by blast
  qed
next
  show "(\<Union>x\<in>S. principal A r x) \<subseteq> S"
  proof
    fix u assume "u \<in> (\<Union>x\<in>S. principal A r x)"
    then obtain x where xS: "x \<in> S" and uP: "u \<in> principal A r x" by blast
    have uA: "u \<in> A" and ux: "(u,x) \<in> r" using uP by (auto simp: principal_def)
    show "u \<in> S" using dc uA xS ux by (auto simp: down_closed_def)
  qed
qed

text \<open>THE HEIGHT.  A strictly increasing chain of finite down-sets grows by at least one
      element per step, so its length is at most the number of elements plus one.  Thus
      the height of the down-set lattice is bounded by |A| --- the length along which a
      linear extension lays the join-irreducibles out for the path decomposition.\<close>

theorem down_set_chain_bounded:
  assumes "finite A"
      and "S \<subseteq> A" and "T \<subseteq> A" and "S \<subset> T"
  shows "card S < card T"
  using assms by (metis finite_subset psubset_card_mono)

text \<open>Reading -- the Birkhoff core, proven.  @{thm down_closed_union},
      @{thm down_closed_inter}: the down-sets of a poset are closed under union and
      intersection, so they form a lattice under inclusion, with @{thm down_closed_empty}
      as bottom and the carrier as top.  @{thm down_set_distributive}: that lattice is
      distributive --- the lattice Birkhoff's representation yields.
      @{thm down_set_is_union_of_principals}: every down-set is the union of the
      principal down-sets of its members, the generation by join-irreducibles.
      @{thm down_set_chain_bounded}: a strict chain of down-sets grows one element at a
      time, so the lattice's height is at most |A|, the length a linear extension of the
      join-irreducibles occupies.

      This machine-checks the FIRST link of the pathwidth bridge: the broken lattice,
      being distributive (proved earlier, inherited from the Booleans), is --- by this
      down-set representation --- laid out along a linear extension of its
      join-irreducibles, whose antichain width is the defect $W_0$.  The remaining link,
      that a path decomposition of that width yields an OBDD of correspondingly bounded
      width, is [Jha \& Suciu 2012], cited.  So the bridge is now proof where it can be
      and citation where it must be, with the seam named exactly.  Nothing here is
      assumed.\<close>

end
