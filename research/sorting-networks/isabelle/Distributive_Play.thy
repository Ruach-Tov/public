theory Distributive_Play
  imports Main
begin

(* ============================================================================
   PLAYING AROUND DISTRIBUTIVITY -- drawing the map for proving the broken lattice's
   distributive structure.

   The pathwidth bridge (Birkhoff + Jha-Suciu) wants the cofactor poset to sit inside a
   DISTRIBUTIVE lattice.  Wandering the vicinity, the map clarifies: distributivity is
   INHERITED, for free, from the two-element Boolean algebra -- pointwise meet and join
   of Boolean-valued functions distribute because AND and OR distribute on {True,False}.
   So the whole function lattice is distributive, the monotone functions are a
   distributive sublattice, and any set of cofactors closed under pointwise meet/join is
   a distributive lattice.

   The REAL work is therefore NOT proving distributivity (it is inherited) but bounding
   the CLOSURE -- the meet/join-closure of the cofactor set, which "fills in" the defect
   points and un-breaks the broken lattice.  Its size is W_0's true home.  This theory
   proves the inherited distributivity (the easy, true part) and locates the closure as
   the frontier.

   Functions are 'a => bool ordered pointwise; meet = pointwise conjunction, join =
   pointwise disjunction.  Self-contained (imports Main).
   ============================================================================ *)

definition fmeet :: "('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> bool)" where
  "fmeet f g = (\<lambda>x. f x \<and> g x)"

definition fjoin :: "('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> bool)" where
  "fjoin f g = (\<lambda>x. f x \<or> g x)"

definition fle :: "('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> bool" where
  "fle f g \<longleftrightarrow> (\<forall>x. f x \<longrightarrow> g x)"

text \<open>FACT 1 -- DISTRIBUTIVITY IS INHERITED, POINTWISE.  Meet distributes over join
      (and dually) because conjunction distributes over disjunction on the Booleans.
      No structure of the functions is used; it is a property of {True, False}.\<close>

theorem fmeet_fjoin_distrib:
  "fmeet f (fjoin g h) = fjoin (fmeet f g) (fmeet f h)"
  by (rule ext) (auto simp: fmeet_def fjoin_def)

theorem fjoin_fmeet_distrib:
  "fjoin f (fmeet g h) = fmeet (fjoin f g) (fjoin f h)"
  by (rule ext) (auto simp: fmeet_def fjoin_def)

text \<open>Meet and join are the greatest lower / least upper bounds in the pointwise
      order -- so the function space is a lattice, and by the above a DISTRIBUTIVE one.\<close>

theorem fmeet_lb: "fle (fmeet f g) f \<and> fle (fmeet f g) g"
  by (auto simp: fle_def fmeet_def)

theorem fmeet_greatest: "fle h f \<Longrightarrow> fle h g \<Longrightarrow> fle h (fmeet f g)"
  by (auto simp: fle_def fmeet_def)

theorem fjoin_ub: "fle f (fjoin f g) \<and> fle g (fjoin f g)"
  by (auto simp: fle_def fjoin_def)

theorem fjoin_least: "fle f h \<Longrightarrow> fle g h \<Longrightarrow> fle (fjoin f g) h"
  by (auto simp: fle_def fjoin_def)

text \<open>FACT 2 -- MONOTONE FUNCTIONS ARE A SUBLATTICE.  If f and g are monotone with
      respect to some order @{term r} on the domain, so are their pointwise meet and
      join: conjunction and disjunction preserve monotonicity.  So the monotone
      functions are closed under meet and join, a distributive sublattice.\<close>

definition dmono :: "'a rel \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> bool" where
  "dmono r f \<longleftrightarrow> (\<forall>(x,y) \<in> r. f x \<longrightarrow> f y)"

theorem dmono_fmeet:
  assumes "dmono r f" and "dmono r g"
  shows "dmono r (fmeet f g)"
  using assms by (fastforce simp: dmono_def fmeet_def)

theorem dmono_fjoin:
  assumes "dmono r f" and "dmono r g"
  shows "dmono r (fjoin f g)"
  using assms by (fastforce simp: dmono_def fjoin_def)

text \<open>FACT 3 -- A SET CLOSED UNDER MEET AND JOIN IS A DISTRIBUTIVE LATTICE.  Any set S
      of functions closed under fmeet and fjoin inherits distributivity: the identities
      hold for all functions, so a fortiori for those in S.  This is the abstract
      content behind "the cofactor closure is a distributive lattice": distributivity
      is free once the set is meet/join-closed.\<close>

definition mj_closed :: "('a \<Rightarrow> bool) set \<Rightarrow> bool" where
  "mj_closed S \<longleftrightarrow> (\<forall>f \<in> S. \<forall>g \<in> S. fmeet f g \<in> S \<and> fjoin f g \<in> S)"

theorem closed_set_distributive:
  assumes "mj_closed S" and "f \<in> S" and "g \<in> S" and "h \<in> S"
  shows "fmeet f (fjoin g h) = fjoin (fmeet f g) (fmeet f h)"
  by (rule fmeet_fjoin_distrib)

text \<open>THE MAP, DRAWN.  Distributivity is inherited (@{thm fmeet_fjoin_distrib}), the
      function space is a lattice (@{thm fmeet_greatest}, @{thm fjoin_least}), the
      monotone functions are a sublattice (@{thm dmono_fmeet}, @{thm dmono_fjoin}), and
      any meet/join-closed set is a distributive lattice
      (@{thm closed_set_distributive}).  So proving the broken lattice "distributive"
      is EASY -- it is inherited from the Booleans -- and it is NOT the frontier.

      The frontier is the CLOSURE.  The cofactor SET is not meet/join-closed in general
      -- the meet of two cofactors need not be a cofactor, which is exactly the
      brokenness.  To apply Birkhoff and the pathwidth bridge, one takes the meet/join
      CLOSURE of the cofactor set: a distributive lattice (by @{thm closed_set_distributive})
      that "fills in" the defect points and un-breaks the broken lattice.  Its size, and
      its antichain (Dilworth) width, are what the pathwidth bound needs bounded -- the
      quantity W_0, now for the closure.  So the map reads: distributivity, free;
      closure size / antichain width, the real and open work.  Nothing here is assumed.\<close>

end
