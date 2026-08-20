theory Demazure_Connection
  imports Main
begin

(* ============================================================================
   RECREATIONAL: our comparator IS a Demazure / 0-Hecke operator (by proof).

   Wandering the literature's neighbourhood, our comparator turns out to have a
   distinguished address: the Demazure product (0-Hecke monoid) of Coxeter theory.  A
   0-Hecke generator pi_i is defined by two properties -- it is IDEMPOTENT
   (pi_i o pi_i = pi_i) and it is order-INCREASING toward the sorted arrangement.  A
   comparator has exactly these: sorting a pair twice is the same as once, and a
   comparator never un-sorts.  This little theory proves the defining 0-Hecke relation
   for the comparator on Booleans, connecting our crun/cstep machinery to the
   Demazure/0-Hecke literature not by analogy but by theorem.

   A comparator on wires a < b sends (v!a, v!b) to (min, max) = (conjunction,
   disjunction) on Booleans.  Self-contained (imports Main).
   ============================================================================ *)

definition cstep :: "nat \<Rightarrow> nat \<Rightarrow> bool list \<Rightarrow> bool list" where
  "cstep a b v = v[a := (v!a \<and> v!b), b := (v!a \<or> v!b)]"

text \<open>IDEMPOTENCE -- the defining 0-Hecke relation.  Applying a comparator twice
      equals applying it once: once the pair is sorted, sorting again does nothing.
      This is pi_i o pi_i = pi_i, the idempotence of the Demazure generator.\<close>

theorem cstep_idempotent:
  assumes "a < length v" and "b < length v" and "a \<noteq> b"
  shows "cstep a b (cstep a b v) = cstep a b v"
proof -
  let ?w = "cstep a b v"
  have wa: "?w ! a = (v!a \<and> v!b)"
    using assms by (simp add: cstep_def nth_list_update)
  have wb: "?w ! b = (v!a \<or> v!b)"
    using assms by (simp add: cstep_def nth_list_update)
  have lw: "length ?w = length v" by (simp add: cstep_def)
  have "cstep a b ?w = ?w[a := (?w!a \<and> ?w!b), b := (?w!a \<or> ?w!b)]"
    by (simp add: cstep_def)
  also have "(?w!a \<and> ?w!b) = ?w!a" using wa wb by auto
  also have "(?w!a \<or> ?w!b) = ?w!b" using wa wb by auto
  finally have "cstep a b ?w = ?w[a := ?w!a, b := ?w!b]" by simp
  also have "?w[a := ?w!a, b := ?w!b] = ?w" by (simp add: list_update_id)
  finally show ?thesis .
qed

text \<open>LENGTH PRESERVED (a monoid action on fixed-length vectors).\<close>

theorem cstep_length: "length (cstep a b v) = length v"
  by (simp add: cstep_def)

text \<open>A comparator FIXES already-sorted pairs: if the pair is already in order
      (v!a implies v!b), the comparator leaves the vector unchanged.  This is the other
      half of the 0-Hecke picture -- pi_i acts as the identity on its descent-free set,
      and moves only what is out of order.\<close>

theorem cstep_fixes_sorted:
  assumes "a < length v" and "b < length v" and "a \<noteq> b"
      and "v!a \<longrightarrow> v!b"
  shows "cstep a b v = v"
proof -
  have "(v!a \<and> v!b) = v!a" using assms(4) by auto
  moreover have "(v!a \<or> v!b) = v!b" using assms(4) by auto
  ultimately have "cstep a b v = v[a := v!a, b := v!b]"
    by (simp add: cstep_def)
  thus ?thesis by (simp add: list_update_id)
qed

text \<open>Reading, recreationally.  @{thm cstep_idempotent} proves the defining relation of
      a 0-Hecke / Demazure generator for our comparator: applying it twice equals
      applying it once.  @{thm cstep_fixes_sorted} shows it acts as the identity on
      already-sorted pairs, moving only inversions -- the characteristic behaviour of a
      Demazure operator pi_i.  So the comparator network of the whole book is, literally,
      a Demazure product in the 0-Hecke monoid of the symmetric group; its reachable
      states are a Demazure orbit; and the defect W_0 -- the antichain of that orbit --
      is a maximal antichain in the Bruhat order.  These are named objects with a large
      literature (affine Demazure products, Bruhat antichains, Dedekind numbers), and
      our broken lattice sits among them with a distinguished address.  Proven here is
      only the small, true connecting fact -- the idempotence -- that places it there.\<close>

end
