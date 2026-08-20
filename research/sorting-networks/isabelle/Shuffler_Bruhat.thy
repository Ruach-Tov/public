theory Shuffler_Bruhat
  imports Main
begin

(* ============================================================================
   RECREATIONAL: the backward shuffler, in Coxeter language.

   The backward reading of a comparator network is a SHUFFLER -- a word of gated
   transpositions.  Read through the Demazure/Bruhat lens, its features acquire names:

     - the gated subword image is governed by TITS' SUBWORD PROPERTY of Bruhat order
       (u <= w iff u is a subword of a reduced word for w);
     - the complete-prefix-code / Kraft-McMillan fact is a REDUCED-WORD NORMAL FORM
       (each permutation a unique canonical subword);
     - the factoradic / Lehmer saturation is the COXETER LENGTH -- the inversion count --
       peaking at ell(w_0) = C(n,2) for the longest element.

   This theory proves the arithmetic that grounds the last point: the length function
   on permutations is the number of inversions, it is bounded by C(n,2) = n(n-1)/2, and
   the bound is attained by the reversing permutation w_0.  So the maximal essential
   depth of the backward trace is the Coxeter length of w_0 -- the sorting network, read
   backward, saturates the length function.  Self-contained (imports Main).

   A permutation of {0..<n} is a bijective function on that set; its inversions are the
   out-of-order pairs.
   ============================================================================ *)

definition inversions :: "(nat \<Rightarrow> nat) \<Rightarrow> nat \<Rightarrow> (nat \<times> nat) set" where
  "inversions p n = {(i,j). i < j \<and> j < n \<and> p j < p i}"

definition coxeter_length :: "(nat \<Rightarrow> nat) \<Rightarrow> nat \<Rightarrow> nat" where
  "coxeter_length p n = card (inversions p n)"

text \<open>The inversion set lies inside the set of ordered pairs below n, which has
      cardinality C(n,2) = n(n-1)/2.  So the length is bounded by that.\<close>

definition ordered_pairs :: "nat \<Rightarrow> (nat \<times> nat) set" where
  "ordered_pairs n = {(i,j). i < j \<and> j < n}"

lemma finite_ordered_pairs: "finite (ordered_pairs n)"
proof -
  have "ordered_pairs n \<subseteq> {..<n} \<times> {..<n}"
    by (auto simp: ordered_pairs_def)
  thus ?thesis by (rule finite_subset) simp
qed

lemma inversions_subset: "inversions p n \<subseteq> ordered_pairs n"
  by (auto simp: inversions_def ordered_pairs_def)

lemma card_ordered_pairs: "card (ordered_pairs n) = n * (n - 1) div 2"
proof (induct n)
  case 0 show ?case by (simp add: ordered_pairs_def)
next
  case (Suc n)
  \<comment> \<open>the new pairs are exactly (i, n) for i < n\<close>
  have split: "ordered_pairs (Suc n) = ordered_pairs n \<union> ((\<lambda>i. (i, n)) ` {..<n})"
    by (auto simp: ordered_pairs_def less_Suc_eq)
  have disj: "ordered_pairs n \<inter> ((\<lambda>i. (i, n)) ` {..<n}) = {}"
    by (auto simp: ordered_pairs_def)
  have finA: "finite (ordered_pairs n)" by (rule finite_ordered_pairs)
  have finB: "finite ((\<lambda>i. (i, n)) ` {..<n})" by simp
  have cardB: "card ((\<lambda>i. (i, n)) ` {..<n}) = n"
    by (subst card_image) (auto simp: inj_on_def)
  have "card (ordered_pairs (Suc n)) = card (ordered_pairs n) + card ((\<lambda>i. (i, n)) ` {..<n})"
    using split disj finA finB by (simp add: card_Un_disjoint)
  also have "... = n * (n - 1) div 2 + n" using Suc cardB by simp
  also have "... = Suc n * (Suc n - 1) div 2" by (cases n) auto
  finally show ?case .
qed

text \<open>THE COXETER LENGTH IS BOUNDED BY C(n,2).  Every permutation has at most
      n(n-1)/2 inversions -- the count of ordered pairs.\<close>

theorem coxeter_length_bound:
  "coxeter_length p n \<le> n * (n - 1) div 2"
proof -
  have "coxeter_length p n = card (inversions p n)" by (simp add: coxeter_length_def)
  also have "... \<le> card (ordered_pairs n)"
    by (rule card_mono[OF finite_ordered_pairs inversions_subset])
  also have "... = n * (n - 1) div 2" by (rule card_ordered_pairs)
  finally show ?thesis .
qed

text \<open>THE REVERSING PERMUTATION ATTAINS THE BOUND.  The longest element w_0, which
      reverses the order (w_0 i = n-1-i), inverts EVERY ordered pair: for i < j < n,
      w_0 j = n-1-j < n-1-i = w_0 i.  So its inversion set is all of the ordered pairs,
      and its length is exactly C(n,2) -- the saturation the backward Lehmer digits show.\<close>

definition w0 :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "w0 n i = n - 1 - i"

theorem w0_inverts_all:
  "inversions (w0 n) n = ordered_pairs n"
proof
  show "inversions (w0 n) n \<subseteq> ordered_pairs n" by (rule inversions_subset)
next
  show "ordered_pairs n \<subseteq> inversions (w0 n) n"
  proof
    fix x assume "x \<in> ordered_pairs n"
    then obtain i j where x: "x = (i,j)" and ij: "i < j" and jn: "j < n"
      by (auto simp: ordered_pairs_def)
    have "w0 n j < w0 n i" using ij jn by (simp add: w0_def)
    thus "x \<in> inversions (w0 n) n" using x ij jn by (simp add: inversions_def)
  qed
qed

theorem w0_length_maximal:
  "coxeter_length (w0 n) n = n * (n - 1) div 2"
proof -
  have "coxeter_length (w0 n) n = card (inversions (w0 n) n)"
    by (simp add: coxeter_length_def)
  also have "... = card (ordered_pairs n)" by (simp add: w0_inverts_all)
  also have "... = n * (n - 1) div 2" by (rule card_ordered_pairs)
  finally show ?thesis .
qed

text \<open>Reading, recreationally.  The backward shuffler is the Coxeter-length reading of
      the network.  @{thm coxeter_length_bound}: every permutation has at most
      $\binom{n}{2}$ inversions -- the essential depth of a trace is bounded by that
      length.  @{thm w0_inverts_all} and @{thm w0_length_maximal}: the reversing
      permutation $w_0$, the sorted-to-antisorted extreme, inverts every pair and
      attains the maximal length $\binom{n}{2}$ -- exactly the saturation the backward
      Lehmer digits $(n{-}1, n{-}2, \dots, 1, 0)$ display.  So the factoradic saturation
      of the backward shuffler IS the Coxeter length function reaching its maximum at
      $w_0$; the complete prefix code (Kraft one) is the reduced-word normal form of the
      Bruhat order; and Tits' subword property is the shuffler's surjectivity test.  Our
      backward shuffler and the Bruhat/Coxeter world are the same object, and here the
      length-saturation is proven.\<close>

end
