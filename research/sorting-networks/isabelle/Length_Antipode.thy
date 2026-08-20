theory Length_Antipode
  imports Main
begin

(* ============================================================================
   GROWING THE CONNECTIONS: the Coxeter length and OUR antipode are the same
   reflection.

   The two-face bridge placed our width problem in the Bruhat order and bounded the
   forward defect by the backward reachable count.  Recovering that ground, more
   connections grow --- and the sweetest is that the ANTIPODE, which has run through the
   whole book (complementing the rank, exchanging wire i with wire n-1-i, fixing the
   defect), reappears here as the Bruhat/length antipode: composing a permutation with
   the longest element w_0 complements the Coxeter length.  So the antipode of the
   cofactor lattice and the antipode of the Coxeter group are one reflection, seen on
   two sides.

   We work with the inversion-count length and the reversing permutation w_0(i)=n-1-i.
   Composing with w_0 on the value side, (w_0 . p)(i) = n-1 - p(i), reverses the values,
   turning each non-inversion into an inversion and back.  Self-contained (imports Main).
   ============================================================================ *)

definition inversions :: "(nat \<Rightarrow> nat) \<Rightarrow> nat \<Rightarrow> (nat \<times> nat) set" where
  "inversions p n = {(i,j). i < j \<and> j < n \<and> p j < p i}"

definition coxeter_length :: "(nat \<Rightarrow> nat) \<Rightarrow> nat \<Rightarrow> nat" where
  "coxeter_length p n = card (inversions p n)"

definition ordered_pairs :: "nat \<Rightarrow> (nat \<times> nat) set" where
  "ordered_pairs n = {(i,j). i < j \<and> j < n}"

definition w0 :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "w0 n i = n - 1 - i"

text \<open>Composing p with the value-reversal w_0: (w0comp p)(i) = n-1 - p(i).  This is the
      permutation-side antipode --- it reverses the output values.\<close>

definition w0comp :: "nat \<Rightarrow> (nat \<Rightarrow> nat) \<Rightarrow> (nat \<Rightarrow> nat)" where
  "w0comp n p = (\<lambda>i. n - 1 - p i)"

lemma finite_ordered_pairs: "finite (ordered_pairs n)"
proof -
  have "ordered_pairs n \<subseteq> {..<n} \<times> {..<n}" by (auto simp: ordered_pairs_def)
  thus ?thesis by (rule finite_subset) simp
qed

lemma inversions_subset: "inversions p n \<subseteq> ordered_pairs n"
  by (auto simp: inversions_def ordered_pairs_def)

text \<open>THE COMPLEMENTATION.  On a permutation p of @{term "{..<n}"} whose values are
      exactly @{term "{..<n}"} (a genuine permutation, so p i < n and p injective), the
      value-reversal turns an ordered pair (i,j) into an inversion of w0comp p exactly
      when it was NOT an inversion of p.  So the inversion set of w0comp p is the
      COMPLEMENT, within the ordered pairs, of the inversion set of p.\<close>

theorem inversions_w0comp:
  assumes perm: "\<forall>i<n. p i < n" and inj: "inj_on p {..<n}"
  shows "inversions (w0comp n p) n = ordered_pairs n - inversions p n"
proof
  show "inversions (w0comp n p) n \<subseteq> ordered_pairs n - inversions p n"
  proof
    fix x assume "x \<in> inversions (w0comp n p) n"
    then obtain i j where x: "x = (i,j)" and ij: "i < j" and jn: "j < n"
      and lt: "w0comp n p j < w0comp n p i"
      by (auto simp: inversions_def)
    have iln: "i < n" using ij jn by simp
    have pj: "p j < n" and pi: "p i < n" using perm jn iln by auto
    \<comment> \<open>n-1-p j < n-1-p i  means  p i < p j  (values reversed)\<close>
    have "p i < p j" using lt pi pj by (simp add: w0comp_def)
    hence "\<not> (p j < p i)" by simp
    hence "(i,j) \<notin> inversions p n" by (simp add: inversions_def)
    moreover have "(i,j) \<in> ordered_pairs n" using ij jn by (simp add: ordered_pairs_def)
    ultimately show "x \<in> ordered_pairs n - inversions p n" using x by simp
  qed
next
  show "ordered_pairs n - inversions p n \<subseteq> inversions (w0comp n p) n"
  proof
    fix x assume "x \<in> ordered_pairs n - inversions p n"
    hence "x \<in> ordered_pairs n" and "x \<notin> inversions p n" by auto
    then obtain i j where x: "x = (i,j)" and ij: "i < j" and jn: "j < n"
      by (auto simp: ordered_pairs_def)
    have iln: "i < n" using ij jn by simp
    have pj: "p j < n" and pi: "p i < n" using perm jn iln by auto
    have "\<not> (p j < p i)" using \<open>x \<notin> inversions p n\<close> x ij jn by (simp add: inversions_def)
    hence "p i \<le> p j" by simp
    \<comment> \<open>distinct values (injective), so p i < p j strictly\<close>
    have "p i \<noteq> p j" using inj ij jn iln by (auto simp: inj_on_def)
    with \<open>p i \<le> p j\<close> have "p i < p j" by simp
    hence "w0comp n p j < w0comp n p i" using pi pj by (simp add: w0comp_def)
    thus "x \<in> inversions (w0comp n p) n" using x ij jn by (simp add: inversions_def)
  qed
qed

text \<open>THE LENGTH ANTIPODE.  Hence the length of the value-reversed permutation is the
      complement of the length: @{term "coxeter_length (w0comp n p) n = card (ordered_pairs n) - coxeter_length p n"}.
      For a permutation, the two lengths sum to @{term "card (ordered_pairs n)"} =
      $\binom{n}{2}$.  This is OUR antipode: it exchanges $\ell$ with
      $\binom{n}{2} - \ell$, reflecting the length about its midpoint --- the same
      reflection that exchanges wire $i$ with wire $n-1-i$ and the rank with its
      complement.\<close>

theorem coxeter_length_antipode:
  assumes perm: "\<forall>i<n. p i < n" and inj: "inj_on p {..<n}"
  shows "coxeter_length (w0comp n p) n + coxeter_length p n = card (ordered_pairs n)"
proof -
  have sub: "inversions p n \<subseteq> ordered_pairs n" by (rule inversions_subset)
  have fin: "finite (ordered_pairs n)" by (rule finite_ordered_pairs)
  have "coxeter_length (w0comp n p) n = card (ordered_pairs n - inversions p n)"
    using inversions_w0comp[OF perm inj] by (simp add: coxeter_length_def)
  also have "... = card (ordered_pairs n) - card (inversions p n)"
    using fin sub by (simp add: card_Diff_subset finite_subset)
  finally have "coxeter_length (w0comp n p) n
                  = card (ordered_pairs n) - coxeter_length p n"
    by (simp add: coxeter_length_def)
  moreover have "coxeter_length p n \<le> card (ordered_pairs n)"
    unfolding coxeter_length_def using fin sub by (simp add: card_mono)
  ultimately show ?thesis by simp
qed

text \<open>Reading.  The antipode of the whole book --- the reflection that complements the
      rank, exchanges wire $i$ with wire $n-1-i$, and fixes the defect --- is, on the
      permutation side, the Bruhat/length antipode: @{thm coxeter_length_antipode} shows
      value-reversal exchanges the Coxeter length $\ell$ with $\binom{n}{2}-\ell$,
      reflecting it about its midpoint.  So the forward antipode of the cofactor lattice
      and the length antipode of the Coxeter group are ONE reflection, seen on two sides
      of the two-faced object.  The median --- the length-$\binom{n}{2}/2$ self-reverse,
      the self-dual wire, the fixed point --- is the same centre throughout.  Another loop
      of the study closes: the Coxeter length carries our antipode, and the two faces
      share not only a bridge but a symmetry.  Nothing here is assumed.\<close>

end
