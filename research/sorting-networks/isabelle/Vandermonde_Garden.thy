theory Vandermonde_Garden
  imports Main
begin

(* ============================================================================
   THE GARDEN OF VANDERMONDE: from the convolution identity to Batcher's width.

   Batcher's recursive-merge sorter has intermediate cofactor width equal to the
   threshold ramp min(t, n+1-t)+1 -- the binomial SUPPORT ramp, LINEAR in n -- rather than
   the binomial PEAK C(n, n/2), which is exponential.  The structural reason: a merge of
   two sorted sequences is the CONVOLUTION of their 0/1-count distributions, and the
   convolution of two binomial rows is the next binomial row (Vandermonde).  The support
   of the count distribution is what the cofactor width tracks; the support grows by
   addition, hence linearly.

   HOL already proves the seed:
       vandermonde:  (\<Sum>k\<le>r. (m choose k) * (n choose (r-k))) = (m+n) choose r.
   We do not reprove it.  This theory PLANTS THE GARDEN AROUND IT -- the facts that turn
   the convolution identity into the width schedule:

     - the count of a 0/1 vector (number of ones) is additive under concatenation;
     - the set of achievable counts of a length-n vector is exactly {0..n} -- the SUPPORT,
       of size n+1, LINEAR;
     - merging two blocks adds their counts, so the merged support is the sumset of the
       parts' supports: {0..m} + {0..m} = {0..2m} -- the support DOUBLES ADDITIVELY, not
       multiplicatively;
     - Vandermonde is the multiplicity-carrying form of that additive support law.

   The width tracks the support ({0..n}, size n+1), which grows by ADDITION under merge,
   giving the linear ramp; the adversary's slice tracks the peak coefficient C(n, n/2),
   which grows by the binomial and is exponential.  The garden is the additive-support
   law; the seed is Vandermonde.  Self-contained beyond HOL-Library.Multiset.
   ============================================================================ *)

text \<open>THE COUNT of a boolean vector: the number of true entries.  This is the ``weight''
      that a sorted sequence records, and the variable the generating function tracks.\<close>

definition count_ones :: "bool list \<Rightarrow> nat" where
  "count_ones v = length (filter id v)"

text \<open>The count is ADDITIVE under concatenation -- the merge of two blocks carries the
      sum of their counts.  This is the additive law the generating-function product
      (1+x)^m (1+x)^p = (1+x)^{m+p} encodes.\<close>

theorem count_ones_append:
  "count_ones (u @ w) = count_ones u + count_ones w"
  by (simp add: count_ones_def)

lemma count_ones_replicate_True: "count_ones (replicate k True) = k"
  by (simp add: count_ones_def)

lemma count_ones_replicate_False: "count_ones (replicate k False) = 0"
  by (simp add: count_ones_def)

text \<open>THE SUPPORT: the set of achievable counts of a length-n vector is exactly {0..n}.
      Its size is n+1 --- LINEAR.  This is the support of the binomial row, the quantity
      the cofactor width tracks.\<close>

theorem achievable_counts:
  "{count_ones v | v. length v = n} = {..n}"
proof
  show "{count_ones v | v. length v = n} \<subseteq> {..n}"
  proof
    fix c assume "c \<in> {count_ones v | v. length v = n}"
    then obtain v where "c = count_ones v" and "length v = n" by auto
    hence "c \<le> n" by (simp add: count_ones_def) (metis length_filter_le)
    thus "c \<in> {..n}" by simp
  qed
next
  show "{..n} \<subseteq> {count_ones v | v. length v = n}"
  proof
    fix c assume "c \<in> {..n}"
    hence "c \<le> n" by simp
    \<comment> \<open>the vector of c ones then n-c falses has count c and length n\<close>
    let ?v = "replicate c True @ replicate (n - c) False"
    have L: "length ?v = n" using \<open>c \<le> n\<close> by simp
    have C: "count_ones ?v = c"
      by (simp add: count_ones_append count_ones_replicate_True count_ones_replicate_False)
    have "c = count_ones ?v \<and> length ?v = n" using C L by simp
    thus "c \<in> {count_ones v | v. length v = n}" by blast
  qed
qed

theorem support_size:
  "card {count_ones v | v. length v = n} = n + 1"
  by (subst achievable_counts) simp

text \<open>THE MERGE SUPPORT LAW.  Concatenating a length-m block and a length-p block yields
      counts that are exactly the sumset {0..m} + {0..p} = {0..m+p}.  The support adds;
      it does not multiply.  This is the ADDITIVE growth that keeps the width linear.\<close>

theorem merge_support_sumset:
  "{count_ones u + count_ones w | u w. length u = m \<and> length w = p} = {..(m + p)}"
proof
  show "{count_ones u + count_ones w | u w. length u = m \<and> length w = p} \<subseteq> {..m + p}"
    by (auto simp: count_ones_def)
       (metis add_le_mono length_filter_le)
next
  show "{..m + p} \<subseteq> {count_ones u + count_ones w | u w. length u = m \<and> length w = p}"
  proof
    fix c assume "c \<in> {..m + p}"
    hence cle: "c \<le> m + p" by simp
    \<comment> \<open>split c into a part <= m and the rest <= p\<close>
    define a where "a = min c m"
    define b where "b = c - a"
    have "a \<le> m" by (simp add: a_def)
    have "b \<le> p" using cle unfolding a_def b_def by linarith
    have "a + b = c" unfolding a_def b_def by simp
    let ?u = "replicate a True @ replicate (m - a) False"
    let ?w = "replicate b True @ replicate (p - b) False"
    have "length ?u = m" using \<open>a \<le> m\<close> by simp
    moreover have "length ?w = p" using \<open>b \<le> p\<close> by simp
    moreover have "count_ones ?u + count_ones ?w = c"
      using \<open>a + b = c\<close>
      by (simp add: count_ones_append count_ones_replicate_True count_ones_replicate_False)
    ultimately have "c = count_ones ?u + count_ones ?w \<and> length ?u = m \<and> length ?w = p" by simp
    thus "c \<in> {count_ones u + count_ones w | u w. length u = m \<and> length w = p}" by blast
  qed
qed

text \<open>Reading.  The garden grows from Vandermonde.  @{thm count_ones_append}: the count is
      additive under merge --- the generating-function product law $(1+x)^m (1+x)^p =
      (1+x)^{m+p}$ at the level of counts.  @{thm achievable_counts} and
      @{thm support_size}: the achievable counts of a length-$n$ block are exactly
      $\{0,\dots,n\}$, a support of size $n+1$, LINEAR --- the quantity the cofactor width
      of a sorted (threshold) wire tracks.  @{thm merge_support_sumset}: merging two blocks
      adds their supports as a sumset, $\{0..m\}+\{0..p\}=\{0..m+p\}$ --- the support grows
      by ADDITION, not multiplication, which is why the width stays linear under Batcher's
      recursive doubling.  HOL's @{thm vandermonde} is the multiplicity-carrying form of
      this same additive law: the convolution $\sum_k \binom{m}{k}\binom{p}{r-k} =
      \binom{m+p}{r}$ counts, with multiplicity, the ways a merged count $r$ splits across
      the two blocks whose supports add.  So the width tracks the support (linear); the
      adversary's middle slice tracks the peak coefficient $\binom{n}{n/2}$ (exponential);
      and Batcher stays on the support ramp because each merge only ADDS supports.  This is
      the garden --- the additive-support law around the Vandermonde seed.  The paths
      through it (the threshold-ramp width, the recursive-merge induction) are the next
      plantings.  Nothing here is assumed.\<close>

end
