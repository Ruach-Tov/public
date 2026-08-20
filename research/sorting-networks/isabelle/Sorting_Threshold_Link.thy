theory Sorting_Threshold_Link
  imports Main
begin

(* ============================================================================
   CONNECTIVE THEORY 1: sorting and the threshold structure.

   This theory welds two of the proof islands.  It re-states the minimal
   definitions (self-contained, imports Main only, to avoid the name clashes that
   arise from importing sibling theories that share constant names), and proves:

     (WELD)  a network that sorts every 0/1 input produces, on every input, a
             nondecreasing (bsorted) output.  This is definitional once sorting is
             taken to mean "the output is bsorted", but the book cited it as a step
             without stating it; here it is a named theorem.

     (DISCOVERY, found by exploration)  a bsorted 0/1 vector is exactly a
             THERMOMETER CODE: a block of falses followed by a block of trues.
             Equivalently, its entry i is the threshold "at least (length - i) of
             the entries are true".  Sortedness and the threshold structure are the
             SAME thing on 0/1 vectors -- so the bridge from sorting to thresholds is
             not merely a chain of two lemmas but a single equivalence.
   ============================================================================ *)

definition count_true :: "bool list \<Rightarrow> nat" where
  "count_true x = length (filter id x)"

definition thr :: "nat \<Rightarrow> bool list \<Rightarrow> bool" where
  "thr t x = (t \<le> count_true x)"

definition bsorted :: "bool list \<Rightarrow> bool" where
  "bsorted v \<longleftrightarrow> (\<forall>i j. i \<le> j \<and> j < length v \<longrightarrow> v!i \<longrightarrow> v!j)"

text \<open>A comparator run on bool lists (min = conjunction to the low index, max =
      disjunction to the high).  A network sorts if every output is bsorted.\<close>

definition cstep :: "nat \<Rightarrow> nat \<Rightarrow> bool list \<Rightarrow> bool list" where
  "cstep a b v = v[a := (v!a \<and> v!b), b := (v!a \<or> v!b)]"

fun crun :: "(nat \<times> nat) list \<Rightarrow> bool list \<Rightarrow> bool list" where
  "crun [] v = v" |
  "crun ((a,b) # cs) v = crun cs (cstep a b v)"

definition sorts_all_bool :: "(nat \<times> nat) list \<Rightarrow> nat \<Rightarrow> bool" where
  "sorts_all_bool cs n \<longleftrightarrow> (\<forall>v. length v = n \<longrightarrow> bsorted (crun cs v))"

text \<open>THE WELD.  A sorting network's output is bsorted.  (Definitional, now named.)\<close>

theorem sorts_gives_bsorted_output:
  assumes "sorts_all_bool cs n" and "length v = n"
  shows "bsorted (crun cs v)"
  using assms by (simp add: sorts_all_bool_def)

text \<open>A THERMOMETER CODE: a run of falses followed by a run of trues.\<close>

definition thermometer :: "bool list \<Rightarrow> bool" where
  "thermometer v \<longleftrightarrow> (\<exists>k \<le> length v. v = replicate (length v - k) False @ replicate k True)"

text \<open>THE DISCOVERY.  A bool list is bsorted if and only if it is a thermometer
      code.  So sortedness of a 0/1 vector is exactly the threshold-block structure.
      The forward direction: a bsorted list has all its trues at the end, so it is a
      false-block then a true-block.  The reverse: a thermometer code is manifestly
      nondecreasing.\<close>

lemma thermometer_bsorted:
  assumes "thermometer v"
  shows "bsorted v"
proof -
  from assms obtain k where k: "k \<le> length v"
    and v: "v = replicate (length v - k) False @ replicate k True"
    by (auto simp: thermometer_def)
  show ?thesis
    unfolding bsorted_def
  proof (intro allI impI)
    fix i j assume ij: "i \<le> j \<and> j < length v" and vi: "v!i"
    let ?z = "length v - k"
    have lenrep: "length (replicate ?z False) = ?z" by simp
    have "i \<ge> ?z"
    proof (rule ccontr)
      assume "\<not> ?z \<le> i" hence "i < ?z" by simp
      have "v!i = (replicate ?z False @ replicate k True)!i" using v by simp
      also have "... = (replicate ?z False)!i"
        using \<open>i < ?z\<close> lenrep by (simp add: nth_append)
      also have "... = False" using \<open>i < ?z\<close> by simp
      finally show False using vi by simp
    qed
    hence jz: "j \<ge> ?z" using ij by simp
    have jl: "j < length v" using ij by simp
    have "v!j = (replicate ?z False @ replicate k True)!j" using v by simp
    also have "... = (replicate k True)!(j - ?z)"
      using jz lenrep by (simp add: nth_append)
    also have "... = True" using jz jl k by simp
    finally show "v!j" by simp
  qed
qed

lemma bsorted_thermometer:
  assumes "bsorted v"
  shows "thermometer v"
proof -
  let ?k = "count_true v"
  let ?z = "length v - ?k"
  \<comment> \<open>Every true is at position >= ?z, every false at position < ?z.\<close>
  have kle: "?k \<le> length v" by (simp add: count_true_def)
  have "v = replicate ?z False @ replicate ?k True"
  proof (rule nth_equalityI)
    show len: "length v = length (replicate ?z False @ replicate ?k True)"
      using kle by simp
  next
    fix i assume i: "i < length v"
    have trues: "{i. i < length v \<and> v!i} = {?z..<length v}"
    proof
      show "{i. i < length v \<and> v!i} \<subseteq> {?z..<length v}"
      proof
        fix x assume "x \<in> {i. i < length v \<and> v!i}"
        hence xl: "x < length v" and vx: "v!x" by auto
        have "card {i. i < length v \<and> v!i} = ?k"
          by (simp add: count_true_def length_filter_conv_card)
        \<comment> \<open>the set of true positions has size k; being an up-set of a bsorted
            list it is exactly the top k positions\<close>
        have up: "\<And>j. \<lbrakk>x \<le> j; j < length v\<rbrakk> \<Longrightarrow> v!j"
          using assms vx xl unfolding bsorted_def by blast
        have sub: "{x..<length v} \<subseteq> {i. i < length v \<and> v!i}" using up by auto
        have fin: "finite {i. i < length v \<and> v!i}" by simp
        have "card {x..<length v} \<le> card {i. i < length v \<and> v!i}"
          by (rule card_mono[OF fin sub])
        hence "length v - x \<le> ?k"
          using \<open>card {i. i < length v \<and> v!i} = ?k\<close> by simp
        thus "x \<in> {?z..<length v}" using xl by auto
      qed
    next
      show "{?z..<length v} \<subseteq> {i. i < length v \<and> v!i}"
      proof
        fix x assume x: "x \<in> {?z..<length v}"
        hence xz: "?z \<le> x" and xl: "x < length v" by auto
        \<comment> \<open>if v!x were false, all positions <= x would be false, leaving < k trues\<close>
        show "x \<in> {i. i < length v \<and> v!i}"
        proof (cases "v!x")
          case True thus ?thesis using xl by simp
        next
          case False
          have lowf: "\<And>j. j \<le> x \<Longrightarrow> \<not> v!j"
            using assms False xl unfolding bsorted_def by blast
          have "{i. i < length v \<and> v!i} \<subseteq> {x<..<length v}"
          proof
            fix y assume "y \<in> {i. i < length v \<and> v!i}"
            hence yl: "y < length v" and vy: "v!y" by auto
            have "x < y" using lowf vy by (metis not_less)
            thus "y \<in> {x<..<length v}" using yl by simp
          qed
          hence sub2: "{i. i < length v \<and> v!i} \<subseteq> {x<..<length v}" .
          have "?k = card {i. i < length v \<and> v!i}"
            by (simp add: count_true_def length_filter_conv_card)
          also have "... \<le> card {x<..<length v}"
            by (rule card_mono[OF finite_greaterThanLessThan sub2])
          finally have kle2: "?k \<le> card {x<..<length v}" .
          have cardeq: "card {x<..<length v} = length v - x - 1"
          proof -
            have "{x<..<length v} = {Suc x..<length v}" by auto
            thus ?thesis by simp
          qed
          have "?k \<le> length v - x - 1" using kle2 cardeq by simp
          thus ?thesis using xz xl by simp
        qed
      qed
    qed
    show "v!i = (replicate ?z False @ replicate ?k True)!i"
    proof (cases "i < ?z")
      case True
      hence "i \<notin> {?z..<length v}" by simp
      hence "\<not> v!i" using trues i by blast
      thus ?thesis using True by (simp add: nth_append)
    next
      case False
      hence "i \<in> {?z..<length v}" using i by simp
      hence "v!i" using trues by blast
      moreover have "(replicate ?z False @ replicate ?k True)!i"
        using False i kle by (simp add: nth_append)
      ultimately show ?thesis by simp
    qed
  qed
  thus ?thesis using kle by (auto simp: thermometer_def)
qed

theorem bsorted_iff_thermometer: "bsorted v \<longleftrightarrow> thermometer v"
  using thermometer_bsorted bsorted_thermometer by blast

text \<open>Consequence, the structural weld: a sorting network's output is a thermometer
      code -- a block of falses then a block of trues -- so each of its entries is a
      threshold of the count.  Sorting and the threshold structure are one.\<close>

theorem sorter_output_is_thermometer:
  assumes "sorts_all_bool cs n" and "length v = n"
  shows "thermometer (crun cs v)"
  using sorts_gives_bsorted_output[OF assms] bsorted_iff_thermometer by blast

end
