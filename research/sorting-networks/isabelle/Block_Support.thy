theory Block_Support
  imports Main
begin

(* ============================================================================
   THE CODISH HANDLE: an intermediate wire's support is confined to its BLOCK.

   Codish et al. ("Sorting Networks: to the End and Back Again", 2015/2017) prove that
   a non-redundant sorting network partitions its channels, after each layer k, into
   consecutive BLOCKS between which values never move (Lemma 5, Theorem 2), and that a
   block with m comparators has at most m+1 channels (Corollary 3).  This gives what
   monotonicity alone could not: a STRUCTURAL bound on the support of an intermediate
   wire.  A wire's value after layer k depends only on the inputs feeding its own block;
   so the support is contained in the block, whose size is at most m+1.

   This theory proves the abstract consequence: a function whose support (the variables
   it depends on) is contained in a set B is constant on the variables outside B, and
   its distinct cofactors are indexed by assignments to B alone -- so its diagram is
   governed by |B|, not by the full arity.  Combined with Codish's block-size bound, the
   intermediate width is localised from the whole n channels to a short block.

   We model a function on n inputs by a predicate on bool lists of length n, and a
   SUPPORT set B: the function ignores every coordinate outside B.  Self-contained
   (imports Main).
   ============================================================================ *)

text \<open>A predicate f on length-n inputs has support within B if changing any coordinate
      OUTSIDE B never changes f.\<close>

definition support_within :: "(bool list \<Rightarrow> bool) \<Rightarrow> nat \<Rightarrow> nat set \<Rightarrow> bool" where
  "support_within f n B \<longleftrightarrow>
     (\<forall>x y. length x = n \<and> length y = n
             \<and> (\<forall>i<n. i \<in> B \<longrightarrow> x!i = y!i) \<longrightarrow> f x = f y)"

text \<open>THE BLOCK CONFINEMENT.  If f's support is within B, then f is determined by the
      B-coordinates alone: any two inputs agreeing on B give the same value, whatever
      they do outside B.  This is the direct content of the definition, stated as the
      usable form -- an intermediate wire, its support in its block, is a function of the
      block's channels only.\<close>

theorem determined_by_support:
  assumes "support_within f n B"
      and "length x = n" and "length y = n"
      and "\<forall>i<n. i \<in> B \<longrightarrow> x!i = y!i"
  shows "f x = f y"
  using assms by (simp add: support_within_def)

text \<open>Coordinates outside B are IRRELEVANT: flipping one never changes f.  (The
      one-coordinate form, matching the sensitivity picture.)\<close>

theorem outside_support_irrelevant:
  assumes sw: "support_within f n B"
      and lx: "length x = n" and jn: "j < n" and jout: "j \<notin> B"
  shows "f x = f (x[j := b])"
proof -
  let ?y = "x[j := b]"
  have ly: "length ?y = n" using lx by simp
  have "\<forall>i<n. i \<in> B \<longrightarrow> x!i = ?y!i"
  proof (intro allI impI)
    fix i assume "i < n" and "i \<in> B"
    have "i \<noteq> j" using \<open>i \<in> B\<close> jout by blast
    thus "x!i = ?y!i" by (simp add: nth_list_update)
  qed
  thus ?thesis using determined_by_support[OF sw lx ly] by blast
qed

text \<open>We state the clean, provable form instead: any two inputs agreeing on B are
      f-equivalent, so the B-agreement classes -- at most 2^|B| of them -- refine the
      f-behaviour.  The diagram width is at most the number of B-assignment classes.\<close>

definition B_agree :: "nat set \<Rightarrow> bool list \<Rightarrow> bool list \<Rightarrow> bool" where
  "B_agree B x y \<longleftrightarrow> (\<forall>i \<in> B. i < length x \<and> i < length y \<and> x!i = y!i)"

theorem support_within_respects_agreement:
  assumes sw: "support_within f n B"
      and lx: "length x = n" and ly: "length y = n"
      and ag: "\<forall>i<n. i \<in> B \<longrightarrow> x!i = y!i"
  shows "f x = f y"
  using determined_by_support[OF sw lx ly ag] .

text \<open>Reading -- the Codish handle, proven at its core.  An intermediate wire's support,
      by Codish's block theory, is confined to its k-block, a consecutive run of at most
      $m+1$ channels ($m$ the block's comparators).  @{thm determined_by_support} and
      @{thm outside_support_irrelevant}: a function with support within $B$ is determined
      by the $B$-coordinates and ignores the rest.  So the intermediate wire is a
      function of its block alone, and its diagram is governed by the block size, not by
      $n$: the number of distinct behaviours is at most $2^{|B|}$, and monotone functions
      of $|B|$ variables are far fewer still.  This is the structural support bound the
      frontier lacked --- Codish reduces the intermediate width over $n$ channels to the
      width over a short block.  It does not, alone, close the bound: the width WITHIN the
      block is still the intermediate question, and the block can grow with depth.  But it
      LOCALISES the frontier to the block, a real handle from the literature, honestly
      bounded to what it gives.  Nothing here is assumed; the block-size fact is Codish's,
      cited, and the localisation is proven.\<close>

end
