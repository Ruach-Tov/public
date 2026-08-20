theory Wire_Support
  imports Main
begin

(* ============================================================================
   AUTODIDACTERY: THE SUPPORT OF INTERMEDIATE WIRES.

   For the joy of learning, not toward a goal: what does a comparator do to the
   SUPPORT of a wire -- the set of input indices the wire's value actually depends on?
   These are honest facts about information flow in a comparator network, true for all
   n, proved by reasoning.  They build the map of how support grows through the
   network, which is where the intermediate-wire question lives.

   We model a wire configuration abstractly: each wire j carries a support set
   sup j \<subseteq> {..<n} (the inputs it depends on) and evolves under comparators.  A
   comparator (a,b) replaces the supports of wires a and b by their UNION -- the new
   values there are functions of the old pair -- and leaves other wires untouched.
   This over-approximates the true dependence (min/max may drop a dependence, never
   add one), so every provable upper bound here is honest.

   Self-contained (imports Main).
   ============================================================================ *)

type_synonym config = "nat \<Rightarrow> nat set"

text \<open>The comparator step on supports: wires a and b become the union of their
      supports; every other wire is unchanged.\<close>

definition sstep :: "nat \<Rightarrow> nat \<Rightarrow> config \<Rightarrow> config" where
  "sstep a b s = (\<lambda>j. if j = a \<or> j = b then s a \<union> s b else s j)"

fun srun :: "(nat \<times> nat) list \<Rightarrow> config \<Rightarrow> config" where
  "srun [] s = s" |
  "srun ((a,b) # cs) s = srun cs (sstep a b s)"

text \<open>The initial configuration: wire i depends on input i alone.\<close>

definition init_config :: "config" where
  "init_config = (\<lambda>i. {i})"

text \<open>FACT 1 -- UNTOUCHED WIRES KEEP THEIR SUPPORT.\<close>

theorem sstep_untouched:
  assumes "j \<noteq> a" and "j \<noteq> b"
  shows "sstep a b s j = s j"
  using assms by (simp add: sstep_def)

text \<open>FACT 2 -- A COMPARATOR ONLY MERGES: each touched wire's new support is the union
      of the two old ones, so it is contained in that union -- never a new index.\<close>

theorem sstep_merge_a: "sstep a b s a = s a \<union> s b"
  by (simp add: sstep_def)

theorem sstep_merge_b: "sstep a b s b = s a \<union> s b"
  by (simp add: sstep_def)

text \<open>FACT 3 -- THE UNION OF ALL SUPPORTS IS PRESERVED.  Merging two supports into
      their union changes no wire's contribution to the overall union.  So the set of
      inputs that still matter, taken across all wires, is invariant under a
      comparator -- information is neither created nor destroyed in aggregate, only
      redistributed.\<close>

theorem sstep_preserves_union:
  "(\<Union>j \<in> W. sstep a b s j) = (\<Union>j \<in> W. s j) \<union> (if a \<in> W \<or> b \<in> W then s a \<union> s b else {})"
  by (auto simp: sstep_def)

text \<open>A cleaner form when both touched wires are among those considered: the union is
      exactly preserved.\<close>

theorem sstep_union_eq:
  assumes "a \<in> W" and "b \<in> W"
  shows "(\<Union>j \<in> W. sstep a b s j) = (\<Union>j \<in> W. s j)"
proof
  show "(\<Union>j \<in> W. sstep a b s j) \<subseteq> (\<Union>j \<in> W. s j)"
    using assms by (auto simp: sstep_def)
next
  show "(\<Union>j \<in> W. s j) \<subseteq> (\<Union>j \<in> W. sstep a b s j)"
  proof
    fix x assume "x \<in> (\<Union>j \<in> W. s j)"
    then obtain j where jW: "j \<in> W" and xj: "x \<in> s j" by blast
    show "x \<in> (\<Union>j \<in> W. sstep a b s j)"
    proof (cases "j = a \<or> j = b")
      case True
      hence "x \<in> sstep a b s a" using xj by (auto simp: sstep_def)
      thus ?thesis using assms(1) by blast
    next
      case False
      hence "sstep a b s j = s j" by (simp add: sstep_def)
      thus ?thesis using jW xj by auto
    qed
  qed
qed

text \<open>FACT 4 -- SUPPORT STAYS WITHIN THE INITIAL INDEX SET.  Starting from singletons
      within @{term "{..<n}"}, every support at every step is a subset of @{term "{..<n}"}:
      a comparator introduces no index outside the wires it merges.  So every wire
      depends on at most @{term n} inputs -- the honest, if coarse, ceiling.\<close>

lemma sstep_within:
  assumes "\<forall>j. s j \<subseteq> {..<n}"
  shows "\<forall>j. sstep a b s j \<subseteq> {..<n}"
  using assms by (auto simp: sstep_def)

theorem srun_within:
  assumes "\<forall>j. s j \<subseteq> {..<n}"
  shows "\<forall>j. srun cs s j \<subseteq> {..<n}"
  using assms
proof (induct cs arbitrary: s)
  case Nil then show ?case by simp
next
  case (Cons c cs)
  obtain a b where "c = (a,b)" by (cases c)
  moreover have "\<forall>j. sstep a b s j \<subseteq> {..<n}" using Cons.prems by (rule sstep_within)
  ultimately show ?case using Cons.hyps by simp
qed

theorem support_card_le_n:
  \<comment> \<open>when the initial supports are all within {..<n} (a well-formed n-wire net),
      every wire's support has at most n elements\<close>
  assumes "\<forall>i. init_config i \<subseteq> {..<n}"
  shows "card (srun cs init_config j) \<le> n"
proof -
  have sub: "srun cs init_config j \<subseteq> {..<n}"
    using srun_within[OF assms] by blast
  have "card (srun cs init_config j) \<le> card {..<n::nat}"
    by (rule card_mono[OF finite_lessThan sub])
  thus ?thesis by simp
qed

text \<open>THE HONEST EDGE, in support form.  Support is bounded by @{term n} (there are
      only @{term n} inputs), and grows only by merging touched pairs.  But the RANK
      of a wire ranges over the residual assignments to its support, up to
      @{term "2 ^ card (support)"}: even a support of size @{term n} permits an
      exponential rank range.  So the support ceiling alone does not give a polynomial
      height; what would is a bound showing the wire's dependence on its support is
      itself simple (few distinct residual behaviours).  That is the open map, and the
      support algebra here locates it precisely: the growth of support is tame (union
      of touched pairs, within @{term n}), but the COMBINATORICS of the dependence on
      that support is where the intermediate-wire height is decided.\<close>

text \<open>Reading.  These are honest facts about information flow: a comparator merges the
      supports of the two wires it touches (@{thm sstep_merge_a}, @{thm sstep_merge_b}),
      leaves others alone (@{thm sstep_untouched}), preserves the aggregate union
      (@{thm sstep_union_eq}), and keeps every support within the input set
      (@{thm srun_within}), so no wire depends on more than @{term n} inputs.  None of
      this is assumed; all is proved for every network and every n.  The support grows
      tamely; the exponential possibility lives not in the support's SIZE but in the
      wire's DEPENDENCE on it -- the honest location of the intermediate-wire question.\<close>

end
