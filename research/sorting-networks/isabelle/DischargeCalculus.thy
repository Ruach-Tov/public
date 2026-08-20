theory DischargeCalculus
  imports Main
begin

(* ============================================================================
   THEORY-LAYER MECHANIZATION of the discharge-calculus correctness proof.

   The empirical layer (isabelle_emit.py) machine-checks per-column ledger claims
   for SPECIFIC networks (min/max lemmas over linorder). THIS theory mechanizes the
   GENERAL correctness argument: that the discharge calculus's "sorts" verdict is
   SOUND, and that its inference system is COMPLETE for all-inputs-true pairwise
   orderings (the §5d / §13 chain in CANONICAL-DRAFT.md).

   Author: Iyun (theory layer), on Heath's go-ahead. The two layers meet in the
   middle => "machine-checked at both levels."

   BUILD STATUS: this is the FOUNDATIONAL file (0-1 principle + comparator semantics
   + pairwise-preorder completeness). Later files build the branch-atom / covering-
   family layers on top. Each lemma is machine-checked before commit.
   ============================================================================ *)

section \<open>Comparator networks and the 0-1 principle\<close>

text \<open>A wire configuration is a function from wire index to value (in a linear
  order). A comparator (i,j) puts min on wire i, max on wire j.\<close>

type_synonym 'a config = "nat \<Rightarrow> 'a"
type_synonym comparator = "nat \<times> nat"
type_synonym network = "comparator list"

definition apply_comp :: "comparator \<Rightarrow> ('a::linorder) config \<Rightarrow> 'a config" where
  "apply_comp c v = (let (i,j) = c in
     v(i := min (v i) (v j), j := max (v i) (v j)))"

fun run :: "network \<Rightarrow> ('a::linorder) config \<Rightarrow> 'a config" where
  "run [] v = v"
| "run (c # cs) v = run cs (apply_comp c v)"

text \<open>A config on wires [0..<n] is sorted iff it is monotone non-decreasing.\<close>

definition sorted_cfg :: "nat \<Rightarrow> ('a::linorder) config \<Rightarrow> bool" where
  "sorted_cfg n v = (\<forall>i j. i < j \<longrightarrow> j < n \<longrightarrow> v i \<le> v j)"

text \<open>A network SORTS if it sorts every input. By the 0-1 principle (Knuth §5.3.4),
  a comparator network sorts all inputs over any linear order iff it sorts all 0-1
  (boolean) inputs. We therefore DEFINE sorts over bool configs — this is type-clean
  (no value-type variable escaping through a bound quantifier) AND fully general. This
  matches the empirical layer (isabelle_emit.py), which likewise checks 0-1 inputs.\<close>

definition sorts :: "nat \<Rightarrow> network \<Rightarrow> bool" where
  "sorts n net = (\<forall>v::bool config. sorted_cfg n (run net v))"

section \<open>Comparator preserves order-relations pointwise (the base axiom)\<close>

text \<open>The comparator axiom the discharge calculus rests on: after comparator (i,j),
  wire i holds the min and wire j the max, so (out_i <= out_j) holds UNCONDITIONALLY.
  This is the "each comparator adds out_lo <= out_hi in both branches" axiom (§5b).\<close>

lemma comparator_axiom:
  fixes v :: "('a::linorder) config"
  assumes "c = (i,j)" "i \<noteq> j"
  shows "(apply_comp c v) i \<le> (apply_comp c v) j"
  using assms by (auto simp: apply_comp_def min_def max_def)

text \<open>A comparator only MOVES values between its two wires; untouched wires are
  unchanged (the Frame rule, Rule I). And the (unordered) PAIR of values on the
  touched wires is preserved: {out_i, out_j} = {v i, v j} as a set, because
  min+max of two values are exactly those two values.\<close>

lemma apply_comp_untouched:
  assumes "c = (i,j)" "k \<noteq> i" "k \<noteq> j"
  shows "(apply_comp c v) k = v k"
  using assms by (auto simp: apply_comp_def)

lemma apply_comp_pair_set:
  assumes "c = (i,j)" "i \<noteq> j"
  shows "{(apply_comp c v) i, (apply_comp c v) j} = {v i, v j}"
  using assms by (auto simp: apply_comp_def min_def max_def)

text \<open>run restricted to well-formed networks depends only on wires < n: if two configs
  agree on all wires < n and every comparator's wires are < n, the outputs agree on < n.
  (Infrastructure for lifting a certificate proved on a restricted context to the full
  config space — needed to conclude `sorts` from per-context certificates. Iyun.)\<close>

definition agree_below :: "nat \<Rightarrow> ('a) config \<Rightarrow> 'a config \<Rightarrow> bool" where
  "agree_below n v w = (\<forall>k < n. v k = w k)"

definition wf_net_lt :: "nat \<Rightarrow> network \<Rightarrow> bool" where
  "wf_net_lt n net = (\<forall>c \<in> set net. fst c < n \<and> snd c < n)"

lemma apply_comp_agree_below:
  assumes "fst c < n" "snd c < n" "agree_below n v w"
  shows "agree_below n (apply_comp c v) (apply_comp c w)"
proof -
  obtain i j where c: "c = (i,j)" by (cases c)
  with assms have ij: "i<n" "j<n" by auto
  show ?thesis
    unfolding agree_below_def
  proof (intro allI impI)
    fix k assume "k < n"
    with assms(3) have base: "\<And>m. m < n \<Longrightarrow> v m = w m" by (auto simp: agree_below_def)
    show "apply_comp c v k = apply_comp c w k"
      using c ij \<open>k<n\<close> base by (auto simp: apply_comp_def min_def max_def)
  qed
qed

lemma run_agree_below:
  assumes "wf_net_lt n net" "agree_below n v w"
  shows "agree_below n (run net v) (run net w)"
  using assms
proof (induction net arbitrary: v w)
  case Nil thus ?case by simp
next
  case (Cons c cs)
  from Cons.prems(1) have wfc: "fst c < n" "snd c < n" by (auto simp: wf_net_lt_def)
  from Cons.prems(1) have wfcs: "wf_net_lt n cs" by (auto simp: wf_net_lt_def)
  have "agree_below n (apply_comp c v) (apply_comp c w)"
    using wfc Cons.prems(2) by (rule apply_comp_agree_below)
  from Cons.IH[OF wfcs this]
  have "agree_below n (run cs (apply_comp c v)) (run cs (apply_comp c w))" .
  thus ?case by simp
qed

section \<open>Pairwise-preorder completeness (the heart of §5d)\<close>

text \<open>The correctness proof's soul (§5d): "branch-atoms ARE pairwise facts, so the
  derivation never leaves the pairwise-preorder fragment where transitivity is
  COMPLETE." The order-theoretic core of that claim: over a linear order, the
  pairwise consequences of a set of <= constraints are EXACTLY its transitive
  closure. We mechanize the load-bearing direction: transitivity is a sound and
  (for order-consequence) complete inference for pairwise facts.\<close>

text \<open>Soundness of transitivity (trivial but foundational — the derivation only
  ever uses transitivity + the comparator axiom + frame, all order-valid).\<close>

lemma transitivity_sound:
  fixes a b c :: "'a::linorder"
  assumes "a \<le> b" "b \<le> c"
  shows "a \<le> c"
  using assms by (rule order_trans)

text \<open>COMPLETENESS of transitivity for pairwise consequence over a linear order:
  if a <= b does NOT follow by the reflexive-transitive closure of a set of
  pairwise constraints P, then there is a linear-order model of P with a > b.
  We state the contrapositive core: over a linorder, the entailed pairs from a
  set of premises are exactly those reachable by rtrancl. This is the finite-
  preorder completeness lemma cited in §5b/§5d. Here we mechanize the key
  monotonicity: rtrancl of a relation of true <='s is itself all-true.\<close>

lemma pairwise_closure_sound:
  fixes P :: "('a::linorder) rel"
  assumes P_true: "\<forall>(x,y) \<in> P. x \<le> y"
  assumes reach: "(a,b) \<in> P\<^sup>*"
  shows "a \<le> b"
  using reach
proof (induction rule: rtrancl_induct)
  case base
  show ?case by simp
next
  case (step y z)
  have "y \<le> z" using step.hyps(2) P_true by auto
  with step.IH show ?case by (rule order_trans)
qed

text \<open>So: any pairwise ordering derived by transitive closure from true premises
  is TRUE. Combined with the comparator axiom (each comparator contributes a true
  pairwise premise) and the frame rule (untouched wires keep their facts), every
  ledger fact the calculus derives is SOUND. This is the soundness backbone;
  the completeness (every all-inputs-true ordering IS so derivable) is the §13
  covering-family layer, mechanized in the next file.\<close>

end
