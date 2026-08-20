theory BranchAtoms
  imports DischargeCalculus
begin

(* ============================================================================
   THEORY-LAYER, FILE (2): BRANCH-ATOM CLOSURE.

   Mechanizes the SOUL of the correctness proof (§5d):
     "Branch-atoms ARE pairwise facts, so the derivation never leaves the
      pairwise-preorder fragment where transitivity is COMPLETE."

   The two formal pillars:
   (A) A branch atom is a pairwise fact. When comparator (i,j) processes a config,
       it takes exactly one of two branches:
         Ox (no-swap):  the incoming values already had v i <= v j
         tx (swap):     the incoming had v j < v i, i.e. v j <= v i
       BOTH branch conditions are pairwise <= relations on the pre-comparator wires.
   (C) Case-2 resolution: WITHIN a fixed branch, min/max resolve to DEFINITE wires,
       so the output pairwise facts pull back to pairwise facts on the input. The
       "min/max introducing non-pairwise structure" danger (Bocher's flagged point,
       §5d CHECK 2) does NOT occur, because the branch fixes which wire is which.

   Author: Iyun (theory layer), on Heath's go-ahead. Builds on DischargeCalculus.
   Every lemma machine-checked before commit.
   ============================================================================ *)

section \<open>Branch conditions are pairwise facts (Pillar A)\<close>

text \<open>The no-swap branch condition Ox for comparator (i,j) on config v.\<close>
definition branch_Ox :: "comparator \<Rightarrow> ('a::linorder) config \<Rightarrow> bool" where
  "branch_Ox c v = (let (i,j) = c in v i \<le> v j)"

text \<open>The swap branch condition tx: the swap fires exactly when v j < v i,
  equivalently \<not>(v i \<le> v j). We record its pairwise form v j \<le> v i.\<close>
definition branch_tx :: "comparator \<Rightarrow> ('a::linorder) config \<Rightarrow> bool" where
  "branch_tx c v = (let (i,j) = c in v j \<le> v i)"

text \<open>EXHAUSTIVE and pairwise: every config satisfies Ox or tx (the Ox\<or>tx
  tautology, §5b) — and both are pairwise <= relations. This is the linearity
  of the order made explicit: the two branch atoms partition possibility-space,
  and each is a single pairwise fact.\<close>

lemma branch_exhaustive:
  fixes v :: "('a::linorder) config"
  shows "branch_Ox c v \<or> branch_tx c v"
  by (cases c) (auto simp: branch_Ox_def branch_tx_def)

text \<open>The two branches are jointly exhaustive; their overlap is exactly equality
  on the compared wires (v i = v j), where BOTH hold — harmless, since equal values
  make the two branch-outcomes identical.\<close>

lemma branch_overlap_is_equality:
  fixes v :: "('a::linorder) config"
  assumes "c = (i,j)" "branch_Ox c v" "branch_tx c v"
  shows "v i = v j"
  using assms by (auto simp: branch_Ox_def branch_tx_def)

section \<open>Within a branch, min/max resolve to a definite wire (Pillar C)\<close>

text \<open>The Case-2 resolution. In the no-swap branch (Ox: v i <= v j), the comparator
  leaves values in place: out_i = v i (the min IS v i) and out_j = v j (the max IS
  v j). So any pairwise fact about the OUTPUT wire i is a pairwise fact about the
  INPUT wire i — no min/max survives. This is why "relabeling preserves pairwise-
  ness" (§5d CHECK 2): the branch atom RESOLVES the min/max to a specific wire.\<close>

lemma Ox_resolves_min_max:
  fixes v :: "('a::linorder) config"
  assumes "c = (i,j)" "branch_Ox c v"
  shows "(apply_comp c v) i = v i" and "(apply_comp c v) j = v j"
  using assms by (auto simp: apply_comp_def branch_Ox_def min_def max_def)

text \<open>In the swap branch (tx: v j <= v i), the comparator swaps: out_i = v j (the
  min IS v j) and out_j = v i (the max IS v i). Again a definite wire — the min/max
  is resolved by the branch, output facts pull back to pairwise input facts.\<close>

lemma tx_resolves_min_max:
  fixes v :: "('a::linorder) config"
  assumes "c = (i,j)" "branch_tx c v"
  shows "(apply_comp c v) i = v j" and "(apply_comp c v) j = v i"
  using assms by (auto simp: apply_comp_def branch_tx_def min_def max_def)

section \<open>The closure theorem: the fragment is never left\<close>

text \<open>Consequence of Pillars A+C: after a comparator, in EITHER branch, each output
  wire's value equals SOME input wire's value (a definite one, fixed by the branch).
  So every pairwise relation among output wires is a pairwise relation among input
  wires. The derivation stays inside the pairwise-preorder fragment. We state it as:
  the output config, on the compared wires, is a permutation of the input values that
  is DETERMINED by the branch (identity under Ox, transposition under tx).\<close>

lemma output_is_definite_input_wire:
  fixes v :: "('a::linorder) config"
  assumes c: "c = (i,j)" and ij: "i \<noteq> j"
  shows "(branch_Ox c v \<longrightarrow>
            (apply_comp c v) i = v i \<and> (apply_comp c v) j = v j)
       \<and> (branch_tx c v \<longrightarrow>
            (apply_comp c v) i = v j \<and> (apply_comp c v) j = v i)"
proof (intro conjI impI)
  assume "branch_Ox c v"
  thus "(apply_comp c v) i = v i" using c by (simp add: Ox_resolves_min_max(1))
next
  assume "branch_Ox c v"
  thus "(apply_comp c v) j = v j" using c by (simp add: Ox_resolves_min_max(2))
next
  assume "branch_tx c v"
  thus "(apply_comp c v) i = v j" using c by (simp add: tx_resolves_min_max(1))
next
  assume "branch_tx c v"
  thus "(apply_comp c v) j = v i" using c by (simp add: tx_resolves_min_max(2))
qed

text \<open>THE BRANCH-ATOM CLOSURE (§5d soul, mechanized). Any pairwise ordering between
  two OUTPUT wires, in a fixed branch, is equal to a pairwise ordering between two
  (definite) INPUT wires. Concretely: a pairwise fact "out_i <= out_j" reduces, in
  each branch, to a pairwise fact on inputs — no non-pairwise (min/max) structure
  survives inside a context. Hence branch-atoms + wire-facts together form a
  closed pairwise-preorder fragment, where transitivity (DischargeCalculus.
  pairwise_closure_sound) is the complete inference.\<close>

theorem branch_atom_closure:
  fixes v :: "('a::linorder) config"
  assumes c: "c = (i,j)" and ij: "i \<noteq> j"
  shows "(apply_comp c v) i \<le> (apply_comp c v) j
           \<longleftrightarrow> (branch_Ox c v \<and> v i \<le> v j) \<or> (branch_tx c v \<and> v j \<le> v i)"
proof -
  have "branch_Ox c v \<or> branch_tx c v" by (rule branch_exhaustive)
  moreover
  { assume ox: "branch_Ox c v"
    hence "(apply_comp c v) i = v i" "(apply_comp c v) j = v j"
      using c by (auto simp: Ox_resolves_min_max)
    hence ?thesis using ox c by (auto simp: branch_Ox_def) }
  moreover
  { assume tx: "branch_tx c v"
    hence "(apply_comp c v) i = v j" "(apply_comp c v) j = v i"
      using c by (auto simp: tx_resolves_min_max)
    hence ?thesis using tx c by (auto simp: branch_tx_def) }
  ultimately show ?thesis by blast
qed

text \<open>Reading of branch_atom_closure: the OUTPUT pairwise fact (out_i <= out_j)
  holds iff, in whichever branch the input took, the corresponding INPUT pairwise
  fact holds. The comparator axiom (DischargeCalculus.comparator_axiom) says the LHS
  is ALWAYS true; and indeed the RHS is always true too, because in branch Ox we have
  v i <= v j by definition of Ox, and in branch tx we have v j <= v i by definition of
  tx — so both disjuncts' pairwise conditions are exactly the branch atoms themselves.
  The min/max never escapes the pairwise fragment. QED for Pillar C / §5d CHECK 2.\<close>


section \<open>The Bishop: parity is welded to ordering direction (Heath, mechanized)\<close>

text \<open>The PARITY of a branch: no-swap Ox is EVEN (False), swap tx is ODD (True) --
  the ``colour'' of the affine information the branch contributes.\<close>
definition branch_parity :: "comparator \<Rightarrow> ('a::linorder) config \<Rightarrow> bool" where
  "branch_parity c v = branch_tx c v"

definition asserts_forward :: "comparator \<Rightarrow> ('a::linorder) config \<Rightarrow> bool" where
  "asserts_forward c v = (let (i,j) = c in v i \<le> v j)"
definition asserts_reversed :: "comparator \<Rightarrow> ('a::linorder) config \<Rightarrow> bool" where
  "asserts_reversed c v = (let (i,j) = c in v j \<le> v i)"

text \<open>THE BISHOP (parity--direction lock). EVEN branch (Ox, no-swap) asserts FORWARD
  (v i \<le> v j); ODD branch (tx, swap) asserts REVERSED (v j \<le> v i). Parity and
  direction are one distinction, welded at MEASURE: a branch stays on its colour.\<close>
theorem bishop_parity_direction_lock:
  fixes v :: "('a::linorder) config"
  shows even_forward:  "branch_Ox c v \<longleftrightarrow> asserts_forward c v"
    and odd_reversed:  "branch_tx c v \<longleftrightarrow> asserts_reversed c v"
proof -
  show "branch_Ox c v \<longleftrightarrow> asserts_forward c v"
    by (cases c) (auto simp: branch_Ox_def asserts_forward_def)
  show "branch_tx c v \<longleftrightarrow> asserts_reversed c v"
    by (cases c) (auto simp: branch_tx_def asserts_reversed_def)
qed

text \<open>The EVEN branch (Ox) is EXACTLY the forward assertion; the ODD branch (tx) is
  EXACTLY the reversed assertion --- each colour IS its ordering direction, by
  definition. Off the diagonal (\<open>v i \<noteq> v j\<close>) exactly ONE colour holds (the branch is
  determined); ON the diagonal (\<open>v i = v j\<close>) both hold --- the harmless overlap
  (@{thm branch_overlap_is_equality}), the one square where the colours meet and the
  two branch-outcomes coincide. So the lock is: a branch's parity and the direction it
  asserts are the SAME fact, never independent.\<close>

text \<open>PRESERVATION: even (Ox) keeps forward facts forward (identity on the pair);
  odd (tx) keeps reversed facts reversed (transposition). The swap flips BOTH parity
  and direction together, so the lock is invariant under composition.\<close>
theorem bishop_preserved_by_comparator:
  fixes v :: "('a::linorder) config"
  assumes c: "c = (i,j)" and ij: "i \<noteq> j"
  shows "(branch_Ox c v \<longrightarrow> ((apply_comp c v) i \<le> (apply_comp c v) j \<longleftrightarrow> v i \<le> v j))
       \<and> (branch_tx c v \<longrightarrow> ((apply_comp c v) i \<le> (apply_comp c v) j \<longleftrightarrow> v j \<le> v i))"
proof (intro conjI impI)
  assume ox: "branch_Ox c v"
  hence "(apply_comp c v) i = v i" "(apply_comp c v) j = v j"
    using c by (auto simp: Ox_resolves_min_max)
  thus "(apply_comp c v) i \<le> (apply_comp c v) j \<longleftrightarrow> v i \<le> v j" by simp
next
  assume tx: "branch_tx c v"
  hence "(apply_comp c v) i = v j" "(apply_comp c v) j = v i"
    using c by (auto simp: tx_resolves_min_max)
  thus "(apply_comp c v) i \<le> (apply_comp c v) j \<longleftrightarrow> v j \<le> v i" by simp
qed

text \<open>Together: the affine information decomposes into two colours welded to the two
  ordering directions; no comparator moves a coupling off its colour. Heath's bishop,
  mechanized.\<close>


end
