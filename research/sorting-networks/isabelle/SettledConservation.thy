theory SettledConservation
  imports DischargeCalculus
begin

(* ============================================================================
   SETTLED-STATE CONSERVATION UNDER COMPARATORS
   (Heath's formulation, 2026-07-27; instrumented by Opus5.)

   A settled pair is never DESTROYED by a comparator -- it may only be RENAMED.
   Concretely, if (i,j) is settled before comparator (a,b), then after the
   comparator either (i,j) is still settled, or its image under the transposition
   a <-> b is settled.  This is why the settled COUNT is non-decreasing while the
   settled SET, read by wire index, appears to churn.

   Opus5's earlier "68,352 monotonicity violations" measured the SET by address
   and read a renaming as a loss.  Exhaustive recount over all reachable images:
     n=3..6, 162,139 non-idempotent moves, ZERO decreases of the settled COUNT;
     n=3..5,   3,313 moves, ZERO failures of the canonical relabel map below.
   ============================================================================ *)

definition img_step :: "comparator \<Rightarrow> ('a::linorder) config set \<Rightarrow> 'a config set" where
  "img_step c S = apply_comp c ` S"

definition settledS :: "('a::linorder) config set \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool" where
  "settledS S i j = (\<forall>v \<in> S. v i \<le> v j)"

text \<open>The relabel: the transposition induced by comparator (a,b).\<close>
definition swap_idx :: "comparator \<Rightarrow> nat \<Rightarrow> nat" where
  "swap_idx c x = (let (a,b) = c in if x = a then b else if x = b then a else x)"

lemma swap_idx_involutive: "swap_idx c (swap_idx c x) = x"
  by (cases c) (auto simp: swap_idx_def)

text \<open>Comparator semantics, unfolded on the three relevant positions.\<close>
lemma apply_comp_at:
  assumes "c = (a,b)" and "a \<noteq> b"
  shows "apply_comp c v a = min (v a) (v b)"
    and "apply_comp c v b = max (v a) (v b)"
    and "x \<noteq> a \<Longrightarrow> x \<noteq> b \<Longrightarrow> apply_comp c v x = v x"
  using assms by (auto simp: apply_comp_def)

text \<open>KEY: a pair untouched by the comparator keeps its settled status.\<close>
lemma settled_untouched:
  assumes "c = (a,b)" "a \<noteq> b"
      and "i \<noteq> a" "i \<noteq> b" "j \<noteq> a" "j \<noteq> b"
      and "settledS S i j"
    shows "settledS (img_step c S) i j"
  using assms by (auto simp: settledS_def img_step_def apply_comp_def)

text \<open>KEY: the comparator's own pair is settled afterwards, unconditionally.\<close>
lemma settled_comparator_pair:
  assumes "c = (a,b)" "a \<noteq> b"
  shows "settledS (img_step c S) a b"
  using assms by (auto simp: settledS_def img_step_def apply_comp_def min_def max_def)

text \<open>A pair with one leg on the comparator's low wire: min only decreases,
  so an upper bound is preserved.\<close>
lemma settled_low_leg:
  assumes "c = (a,b)" "a \<noteq> b" "j \<noteq> a" "j \<noteq> b"
      and "settledS S a j" and "settledS S b j"
  shows "settledS (img_step c S) a j"
  using assms by (auto simp: settledS_def img_step_def apply_comp_def min_def)

text \<open>Dually, the high wire carries the max, so a lower bound is preserved.\<close>
lemma settled_high_leg:
  assumes "c = (a,b)" "a \<noteq> b" "i \<noteq> a" "i \<noteq> b"
      and "settledS S i a" and "settledS S i b"
  shows "settledS (img_step c S) i b"
  using assms by (auto simp: settledS_def img_step_def apply_comp_def max_def)


text \<open>THE CANONICAL WITNESS.  Enumeration over all reachable images (n=5,
  13,108 settled-pair/comparator instances) shows the target pair is DETERMINED:
    - pair untouched by the comparator       -> itself
    - low end on the comparator's LOW wire   -> itself   (min flows down)
    - high end on the comparator's HIGH wire -> itself   (max flows up)
    - low end on the comparator's HIGH wire  -> swapped
    - high end on the comparator's LOW wire  -> swapped
  A settled pair equal to the comparator itself cannot occur: that comparator
  would be idempotent.\<close>

definition carry :: "comparator \<Rightarrow> nat \<times> nat \<Rightarrow> nat \<times> nat" where
  "carry c p =
     (let (a,b) = c; (i,j) = p in
        if i = b \<or> j = a
        then (swap_idx c i, swap_idx c j)
        else p)"

lemma carry_untouched:
  assumes "c = (a,b)" "i \<noteq> a" "i \<noteq> b" "j \<noteq> a" "j \<noteq> b"
  shows "carry c (i,j) = (i,j)"
  using assms by (auto simp: carry_def)

text \<open>SETTLED CONSERVATION (TIGHT).  No side conditions: a settled pair is
  carried to @{term carry}, full stop.  Verified by exhaustive enumeration over
  ARBITRARY subsets (n=4, 165,594 instances, zero counterexamples) before proof.

  The proof is pointwise.  Fix v in S; write w = apply_comp c v.  In each case the
  goal reduces to a min/max inequality that follows from the single premise
  @{term "v i \<le> v j"} together with the definitional facts about min and max.\<close>
text \<open>FLAT PROOF (2026-07-28).  The original proof used a hierarchical
  ''consider'' (A) i=b | (B) j=a | (C) neither, with hand-nested ''cases'' inside each
  and ''auto'' per leaf.  Porting this theorem to Lean 4 revealed the case-split is
  really a UNIFORM 2^4 explosion on the four index equalities (i=a, i=b, j=a, j=b),
  every leaf a min/max fact discharged by arithmetic.  We rewrote the Isabelle proof in
  that flatter form: ONE 4-way ''cases'' chain plus ONE ''auto'' over the definitional
  lemmas, replacing the ~30-line hierarchical proof with a ~6-line pointwise key.  Same
  theorem, same tightness (verified by exhaustive enumeration, n=4, 165,594 instances),
  cleaner shape learned from the dual formalization.\<close>
theorem settled_conserved:
  assumes c: "c = (a,b)" and ab: "a < b"
      and s: "settledS S i j"
  shows "settledS (img_step c S) (fst (carry c (i,j))) (snd (carry c (i,j)))"
proof -
  have key: "\<And>v. v \<in> S \<Longrightarrow>
       apply_comp c v (fst (carry c (i,j))) \<le> apply_comp c v (snd (carry c (i,j)))"
    using s ab c
    by (cases "i = a"; cases "i = b"; cases "j = a"; cases "j = b")
       (auto simp: settledS_def carry_def swap_idx_def apply_comp_def min_def max_def)
  show ?thesis by (auto simp: settledS_def img_step_def key)
qed

(* ============================================================================
   IDEMPOTENCY IS A PROPERTY OF A POSITION IN A NETWORK, NOT OF A COMPARATOR
   (Heath, 2026-07-27: "a comparator can only be idempotent in a network".)

   A comparator has no intrinsic idempotency.  (2,3) swaps or does not swap
   depending on the reachable image at that point, and the reachable image is
   determined by the PREFIX of the network before it.  Formalising this closes a
   real methodological hazard: evaluating idempotency on an ARBITRARY config set
   asks a question about states no execution produces.  Opus5 reported 13,578
   "counterexamples" to strict progress that were all of this form -- witnesses
   drawn from unreachable sets.  Enumerating INPUTS is merely exponential;
   enumerating unreachable INTERNAL STATES is incorrect.
   ============================================================================ *)

text \<open>The reachable image of a network: everything the prefix can produce.\<close>
definition reach :: "network \<Rightarrow> ('a::linorder) config set" where
  "reach net = range (run net)"

text \<open>Idempotency AT A POSITION: comparator k of net does nothing to the image
  that the first k comparators produce.\<close>
definition idem_at :: "('a::linorder) itself \<Rightarrow> network \<Rightarrow> nat \<Rightarrow> bool" where
  "idem_at TYPE('a) net k =
     (img_step (net ! k) (reach (take k net) :: 'a config set) = reach (take k net))"

lemma reach_Nil: "reach [] = range (\<lambda>v. v)"
  by (simp add: reach_def)

text \<open>The image after one more comparator is the step of the image before it.\<close>
lemma run_snoc: "run (net @ [c]) v = apply_comp c (run net v)"
  by (induct net arbitrary: v) auto

lemma reach_snoc:
  "reach (net @ [c]) = img_step c (reach net)"
  by (auto simp: reach_def img_step_def run_snoc image_image)

text \<open>Hence idempotency at the last position says exactly that appending the
  comparator does not change the reachable image.\<close>
lemma idem_at_last:
  assumes "net' = net @ [c]"
  shows "idem_at TYPE('a::linorder) net' (length net)
           \<longleftrightarrow> (reach net' :: 'a config set) = reach net"
  using assms by (simp add: idem_at_def reach_snoc)

text \<open>A comparator is idempotent at a position exactly when its own pair is
  already settled in the image reaching it -- no vector can witness a swap.\<close>
text \<open>A comparator does nothing to an image exactly when its own pair is already
  settled there.  Forward: if settled, every vector already has v a <= v b, so
  apply_comp is the identity on S.  Backward: if the image is unchanged, then
  every image element has a <= b (because apply_comp always makes it so), and the
  image IS S -- so S itself is settled.\<close>
lemma idem_iff_settled:
  assumes c: "c = (a,b)" and ab: "a < b"
  shows "img_step c S = S \<longleftrightarrow> settledS S a b"
proof
  assume "settledS S a b"
  hence "\<And>v. v \<in> S \<Longrightarrow> apply_comp c v = v"
    using c ab by (auto simp: settledS_def apply_comp_def min_def max_def)
  thus "img_step c S = S" by (auto simp: img_step_def)
next
  assume step: "img_step c S = S"
  \<comment> \<open>every element of the image satisfies a <= b, by construction\<close>
  have img_ok: "\<And>w. w \<in> img_step c S \<Longrightarrow> w a \<le> w b"
    using c ab by (auto simp: img_step_def apply_comp_def min_def max_def)
  show "settledS S a b"
    using step img_ok by (auto simp: settledS_def)
qed

(* ============================================================================
   TRANSITIVITY -- the third inference the generator needs.

   carry + own-pair is NOT complete for the settled set: measured gaps of
   4/10/18/46 pairs on n4_optimal / n5_classic / n6_classic / n8_batcher.
   Every gap closes by chaining through the comparator's own pair.  With this
   lemma the three rules (conserve, establish, chain) are complete.
   ============================================================================ *)

lemma settled_trans:
  assumes "settledS S i j" and "settledS S j k"
  shows "settledS S i k"
  using assms by (auto simp: settledS_def order_trans)

text \<open>The generator's three inference rules, named for citation in emitted proofs:
    CONSERVE  = @{thm settled_conserved}     (a settled pair survives, renamed)
    ESTABLISH = @{thm settled_comparator_pair} (the comparator settles its own pair)
    CHAIN     = @{thm settled_trans}          (transitivity)\<close>

text \<open>Sortedness of an image is exactly settledness of all adjacent pairs.\<close>
definition img_sorted :: "nat \<Rightarrow> ('a::linorder) config set \<Rightarrow> bool" where
  "img_sorted n S = (\<forall>k < n - 1. settledS S k (Suc k))"

lemma img_sorted_intro:
  assumes "\<And>k. k < n - 1 \<Longrightarrow> settledS S k (Suc k)"
  shows "img_sorted n S"
  using assms by (simp add: img_sorted_def)

(* ============================================================================
   SET-LEVEL CONSERVATION -- the shape the progress rule actually needs.

   The pairwise theorem @{thm settled_conserved} names a target for each settled
   pair.  It is NOT injective: with c=(1,2), both (0,1) and (0,2) map to targets
   that coincide (1,800 collisions at n=5).  So a cardinality argument cannot go
   through pairwise.  The statement that DOES hold, with zero counterexamples
   over all reachable images at n=3,4,5 (3,313 non-idempotent moves):

       settled(step c S)  >=  carry c ` settled(S)  Un  {c}

   Measured before formalising.  The weaker-looking "settled(S) <= settled(step c S)"
   is FALSE (963 failures at n=5): pairs move, they do not stay.
   ============================================================================ *)

definition settled_set :: "nat \<Rightarrow> ('a::linorder) config set \<Rightarrow> (nat \<times> nat) set" where
  "settled_set n S = {(i,j). i < n \<and> j < n \<and> i \<noteq> j \<and> settledS S i j}"

lemma settled_setI:
  "i < n \<Longrightarrow> j < n \<Longrightarrow> i \<noteq> j \<Longrightarrow> settledS S i j \<Longrightarrow> (i,j) \<in> settled_set n S"
  by (simp add: settled_set_def)

text \<open>Carrying preserves index bounds, so the image stays inside the pair space.\<close>
lemma carry_bounds:
  assumes "c = (a,b)" "a < n" "b < n" "i < n" "j < n"
  shows "fst (carry c (i,j)) < n \<and> snd (carry c (i,j)) < n"
  using assms by (auto simp: carry_def swap_idx_def)

lemma carry_neq:
  assumes "c = (a,b)" "a < b" "i \<noteq> j"
  shows "fst (carry c (i,j)) \<noteq> snd (carry c (i,j))"
  using assms by (auto simp: carry_def swap_idx_def)

text \<open>SET-LEVEL CONSERVATION.  Everything the previous settled set carries to,
  together with the comparator's own pair, is settled afterwards.  This is the
  pointwise theorem lifted; no new mathematics, the correct quantifier order.\<close>
theorem settled_set_conserved:
  assumes c: "c = (a,b)" and ab: "a < b" and bn: "b < n"
  shows "(\<lambda>p. carry c p) ` settled_set n S \<union> {(a,b)}
           \<subseteq> settled_set n (img_step c S)"
proof
  fix q assume "q \<in> (\<lambda>p. carry c p) ` settled_set n S \<union> {(a,b)}"
  then consider (carried) p where "p \<in> settled_set n S" "q = carry c p"
              | (own) "q = (a,b)" by auto
  then show "q \<in> settled_set n (img_step c S)"
  proof cases
    case carried
    obtain i j where p: "p = (i,j)" by (cases p)
    have "i < n" "j < n" "i \<noteq> j" "settledS S i j"
      using carried p by (auto simp: settled_set_def)
    moreover have "settledS (img_step c S) (fst (carry c (i,j))) (snd (carry c (i,j)))"
      using c ab calculation by (rule_tac settled_conserved) auto
    ultimately show ?thesis
      using carried p c ab bn
      by (auto simp: settled_set_def carry_def swap_idx_def)
  next
    case own
    have "settledS (img_step c S) a b"
      using c ab by (intro settled_comparator_pair) auto
    thus ?thesis using own ab bn by (auto simp: settled_set_def)
  qed
qed

(* ============================================================================
   COLLISION IS DISCHARGE

   Heath: "you are proving that pairwise-symmetric discharge produces a fact."

   MEASURED FIRST (n=3,4,5, all 3,313 non-idempotent moves over reachable images):
     collisions in carry  ==  #{ {p, swap p} : both settled before }
     totals matched exactly: 2=2, 58=58, 2134=2134.  Not an inequality -- an identity.

   A collision means the same target is reached from p by the identity route and
   from swap(p) by the transposed route.  In branch language: the fact holds on
   the g=0 branch AND on the g=1 branch, which is exactly the discharge condition.
   So a collision does not LOSE a pair; it PRODUCES an unconditional one.
   ============================================================================ *)

definition swap_pair :: "comparator \<Rightarrow> nat \<times> nat \<Rightarrow> nat \<times> nat" where
  "swap_pair c p = (swap_idx c (fst p), swap_idx c (snd p))"

lemma swap_pair_involutive: "swap_pair c (swap_pair c p) = p"
  by (cases c; cases p) (simp add: swap_pair_def swap_idx_def)

text \<open>BOTH BRANCHES.  If a pair and its transpose are both settled before the
  comparator, the carried pair is settled after -- by the identity route and by
  the transposed route alike.  This is discharge, stated without atoms: the two
  routes are the two branches.\<close>
lemma both_branches_discharge:
  assumes c: "c = (a,b)" and ab: "a < b"
      and p:  "settledS S i j"
      and sp: "settledS S (swap_idx c i) (swap_idx c j)"
  shows "settledS (img_step c S) (fst (carry c (i,j))) (snd (carry c (i,j)))"
  using c ab p by (rule settled_conserved)

text \<open>COLLISION.  Distinct pairs share a carry target only by being transposes:
  carry either fixes a pair or applies the transposition, so two different sources
  with one target must differ by that transposition.\<close>
lemma carry_collision_transpose:
  assumes c: "c = (a,b)" and ab: "a < b"
      and eq: "carry c p = carry c q" and ne: "p \<noteq> q"
  shows "q = swap_pair c p \<or> p = swap_pair c q"
proof (cases p; cases q)
  fix i j k l assume p: "p = (i,j)" and q: "q = (k,l)"
  show ?thesis
    using eq ne c ab p q
    by (auto simp: carry_def swap_pair_def swap_idx_def split: if_splits)
qed

text \<open>Consequently the carry image of a settled set loses exactly one element per
  transpose-pair it contains: two sources, one target.\<close>
lemma transpose_pair_merges:
  assumes c: "c = (a,b)" and ab: "a < b"
      and tp: "q = swap_pair c p" and ne: "p \<noteq> q"
      and touch: "fst p = b \<or> snd p = a"
  shows "carry c q = carry c p \<or> carry c q = p"
  using assms by (cases p) (auto simp: carry_def swap_pair_def swap_idx_def)

(* ============================================================================
   STRICT PROGRESS -- assembled from proved lemmas, no assumed compensation.

   The earlier attempt assumed its own conclusion.  The correct structure came
   from measuring what actually happens to the settled set (n=3,4,5, all 3,313
   non-idempotent moves over reachable images):

     * a pair p whose TRANSPOSE swap(p) is also settled: BOTH survive
       (2134/2134 at n=5).  carry collides on them, but the SET does not shrink.
     * a pair p with no settled transpose: p may be lost, but carry c p is gained.
       Lost pairs NEVER have a settled swap-partner: 0 of 1,250 at n=5.
     * the comparator's own pair (a,b) is fresh -- not settled before
       (@{thm idem_iff_settled}), settled after (@{thm settled_comparator_pair}),
       and not a carry-image of anything settled (@{thm own_pair_fresh}).

   So carry is injective ON THE LOST SET, the survivors survive, and (a,b) is a
   strict addition.  No compensation argument is required.
   ============================================================================ *)

definition carry_img :: "comparator \<Rightarrow> (nat \<times> nat) set \<Rightarrow> (nat \<times> nat) set" where
  "carry_img c P = (\<lambda>p. carry c p) ` P"

text \<open>The comparator's own pair is not the carry-image of anything settled: carry
  fixes or transposes, so a source would have to be (a,b) or (b,a), and neither is
  settled when the comparator is non-idempotent.\<close>
(* --------------------------------------------------------------------------
   THE REACHABILITY INGREDIENT.

   own_pair_fresh needs: the REVERSE pair (b,a) is never settled, for a<b.
   That is FALSE for arbitrary config sets -- 144 counterexamples at n=3, e.g.
   S = {(1,0,0)} with c = (0,1).  It is true for REACHABLE images, and the reason
   is a fixed point: the sorted 0-1 vectors are unchanged by every comparator, so
   they persist in every reachable image, and one of them witnesses v a < v b.
   Verified: n=3,4,5 (7/44/581 reachable images), zero pairs a<b lacking a witness.
   -------------------------------------------------------------------------- *)

definition step_vec :: "nat \<Rightarrow> nat \<Rightarrow> bool" where
  "step_vec t i = (i \<ge> t)"

text \<open>A threshold vector is a fixed point of every comparator: it is already sorted.\<close>
lemma step_vec_fixed:
  assumes "a < b"
  shows "apply_comp (a,b) (step_vec t) = step_vec t"
proof
  fix x show "apply_comp (a,b) (step_vec t) x = step_vec t x"
    using assms by (cases "x = a"; cases "x = b")
                   (auto simp: apply_comp_def step_vec_def min_def max_def)
qed

text \<open>Ascending networks: every comparator has its low wire first.  This is the
  standing convention (a<b) and it is what makes threshold vectors fixed points.\<close>
definition ascending :: "network \<Rightarrow> bool" where
  "ascending net = (\<forall>c \<in> set net. fst c < snd c)"

text \<open>Threshold vectors persist through any ascending network.\<close>
lemma step_vec_run:
  assumes "ascending net"
  shows "run net (step_vec t) = step_vec t"
  using assms
proof (induct net)
  case Nil thus ?case by simp
next
  case (Cons c cs)
  obtain a b where c: "c = (a,b)" by (cases c)
  hence "a < b" using Cons.prems by (simp add: ascending_def)
  hence "apply_comp c (step_vec t) = step_vec t"
    using c by (simp add: step_vec_fixed)
  thus ?case using Cons by (simp add: ascending_def)
qed

lemma step_vec_in_reach:
  assumes "ascending net"
  shows "step_vec t \<in> reach net"
proof -
  have "run net (step_vec t) = step_vec t" using assms by (rule step_vec_run)
  thus ?thesis unfolding reach_def by (metis rangeI)
qed

text \<open>THE INGREDIENT: over the image of an ascending network, the reverse pair is
  never settled -- the threshold vector with boundary between a and b witnesses it.\<close>
lemma reverse_never_settled:
  assumes ab: "a < b" and asc: "ascending net"
  shows "\<not> settledS (reach net :: (nat \<Rightarrow> bool) set) b a"
proof -
  have inr: "step_vec b \<in> (reach net :: (nat \<Rightarrow> bool) set)"
    using asc by (rule step_vec_in_reach)
  show ?thesis
  proof
    assume rev: "settledS (reach net :: (nat \<Rightarrow> bool) set) b a"
    have "step_vec b b \<le> step_vec b a"
      using rev inr unfolding settledS_def by blast
    moreover have "step_vec b b" by (simp add: step_vec_def)
    moreover have "\<not> step_vec b a" using ab by (simp add: step_vec_def)
    ultimately show False by simp
  qed
qed

text \<open>Pinned to the boolean config type, matching @{thm reverse_never_settled}:
  the 0-1 principle makes that the operative instance, and the threshold-vector
  witness lives there.\<close>
lemma own_pair_fresh:
  fixes S :: "(nat \<Rightarrow> bool) set"
  assumes c: "c = (a,b)" and ab: "a < b" and uns: "\<not> settledS S a b"
      and Sdef: "S = reach net" and asc: "ascending net"
  shows "(a,b) \<notin> carry_img c (settled_set n S)"
proof
  assume "(a,b) \<in> carry_img c (settled_set n S)"
  then obtain p where p: "p \<in> settled_set n S" "carry c p = (a,b)"
    by (auto simp: carry_img_def)
  obtain i j where ij: "p = (i,j)" by (cases p)
  hence sij: "settledS S i j" using p by (auto simp: settled_set_def)
  have "(i,j) = (a,b) \<or> (i,j) = (b,a)"
    using p ij c ab by (auto simp: carry_def swap_idx_def split: if_splits)
  thus False
  proof
    assume "(i,j) = (a,b)" thus False using sij uns by simp
  next
    assume "(i,j) = (b,a)"
    hence "settledS S b a" using sij by simp
    with Sdef have "settledS (reach net :: (nat \<Rightarrow> bool) set) b a" by simp
    thus False using reverse_never_settled[OF ab asc] by simp
  qed
qed

text \<open>Everything settled before is accounted for after: either it survives, or
  its carry-image is settled.  This is @{thm settled_conserved} read as a
  statement about the settled SET.\<close>
lemma settled_accounted:
  assumes c: "c = (a,b)" and ab: "a < b" and bn: "b < n"
      and mem: "(i,j) \<in> settled_set n S"
  shows "carry c (i,j) \<in> settled_set n (img_step c S)"
proof -
  have "i < n" "j < n" "i \<noteq> j" "settledS S i j"
    using mem by (auto simp: settled_set_def)
  moreover have
    "settledS (img_step c S) (fst (carry c (i,j))) (snd (carry c (i,j)))"
    using c ab calculation by (rule_tac settled_conserved) auto
  ultimately show ?thesis using c ab bn
    by (auto simp: settled_set_def carry_def swap_idx_def)
qed

text \<open>STRICT PROGRESS.  A non-idempotent comparator strictly increases the settled
  count.  The carry image accounts for every prior settled pair; the comparator's
  own pair is settled afterwards and lies outside that image; hence the settled set
  afterwards strictly contains an injective image of the one before.\<close>
(* --------------------------------------------------------------------------
   THE SURVIVOR MAP.

   strict_progress previously ASSUMED inj_on (carry c).  That hypothesis is FALSE
   in general -- 1,800 collisions measured at n=5.  The collisions are always
   between a pair carry FIXES and a pair carry MOVES landing on the same target,
   and in every such case the moved pair ALSO survives at its own address
   (1800/1800 at n=5).  So the right map is not carry but:

       phi p  =  p            if p is still settled afterwards
                 carry c p    otherwise

   Measured over all reachable images at n=3,4,5 (3,313 non-idempotent moves):
     phi lands in the new settled set          0 failures
     phi is INJECTIVE                          0 failures
     (a,b) is not in phi's image               0 failures
   -------------------------------------------------------------------------- *)

definition phi :: "comparator \<Rightarrow> (nat \<Rightarrow> bool) set \<Rightarrow> nat
                    \<Rightarrow> nat \<times> nat \<Rightarrow> nat \<times> nat" where
  "phi c S n p = (if p \<in> settled_set n (img_step c S) then p else carry c p)"

text \<open>@{term phi} lands in the new settled set: either the pair survived (first
  branch, immediate) or it did not, and then @{thm settled_accounted} places its
  carry-image there.\<close>
lemma phi_into_after:
  assumes c: "c = (a,b)" and ab: "a < b" and bn: "b < n"
      and mem: "p \<in> settled_set n S"
  shows "phi c S n p \<in> settled_set n (img_step c S)"
proof (cases "p \<in> settled_set n (img_step c S)")
  case True thus ?thesis by (simp add: phi_def)
next
  case False
  obtain i j where ij: "p = (i,j)" by (cases p)
  have "carry c (i,j) \<in> settled_set n (img_step c S)"
    using c ab bn mem ij by (simp add: settled_accounted)
  thus ?thesis using False ij by (simp add: phi_def)
qed

text \<open>A pair that FALLS (settled before, not after) must have been moved by the
  comparator: if carry fixed it, @{thm settled_conserved} would have kept it.\<close>
lemma fallen_is_moved:
  assumes c: "c = (a,b)" and ab: "a < b" and bn: "b < n"
      and mem: "p \<in> settled_set n S"
      and fell: "p \<notin> settled_set n (img_step c S)"
  shows "carry c p \<noteq> p"
proof
  assume "carry c p = p"
  obtain i j where ij: "p = (i,j)" by (cases p)
  have "carry c (i,j) \<in> settled_set n (img_step c S)"
    using c ab bn mem ij by (simp add: settled_accounted)
  thus False using \<open>carry c p = p\<close> ij fell by simp
qed

text \<open>@{term carry} is INJECTIVE ON THE PAIRS IT MOVES -- purely combinatorial,
  no config set involved.  Verified at n=4,5,6: no comparator has a non-injective
  carry on its moved set.\<close>
lemma carry_inj_on_moved:
  assumes c: "c = (a,b)" and ab: "a < b"
  shows "inj_on (carry c) {p. carry c p \<noteq> p}"
proof (rule inj_onI)
  fix p q assume p: "p \<in> {p. carry c p \<noteq> p}" and q: "q \<in> {p. carry c p \<noteq> p}"
             and eq: "carry c p = carry c q"
  obtain i j where ij: "p = (i,j)" by (cases p)
  obtain k l where kl: "q = (k,l)" by (cases q)
  have mp: "i = b \<or> j = a" using p ij c by (auto simp: carry_def split: if_splits)
  have mq: "k = b \<or> l = a" using q kl c by (auto simp: carry_def split: if_splits)
  have "carry c (i,j) = (swap_idx c i, swap_idx c j)" using mp c by (auto simp: carry_def)
  moreover have "carry c (k,l) = (swap_idx c k, swap_idx c l)" using mq c by (auto simp: carry_def)
  ultimately have "(swap_idx c i, swap_idx c j) = (swap_idx c k, swap_idx c l)"
    using eq ij kl by simp
  hence "swap_idx c i = swap_idx c k" and "swap_idx c j = swap_idx c l" by auto
  hence "i = k" and "j = l" by (metis swap_idx_involutive)+
  thus "p = q" using ij kl by simp
qed

lemma inj_on_fallen:
  assumes c: "c = (a,b)" and ab: "a < b" and bn: "b < n"
  shows "inj_on (carry c) {q \<in> settled_set n S. q \<notin> settled_set n (img_step c S)}"
proof (rule inj_onI)
  fix p q
  assume p: "p \<in> {q \<in> settled_set n S. q \<notin> settled_set n (img_step c S)}"
     and q: "q \<in> {q \<in> settled_set n S. q \<notin> settled_set n (img_step c S)}"
     and eq: "carry c p = carry c q"
  have "carry c p \<noteq> p" using fallen_is_moved[OF c ab bn, of p S] p by simp
  moreover have "carry c q \<noteq> q" using fallen_is_moved[OF c ab bn, of q S] q by simp
  ultimately have "p \<in> {r. carry c r \<noteq> r}" and "q \<in> {r. carry c r \<noteq> r}" by auto
  thus "p = q" using inj_onD[OF carry_inj_on_moved[OF c ab] eq] by simp
qed

text \<open>A FALLEN pair's carry-image was NOT settled beforehand.  If it had been,
  @{thm settled_accounted} would place ITS carry-image in the new settled set --
  and carry is involutive on moved pairs, so that image is the fallen pair itself,
  contradicting that it fell.  Measured: 0 of 1,294 fallen pairs at n=4,5.\<close>
(* --------------------------------------------------------------------------
   OPEN: fallen_image_not_prior / surv_not_image_of_fallen.

   CLAIM (measured, not yet proved): if q is settled before a comparator and NOT
   after, then carry c q was not settled before either.  Hence a fallen pair's
   image can never be a "survivor" (settled both before and after), which is the
   surv_not_img side condition of phi_inj.

   Evidence: 0 of 1,294 fallen pairs at n=4,5 had a previously-settled image; and
   for every fallen q, carry c q IS settled afterwards (1250/1250 at n=5).

   Proof route, established but not yet mechanised:
     - the INVOLUTION argument is DEAD.  carry maps a MOVED pair to a FIXED pair
       (70 such cases at n=5), so carry (carry q) = q does not hold in general.
     - the working argument is semantic.  For q = (i,a): settled before means
       w_i <= w_a everywhere; q falls exactly when some vector has w_i > w_b,
       since wire a takes the min.  carry q = (i,b) settled before would demand
       w_i <= w_b everywhere -- contradicting that witness.
     - two degenerate cases must be excluded first, and both facts are already in
       this file: q = (x,x) by settled_set_def's i /= j, and q = (b,a) by
       reverse_never_settled (needs Sdef and asc threaded through).
   -------------------------------------------------------------------------- *)

(* --------------------------------------------------------------------------
   FALLEN-IMAGE, factored into three layers.

   LAYER 1 turns the future-tense hypothesis ("q fell") into a present-tense
   OBJECT (a witness vector).  LAYER 2 is the comparator's pointwise arithmetic,
   no sets involved.  LAYER 3 is linear arithmetic on that one vector.  Past the
   layer-1 door, settledS is never mentioned again -- which is what stops the
   simplifier wandering across four unfolded definitions.

   Measured over ARBITRARY subsets at n=4 before proving: 9,792 instances of the
   two branches, zero violations.  Reachability is not needed for the arithmetic.
   -------------------------------------------------------------------------- *)

text \<open>LAYER 1.  A pair that falls hands out a witness vector.\<close>
lemma fallen_witness:
  assumes "settledS S i j" and "\<not> settledS (img_step c S) i j"
  shows "\<exists>v \<in> S. \<not> (apply_comp c v i \<le> apply_comp c v j)"
  using assms by (auto simp: settledS_def img_step_def)

text \<open>LAYER 3, low branch.  q = (i,a): wire a takes the min, so falling forces a
  vector with v i > v b, and that same vector refutes (i,b) beforehand.\<close>
lemma fallen_low_image:
  assumes c: "c = (a,b)" and ab: "a < b" and ia: "i \<noteq> a" and ib: "i \<noteq> b"
      and prior: "settledS S i a"
      and fell: "\<not> settledS (img_step c S) i a"
  shows "\<not> settledS S i b"
proof -
  obtain v where v: "v \<in> S" and bad: "\<not> (apply_comp c v i \<le> apply_comp c v a)"
    using fallen_witness[OF prior fell] by blast
  have vi: "apply_comp c v i = v i" using c ia ib by (simp add: apply_comp_def)
  have va: "apply_comp c v a = min (v a) (v b)" using c ab by (simp add: apply_comp_def)
  from bad vi va have "\<not> (v i \<le> min (v a) (v b))" by simp
  moreover have "v i \<le> v a" using prior v by (simp add: settledS_def)
  ultimately have "\<not> (v i \<le> v b)" by (simp add: min_def split: if_splits)
  thus ?thesis using v by (auto simp: settledS_def)
qed

text \<open>LAYER 3, high branch.  q = (b,j): wire b takes the max, so falling forces a
  vector with v a > v j, refuting (a,j) beforehand.\<close>
lemma fallen_high_image:
  assumes c: "c = (a,b)" and ab: "a < b" and ja: "j \<noteq> a" and jb: "j \<noteq> b"
      and prior: "settledS S b j"
      and fell: "\<not> settledS (img_step c S) b j"
  shows "\<not> settledS S a j"
proof -
  obtain v where v: "v \<in> S" and bad: "\<not> (apply_comp c v b \<le> apply_comp c v j)"
    using fallen_witness[OF prior fell] by blast
  have vj: "apply_comp c v j = v j" using c ja jb by (simp add: apply_comp_def)
  have vb: "apply_comp c v b = max (v a) (v b)" using c ab by (simp add: apply_comp_def)
  from bad vj vb have "\<not> (max (v a) (v b) \<le> v j)" by simp
  moreover have "v b \<le> v j" using prior v by (simp add: settledS_def)
  ultimately have "\<not> (v a \<le> v j)" by (simp add: max_def split: if_splits)
  thus ?thesis using v by (auto simp: settledS_def)
qed

text \<open>ASSEMBLED: a fallen pair's carry-image was not settled beforehand.  The two
  branches are exactly @{thm fallen_low_image} and @{thm fallen_high_image}; the
  degenerate cases are excluded by facts already present -- q = (x,x) by
  @{text settled_set_def}'s i \<noteq> j, and q = (b,a) by @{thm reverse_never_settled}.\<close>
lemma fallen_image_not_prior:
  fixes S :: "(nat \<Rightarrow> bool) set"
  assumes c: "c = (a,b)" and ab: "a < b" and bn: "b < n"
      and Sdef: "S = reach net" and asc: "ascending net"
      and mem: "q \<in> settled_set n S"
      and fell: "q \<notin> settled_set n (img_step c S)"
    shows "carry c q \<notin> settled_set n S"
proof -
  obtain i j where ij: "q = (i,j)" by (cases q)
  have neq: "i \<noteq> j" using mem ij by (simp add: settled_set_def)
  have sq: "settledS S i j" using mem ij by (simp add: settled_set_def)
  have nsq: "\<not> settledS (img_step c S) i j"
    using fell mem ij by (auto simp: settled_set_def)
  have moved: "carry c q \<noteq> q" by (rule fallen_is_moved[OF c ab bn mem fell])
  have leg: "i = b \<or> j = a" using moved ij c by (auto simp: carry_def split: if_splits)
  have notrev: "\<not> (i = b \<and> j = a)"
  proof
    assume "i = b \<and> j = a"
    hence "settledS S b a" using sq by simp
    thus False using reverse_never_settled[OF ab asc] Sdef by simp
  qed
  show ?thesis
  proof (cases "j = a")
    case True
    hence ib: "i \<noteq> b" using notrev by simp
    have ia: "i \<noteq> a" using neq ij True by simp
    have "carry c q = (i,b)" using ij True c ia ib by (simp add: carry_def swap_idx_def)
    moreover have "\<not> settledS S i b"
      using fallen_low_image[OF c ab ia ib] sq nsq True by simp
    ultimately show ?thesis by (simp add: settled_set_def)
  next
    case False
    hence ib: "i = b" using leg by simp
    have ja: "j \<noteq> a" using False by simp
    have jb: "j \<noteq> b" using neq ij ib by simp
    have "carry c q = (a,j)" using ij ib ja jb c by (simp add: carry_def swap_idx_def)
    moreover have "\<not> settledS S a j"
      using fallen_high_image[OF c ab ja jb] sq nsq ib by simp
    ultimately show ?thesis by (simp add: settled_set_def)
  qed
qed

text \<open>Hence the @{text surv_not_img} side condition used below: a survivor is
  settled BEFORE and after; a fallen pair's image was not settled before.\<close>
lemma surv_not_image_of_fallen:
  fixes S :: "(nat \<Rightarrow> bool) set"
  assumes c: "c = (a,b)" and ab: "a < b" and bn: "b < n"
      and Sdef: "S = reach net" and asc: "ascending net"
      and qmem: "q \<in> settled_set n S" and qfell: "q \<notin> settled_set n (img_step c S)"
      and rmem: "r \<in> settled_set n S"
  shows "carry c q \<noteq> r"
  using fallen_image_not_prior[OF c ab bn Sdef asc qmem qfell] rmem by auto

text \<open>PHI IS INJECTIVE.  Three cases, and the enumeration (n=5, 3,160 moves) shows
  the two non-trivial ones never occur: a fallen pair's carry-image is never a
  survivor, and carry is injective on the fallen set.\<close>
lemma phi_inj:
  assumes c: "c = (a,b)" and ab: "a < b" and bn: "b < n"
      and surv_not_img: "\<And>q r. q \<in> settled_set n S
             \<Longrightarrow> q \<notin> settled_set n (img_step c S)
             \<Longrightarrow> r \<in> settled_set n S
             \<Longrightarrow> r \<in> settled_set n (img_step c S)
             \<Longrightarrow> carry c q \<noteq> r"
      and inj_fallen: "inj_on (carry c)
             {q \<in> settled_set n S. q \<notin> settled_set n (img_step c S)}"
  shows "inj_on (phi c S n) (settled_set n S)"
proof (rule inj_onI)
  fix p q assume p: "p \<in> settled_set n S" and q: "q \<in> settled_set n S"
             and eq: "phi c S n p = phi c S n q"
  let ?A = "settled_set n (img_step c S)"
  consider (ss) "p \<in> ?A" "q \<in> ?A"
         | (sf) "p \<in> ?A" "q \<notin> ?A"
         | (fs) "p \<notin> ?A" "q \<in> ?A"
         | (ff) "p \<notin> ?A" "q \<notin> ?A" by blast
  then show "p = q"
  proof cases
    case ss thus ?thesis using eq by (simp add: phi_def)
  next
    case sf
    hence "p = carry c q" using eq by (simp add: phi_def)
    thus ?thesis using surv_not_img[OF q sf(2) p sf(1)] by simp
  next
    case fs
    hence "carry c p = q" using eq by (simp add: phi_def)
    thus ?thesis using surv_not_img[OF p fs(1) q fs(2)] by simp
  next
    case ff
    have ceq: "carry c p = carry c q" using eq ff by (simp add: phi_def)
    have pin: "p \<in> {q \<in> settled_set n S. q \<notin> ?A}" using p ff by simp
    have qin: "q \<in> {q \<in> settled_set n S. q \<notin> ?A}" using q ff by simp
    show ?thesis using inj_onD[OF inj_fallen ceq pin qin] .
  qed
qed

text \<open>STRICT PROGRESS.  A non-idempotent comparator strictly increases the number
  of settled pairs.  The survivor map @{term phi} injects the old settled set into
  the new one, and the comparator's own pair lies in the new set but outside that
  image -- so the new set is strictly larger.

  This replaces an earlier version that ASSUMED @{term "inj_on (carry c)"}, a
  hypothesis measured to be FALSE (1,800 collisions at n=5).\<close>
theorem strict_progress:
  fixes S :: "(nat \<Rightarrow> bool) set"
  assumes c: "c = (a,b)" and ab: "a < b" and bn: "b < n"
      and nonidem: "img_step c S \<noteq> S"
      and Sdef: "S = reach net" and asc: "ascending net"
      and inj: "inj_on (phi c S n) (settled_set n S)"
      and fin: "finite (settled_set n S)"
  shows "card (settled_set n S) < card (settled_set n (img_step c S))"
proof -
  let ?B = "settled_set n S" and ?A = "settled_set n (img_step c S)"
  have sub: "phi c S n ` ?B \<subseteq> ?A"
    using phi_into_after[OF c ab bn] by auto
  have unsettled: "\<not> settledS S a b"
    using nonidem c ab idem_iff_settled by blast
  \<comment> \<open>the comparator's own pair is settled afterwards ...\<close>
  have own: "(a,b) \<in> ?A"
    using c ab bn settled_comparator_pair[of c a b S]
    by (auto simp: settled_set_def)
  \<comment> \<open>... and is not in phi's image: a survivor branch would make it settled
      BEFORE, contradicting non-idempotence; a fallen branch would make it a
      carry-image, excluded by @{thm own_pair_fresh}.\<close>
  have fresh: "(a,b) \<notin> phi c S n ` ?B"
  proof
    assume "(a,b) \<in> phi c S n ` ?B"
    then obtain p where p: "p \<in> ?B" "phi c S n p = (a,b)" by auto
    show False
    proof (cases "p \<in> ?A")
      case True
      hence "p = (a,b)" using p by (simp add: phi_def)
      hence "settledS S a b" using p by (auto simp: settled_set_def)
      thus False using unsettled by simp
    next
      case False
      hence cp: "carry c p = (a,b)" using p by (simp add: phi_def)
      have "(a,b) \<in> carry_img c ?B"
        unfolding carry_img_def using p(1) cp by (rule_tac image_eqI[of _ _ p]) auto
      thus False using own_pair_fresh[OF c ab unsettled Sdef asc] by simp
    qed
  qed
  have finA: "finite ?A"
  proof -
    have "?A \<subseteq> {0..<n} \<times> {0..<n}" by (auto simp: settled_set_def)
    thus ?thesis using finite_subset by fastforce
  qed
  have "card ?B = card (phi c S n ` ?B)" using inj by (simp add: card_image)
  also have "... < card (insert (a,b) (phi c S n ` ?B))"
    using fresh fin by (simp add: card_insert_disjoint)
  also have "... \<le> card ?A" using sub own finA by (metis card_mono insert_subset)
  finally show ?thesis .
qed

text \<open>PHI IS INJECTIVE, with both side conditions now DISCHARGED:
  @{thm surv_not_image_of_fallen} and @{thm inj_on_fallen}.\<close>
lemma phi_inj_closed:
  fixes S :: "(nat \<Rightarrow> bool) set"
  assumes c: "c = (a,b)" and ab: "a < b" and bn: "b < n"
      and Sdef: "S = reach net" and asc: "ascending net"
  shows "inj_on (phi c S n) (settled_set n S)"
  by (rule phi_inj[OF c ab bn
        surv_not_image_of_fallen[OF c ab bn Sdef asc]
        inj_on_fallen[OF c ab bn]])

text \<open>STRICT PROGRESS, standing on proved lemmas end to end: no assumed injectivity,
  no assumed side conditions.\<close>
theorem strict_progress_closed:
  fixes S :: "(nat \<Rightarrow> bool) set"
  assumes c: "c = (a,b)" and ab: "a < b" and bn: "b < n"
      and nonidem: "img_step c S \<noteq> S"
      and Sdef: "S = reach net" and asc: "ascending net"
      and fin: "finite (settled_set n S)"
  shows "card (settled_set n S) < card (settled_set n (img_step c S))"
  by (rule strict_progress[OF c ab bn nonidem Sdef asc
        phi_inj_closed[OF c ab bn Sdef asc] fin])

(* ============================================================================
   SURVIVAL AT THE OWN ADDRESS -- the emitter's missing rule.

   settled_conserved names carry c p as A target.  It is not the ONLY one: a pair
   can survive UNCHANGED while carry names something else.  Example: comparator
   (1,3), pair (0,1).  Here j = a, so carry moves it to (0,3) -- and (0,1) also
   still holds.  The emitter had no rule for that and fell through to unfolding
   img_step over the whole chain, which is why it timed out from n>=5.

   EXACT CHARACTERISATION, measured before proving (n=4, 19,020 instances):
     (i,a) survives  <=>  (i,b) was ALSO settled prior     7644/7644 vs 0/11376
   The reason is immediate: wire a becomes min(v a, v b), so v i <= min needs v i
   below BOTH.  Dually for wire b, which becomes the max.
   ============================================================================ *)

text \<open>LOW SURVIVAL.  A pair pointing at the comparator's low wire survives exactly
  when it is bounded by both wires.\<close>
lemma settled_low_survives:
  assumes c: "c = (a,b)" and ab: "a < b" and ia: "i \<noteq> a" and ib: "i \<noteq> b"
      and lo: "settledS S i a" and hi: "settledS S i b"
  shows "settledS (img_step c S) i a"
  using assms by (auto simp: settledS_def img_step_def apply_comp_def min_def)

text \<open>HIGH SURVIVAL, dual: a pair pointing away from the comparator's high wire
  survives when both wires are below it.\<close>
lemma settled_high_survives:
  assumes c: "c = (a,b)" and ab: "a < b" and ja: "j \<noteq> a" and jb: "j \<noteq> b"
      and hi: "settledS S b j" and lo: "settledS S a j"
  shows "settledS (img_step c S) b j"
  using assms by (auto simp: settledS_def img_step_def apply_comp_def max_def)

(* ============================================================================
   CASE EXHAUSTION ON A BRANCH CONDITION -- the emitter's residue rule.

   ~2% of facts hold on the image but follow from NO pairwise premise about the
   prior settled set.  They are resolved by splitting on an earlier comparator's
   branch condition: the fact holds on both branches for DIFFERENT reasons.  This
   is the discharge calculus operating, and it is where the ORDER ledger runs out
   and the BRANCH atoms carry the fact.

   Concrete instance (n5_classic_9, step 5, comparator (0,3), target (0,1)):
     neither (0,1) nor (3,1) is settled in S5 -- each has a counterexample --
     yet every vector satisfies one or the other, so min(v 0, v 3) <= v 1.
     Splitting on atom g3 (comparator (1,4)) resolves it:
        g3 = 0  (29 vectors):  v 0 <= v 1 always
        g3 = 1  ( 3 vectors):  v 3 <= v 1 always

   BLOW-UP RISK, measured and bounded: a SINGLE atom always sufficed -- zero facts
   required NESTED splits across seven networks (n=4..8, including bubble and
   bitonic).  The margin is thin: several networks have facts where exactly ONE
   atom works.  The emitter must therefore REFUSE to emit when no single atom
   resolves a fact, rather than silently nesting -- nesting is what turns a
   constant-cost case split into 2^d leaves, and it is what killed an earlier
   conjunctive-context emitter.
   ============================================================================ *)

text \<open>A fact established on both sides of any boolean condition holds outright.
  Stated once so emitted proofs cite it by name instead of inlining case
  scaffolding.  The condition is a single branch atom, so this is two branches of
  constant cost -- never a recursion.\<close>
lemma settled_by_cases:
  assumes pos: "P \<Longrightarrow> settledS S i j"
      and neg: "\<not> P \<Longrightarrow> settledS S i j"
  shows "settledS S i j"
  using assms by blast

text \<open>THE DISJUNCTIVE FORMS.  These are where the order ledger genuinely runs out.
  Note the SHAPE: the comparator's wire is on the BOUNDED side of the target, so
  min/max distributes over the disjunction.  (When the comparator's wire is on the
  BOUNDING side the requirement is a CONJUNCTION instead, and that case is already
  covered by @{thm settled_low_survives} and @{thm settled_high_survives} -- I had
  these two backwards at first; 5,628 mismatches out of 14,892 sets said so.)\<close>

lemma settled_min_le_by_disjunction:
  assumes c: "c = (a,b)" and ab: "a < b" and ja: "j \<noteq> a" and jb: "j \<noteq> b"
      and disj: "\<And>v. v \<in> S \<Longrightarrow> v a \<le> v j \<or> v b \<le> v j"
  shows "settledS (img_step c S) a j"
proof (unfold settledS_def, rule ballI)
  fix w assume "w \<in> img_step c S"
  then obtain v where v: "v \<in> S" and w: "w = apply_comp c v"
    by (auto simp: img_step_def)
  have wa: "w a = min (v a) (v b)" using w c ab by (simp add: apply_comp_def)
  have wj: "w j = v j" using w c ja jb by (simp add: apply_comp_def)
  from disj[OF v] show "w a \<le> w j"
  proof
    assume h: "v a \<le> v j"
    have "min (v a) (v b) \<le> v a" by simp
    thus ?thesis using h wa wj by (metis order_trans)
  next
    assume h: "v b \<le> v j"
    have "min (v a) (v b) \<le> v b" by simp
    thus ?thesis using h wa wj by (metis order_trans)
  qed
qed

lemma settled_le_max_by_disjunction:
  assumes c: "c = (a,b)" and ab: "a < b" and ia: "i \<noteq> a" and ib: "i \<noteq> b"
      and disj: "\<And>v. v \<in> S \<Longrightarrow> v i \<le> v a \<or> v i \<le> v b"
  shows "settledS (img_step c S) i b"
proof (unfold settledS_def, rule ballI)
  fix w assume "w \<in> img_step c S"
  then obtain v where v: "v \<in> S" and w: "w = apply_comp c v"
    by (auto simp: img_step_def)
  have wb: "w b = max (v a) (v b)" using w c ab by (simp add: apply_comp_def)
  have wi: "w i = v i" using w c ia ib by (simp add: apply_comp_def)
  from disj[OF v] show "w i \<le> w b"
  proof
    assume h: "v i \<le> v a"
    have "v a \<le> max (v a) (v b)" by simp
    thus ?thesis using h wb wi by (metis order_trans)
  next
    assume h: "v i \<le> v b"
    have "v b \<le> max (v a) (v b)" by simp
    thus ?thesis using h wb wi by (metis order_trans)
  qed
qed

end
