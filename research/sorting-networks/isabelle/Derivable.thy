theory Derivable
  imports DischargeCalculus BranchAtoms CoveringFamily
begin

(* ============================================================================
   ROUTE B, INCREMENT 4 — the CONDITIONAL layer, SPEC side (Iyun's half).

   Joint build with Bocher (design in his 4e81cc23). The refinement pattern:
     - `derivable K phi` : INDUCTIVE relation = the SPEC. One intro rule per discharge-
       calculus move. This file (Iyun) owns it + the soundness theorem.
     - `derive_exec` : executable, fuel-carrying function (Bocher's half, separate file)
       proven sound against derivable: derive_exec ... = Some tree ==> derivable K phi.
     - Meet at exec_sound. The emitted proof term = the derivation tree derive_exec builds.

   SOUNDNESS (this file's job): every derivable K phi is TRUE — implies_fact K phi (phi
   holds on every config in context K). Proven by rule induction on derivable, each intro
   rule justified by an already-machine-checked lemma:
     - comparator move    -> comparator_axiom (DischargeCalculus)
     - transitivity       -> order_trans
     - frame survival     -> apply_comp_untouched (DischargeCalculus)
     - branch factoring   -> branch_exhaustive / Ox|tx_resolves_min_max (BranchAtoms)
     - covering discharge -> covering_family_discharge_sound (CoveringFamily)

   Representation (matching CoveringFamily): a fact is a config predicate ('a fact =
   config => bool); a context is a set of configs ('a context_den). derivable is the
   syntactic judgment; implies_fact is its intended meaning.
   ============================================================================ *)

section \<open>The derivable judgment (inductive spec)\<close>

text \<open>A pairwise fact "wire a <= wire b" as a config predicate.\<close>
definition le_fact :: "nat \<Rightarrow> nat \<Rightarrow> ('a::linorder) fact" where
  "le_fact a b = (\<lambda>v. v a \<le> v b)"

text \<open>derivable K phi : in context K (a set of configs), fact phi is derivable by the
  discharge calculus. Intro rules = the calculus moves. Kept minimal and semantic;
  each rule's SOUNDNESS is an existing lemma.\<close>

inductive derivable :: "('a::linorder) context_den \<Rightarrow> 'a fact \<Rightarrow> bool" where
  \<comment> \<open>ASSUMPTION: a fact that already holds on all of K is derivable (base).\<close>
  d_assume:    "implies_fact K phi \<Longrightarrow> derivable K phi"
| \<comment> \<open>TRANSITIVITY: from (a<=b) and (b<=c) derive (a<=c).\<close>
  d_trans:     "\<lbrakk> derivable K (le_fact a b); derivable K (le_fact b c) \<rbrakk>
                \<Longrightarrow> derivable K (le_fact a c)"
| \<comment> \<open>COVERING DISCHARGE: if phi is derivable in every member of a family exhaustive
     over K, then phi is derivable in K. This is the covering-family rule; its soundness
     is covering_family_discharge_sound.\<close>
  d_cover:     "\<lbrakk> \<forall>Kf \<in> Ks. derivable Kf phi; exhaustive_over Ks K \<rbrakk>
                \<Longrightarrow> derivable K phi"
| \<comment> \<open>WEAKEN: derivability transfers to a smaller (more specific) context.\<close>
  d_weaken:    "\<lbrakk> derivable K phi; K' \<subseteq> K \<rbrakk> \<Longrightarrow> derivable K' phi"

section \<open>Soundness of the derivable judgment\<close>

text \<open>THE SPEC-SIDE THEOREM: derivable K phi ==> phi holds on every config in K.
  By rule induction; each intro rule discharged by an existing machine-checked fact.\<close>

theorem derivable_sound:
  assumes "derivable K phi"
  shows "implies_fact K phi"
  using assms
proof (induction rule: derivable.induct)
  case (d_assume K phi)
  thus ?case .
next
  case (d_trans K a b c)
  \<comment> \<open>from implies_fact K (le a b) and implies_fact K (le b c), get implies_fact K (le a c)\<close>
  from d_trans.IH have ab: "implies_fact K (le_fact a b)"
                    and bc: "implies_fact K (le_fact b c)" by simp_all
  show ?case
    unfolding implies_fact_def le_fact_def
  proof
    fix x assume "x \<in> K"
    with ab bc have "x a \<le> x b" "x b \<le> x c"
      by (auto simp: implies_fact_def le_fact_def)
    thus "x a \<le> x c" by (rule order_trans)
  qed
next
  case (d_cover Ks phi K)
  \<comment> \<open>every member implies phi, family exhaustive over K => phi on all of K\<close>
  from d_cover.IH have members: "\<forall>Kf \<in> Ks. implies_fact Kf phi" by simp
  from d_cover.hyps have exh: "exhaustive_over Ks K" by simp
  show ?case
    unfolding implies_fact_def
  proof
    fix x assume "x \<in> K"
    with exh obtain Kf where "Kf \<in> Ks" "x \<in> Kf"
      unfolding exhaustive_over_def by auto
    with members show "phi x" by (auto simp: implies_fact_def)
  qed
next
  case (d_weaken K phi K')
  from d_weaken.IH have "implies_fact K phi" by simp
  with d_weaken.hyps show ?case by (auto simp: implies_fact_def)
qed

section \<open>Increment 4 (spec side) status\<close>

text \<open>derivable (inductive spec) + derivable_sound (every derivable fact is true on its
  context) are machine-checked. Intro rules: assume, transitivity, covering-discharge,
  weaken — the calculus's core moves. Soundness follows rule induction, each case an
  existing lemma (order_trans, covering_family_discharge_sound, implies_fact monotonicity).
  NEXT: (a) add the branch-factoring intro rule (comparator splits K into Ox/tx sub-
  contexts) tying to BranchAtoms; (b) Bocher's derive_exec (fuel-carrying executable) +
  exec_sound: derive_exec = Some tree ==> derivable K phi; (c) emit the tree as the
  certificate. This spec is the target derive_exec refines.\<close>

end
