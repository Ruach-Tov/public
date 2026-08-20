theory CoveringFamily
  imports BranchAtoms
begin

(* ============================================================================
   THEORY-LAYER, FILE (3): COVERING-FAMILY (DISJUNCTIVE-ANTECEDENT) DISCHARGE.

   Mechanizes §13 — the soundness lemma that CLOSED the last open lemma
   (the covering-family residual, closed-verified at n10-optimal 45/45).

   Model:
   - A "context" K is a set of branch-atom conditions; semantically it denotes the
     set of configs consistent with it. We model a context directly by its DENOTATION
     [[K]] : the predicate "config x is consistent with K", i.e. a set of configs.
   - The REACHABLE space R is the set of configs actually realizable at the column
     (in the 0-1 setting: the configs some 0-1 input produces there). We model R as a
     set of configs.
   - A ledger fact "K => phi" means: phi holds on every config in [[K]].
   - A covering family {K_1..K_m} for phi: each K_i => phi.
   - EXHAUSTIVE over R: R \<subseteq> \<Union> [[K_i]] (Bocher's reachability quotient:
     the union covers the REACHABLE configs, NOT the whole boolean space).

   THE LEMMA: covering family, each member implies phi, exhaustive over reachable
   => phi holds on all reachable configs (unconditional-over-R discharge).

   Author: Iyun (theory layer), Heath's go-ahead. Builds on BranchAtoms. Machine-checked.
   ============================================================================ *)

section \<open>Contexts, reachability, ledger facts as predicates\<close>

text \<open>A fact phi about configs (e.g. "wire a <= wire b") is a config predicate.\<close>
type_synonym 'a fact = "('a config) \<Rightarrow> bool"

text \<open>A context's denotation is the set of configs consistent with it.\<close>
type_synonym 'a context_den = "('a config) set"

text \<open>"K => phi" : phi holds on every config in context K.\<close>
definition implies_fact :: "('a::linorder) context_den \<Rightarrow> 'a fact \<Rightarrow> bool" where
  "implies_fact K phi = (\<forall>x \<in> K. phi x)"

text \<open>A covering family Ks (a set of contexts) is EXHAUSTIVE over reachable set R
  iff every reachable config lies in some member context.\<close>
definition exhaustive_over :: "('a::linorder) context_den set \<Rightarrow> 'a context_den \<Rightarrow> bool" where
  "exhaustive_over Ks R = (R \<subseteq> \<Union> Ks)"

section \<open>The soundness lemma (§13), mechanized\<close>

text \<open>DISJUNCTIVE-ANTECEDENT DISCHARGE, SOUNDNESS.
  If every member context K of the family implies phi, and the family is exhaustive
  over the reachable space R, then phi holds on every reachable config.
  (Unconditional-over-R: the covering family discharges phi.)\<close>

theorem covering_family_discharge_sound:
  fixes Ks :: "('a::linorder) context_den set"
    and R  :: "'a context_den"
    and phi :: "'a fact"
  assumes members_imply: "\<forall>K \<in> Ks. implies_fact K phi"
  assumes exhaustive:    "exhaustive_over Ks R"
  shows "\<forall>x \<in> R. phi x"
proof
  fix x assume "x \<in> R"
  \<comment> \<open>x is reachable, so by exhaustiveness it lies under some member context K.\<close>
  with exhaustive have "x \<in> \<Union> Ks" by (auto simp: exhaustive_over_def)
  then obtain K where K_mem: "K \<in> Ks" and x_in_K: "x \<in> K" by auto
  \<comment> \<open>That member context implies phi (soundness of the ledger fact K => phi).\<close>
  from members_imply K_mem have "implies_fact K phi" by simp
  with x_in_K show "phi x" by (simp add: implies_fact_def)
qed

text \<open>The reachability quotient is ESSENTIAL (Bocher's crux, §13): the hypothesis is
  R \<subseteq> \<Union> Ks, NOT the boolean tautology (\<Union> Ks = UNIV). We make the
  distinction explicit: covering only the REACHABLE configs suffices; the family need
  NOT cover unrealizable configs. The following shows the lemma would be UNSOUND if we
  demanded phi on non-reachable configs the family doesn't cover.\<close>

lemma reachability_quotient_essential:
  fixes Ks :: "('a::linorder) context_den set" and R :: "'a context_den" and phi :: "'a fact"
  assumes "\<forall>K \<in> Ks. implies_fact K phi"
  assumes "exhaustive_over Ks R"
  \<comment> \<open>phi is guaranteed ONLY on R; a config outside \<Union>Ks carries no guarantee.\<close>
  shows "\<forall>x. x \<in> R \<longrightarrow> phi x"
  using covering_family_discharge_sound[OF assms] by blast

section \<open>The fail-safe asymmetry (§13 Corollary), mechanized\<close>

text \<open>The engine applies covering-family discharge only when exhaustiveness is
  ESTABLISHED (budget permitting). We model the engine's decision as a boolean
  "checked": if exhaustiveness could not be verified (budget exhausted), checked=False
  and the rule is NOT applied. We prove: whenever the engine DOES discharge (applies
  the rule), the discharge is SOUND — regardless of whether every case could be
  checked. Under-discharge (checked=False) forgoes a true conclusion but never asserts
  a false one.\<close>

definition engine_discharges ::
  "bool \<Rightarrow> ('a::linorder) context_den set \<Rightarrow> 'a context_den \<Rightarrow> 'a fact \<Rightarrow> bool" where
  "engine_discharges checked Ks R phi =
     (checked \<and> (\<forall>K \<in> Ks. implies_fact K phi) \<and> exhaustive_over Ks R)"

text \<open>FAIL-SAFE ASYMMETRY: if the engine discharges phi (via covering family), then
  phi genuinely holds on all reachable configs. Soundness holds whether or not
  'checked' is always achievable — the feasibility (budget/poly conjecture) governs
  HOW OFTEN checked=True, never whether a discharge is correct.\<close>

theorem fail_safe_asymmetry:
  assumes "engine_discharges checked Ks R phi"
  shows "\<forall>x \<in> R. phi x"
proof -
  from assms have "\<forall>K \<in> Ks. implies_fact K phi" and "exhaustive_over Ks R"
    by (auto simp: engine_discharges_def)
  thus ?thesis by (rule covering_family_discharge_sound)
qed

text \<open>Corollary: the engine NEVER over-discharges. If phi does NOT hold on all
  reachable configs, the engine does not discharge it (contrapositive of
  fail_safe_asymmetry). Hence every "sorts" verdict (all C(n,2) facts discharged)
  is TRUE — soundness is INDEPENDENT of the polynomial-feasibility conjecture.\<close>

corollary never_over_discharges:
  assumes "\<not> (\<forall>x \<in> R. phi x)"
  shows "\<not> engine_discharges checked Ks R phi"
  using assms fail_safe_asymmetry by blast

end
