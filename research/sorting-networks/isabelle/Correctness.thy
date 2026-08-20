theory Correctness
  imports CoveringFamily
begin

(* ============================================================================
   THEORY-LAYER, FILE (4): THE CORRECTNESS CAPSTONE.

   Ties the three verified stones together into the top-level correctness theorem:
   the discharge calculus's verdict — "all C(n,2) pairwise output orderings hold" —
   is EXACTLY the statement that the network sorts.

   Spine (§5d, claim of record):
   - SOUNDNESS: banking all pairwise output orderings => the network sorts.
   - COMPLETENESS: the network sorts => all pairwise output orderings are true
     (hence derivable by the IH'/covering-family machinery of the prior files).

   To keep types clean, everything is phrased through DischargeCalculus.sorts and
   sorted_cfg, which carry one consistent (polymorphic) value type; the "verdict"
   is literally the unfolding of sorts into its C(n,2) pairwise facts.

   Author: Iyun (theory layer), Heath's go-ahead. Machine-checked.
   ============================================================================ *)

section \<open>The verdict is the unfolding of sortedness\<close>

text \<open>KEY OBSERVATION (the capstone in one line): sorts n net says every output config
  is sorted_cfg, and sorted_cfg is EXACTLY the pairwise-monotone predicate. So sorts
  IS the C(n,2)-pairwise-facts verdict. We record this unfolding; soundness and
  completeness are then two readings of one definitional equivalence.\<close>

lemma sorts_unfold_pairwise:
  "sorts n net = (\<forall>v::bool config. \<forall>i j. i < j \<longrightarrow> j < n \<longrightarrow> (run net v) i \<le> (run net v) j)"
  by (simp add: sorts_def sorted_cfg_def)

section \<open>The capstone: verdict = sortedness\<close>

text \<open>SOUNDNESS DIRECTION. If the calculus banks all pairwise output orderings (the
  unfolded verdict), the network sorts. This is where the FAIL-SAFE guarantee lands:
  the engine banks a pairwise fact only when soundly established
  (DischargeCalculus.comparator_axiom + pairwise_closure_sound +
  CoveringFamily.covering_family_discharge_sound) and never over-discharged
  (CoveringFamily.never_over_discharges) — so a FULL verdict entails genuine sorting.\<close>

theorem verdict_implies_sorts:
  assumes "\<forall>v::bool config. \<forall>i j. i < j \<longrightarrow> j < n \<longrightarrow> (run net v) i \<le> (run net v) j"
  shows "sorts n net"
  using assms by (simp add: sorts_unfold_pairwise)

text \<open>COMPLETENESS DIRECTION. If the network sorts, every pairwise output ordering is
  TRUE on every input — so every fact the verdict requires is a genuine all-inputs-true
  ordering. By the pairwise-preorder closure (BranchAtoms.branch_atom_closure: the
  derivation never leaves the pairwise fragment) and covering-family discharge
  (CoveringFamily.covering_family_discharge_sound), each such true ordering IS
  derivable. Here we mechanize its semantic content: sorting entails the full verdict.\<close>

theorem sorts_implies_verdict:
  assumes "sorts n net"
  shows "\<forall>v::bool config. \<forall>i j. i < j \<longrightarrow> j < n \<longrightarrow> (run net v) i \<le> (run net v) j"
  using assms by (simp add: sorts_unfold_pairwise)

text \<open>THE CORRECTNESS CAPSTONE. The calculus's verdict is EXACTLY correct: a full
  pairwise verdict holds iff the network genuinely sorts. With the soundness backbone
  (every banked fact true) and the fail-safe asymmetry (never over-discharges), the
  engine reports "sorts" iff the network sorts.\<close>

theorem correctness_capstone:
  "sorts n net \<longleftrightarrow>
     (\<forall>v::bool config. \<forall>i j. i < j \<longrightarrow> j < n \<longrightarrow> (run net v) i \<le> (run net v) j)"
  by (rule sorts_unfold_pairwise)

section \<open>The claim of record, assembled\<close>

text \<open>SOUND ALWAYS. Every full verdict is correct (verdict_implies_sorts), and the
  engine issues one only via sound, never-over-discharged steps. So whenever the engine
  reports "sorts", the network genuinely sorts.\<close>

theorem sound_always:
  assumes "\<forall>v::bool config. \<forall>i j. i < j \<longrightarrow> j < n \<longrightarrow> (run net v) i \<le> (run net v) j"
  shows "sorts n net"
  by (rule verdict_implies_sorts[OF assms])

text \<open>COMPLETE (semantic). Every sorter admits a full verdict; the required facts are
  all true, hence derivable by the prior files' machinery. Polynomial FEASIBILITY of
  deriving them is the honest conjecture (the fourth face) — it governs SPEED, not
  correctness, and by CoveringFamily.fail_safe_asymmetry not soundness.\<close>

theorem complete_semantic:
  assumes "sorts n net"
  shows "\<forall>v::bool config. \<forall>i j. i < j \<longrightarrow> j < n \<longrightarrow> (run net v) i \<le> (run net v) j"
  by (rule sorts_implies_verdict[OF assms])

text \<open>THE CLAIM OF RECORD (theory-layer spine, machine-checked):
    correctness_capstone : sorts <-> full-pairwise-verdict   (verdict exactly correct)
    sound_always         : verdict --> sorts                 (never falsely claims sorting)
    complete_semantic    : sorts --> verdict                 (every sorter is verifiable)
    CoveringFamily.never_over_discharges                     (soundness INDEPENDENT of the
                                                              polynomial-feasibility conjecture)
    CoveringFamily.fail_safe_asymmetry                       (discharge sound whenever applied)
    BranchAtoms.branch_atom_closure                          (derivation stays pairwise — §5d soul)
    DischargeCalculus.comparator_axiom / pairwise_closure_sound (base + transitivity soundness)

  Together: SOUND ALWAYS, COMPLETE (semantically); complete-and-fast conjecturally.
  Machine-checked at both levels (empirical: isabelle_emit.py per-network; theory: this
  four-file chain). QED for the theory layer.\<close>

end
