theory DeriveExec
  imports Derivable
begin

(* ============================================================================
   ROUTE B, INCREMENT 4 - the EXECUTABLE side (Bocher's half).

   derive_exec: fuel-carrying executable deriver mirroring the engine's
   _exhaustive recursion (verifier.py covering-family discharge). Returns
   Some dtree (the derivation tree = the CERTIFICATE) or None (fuel out =
   under-derivation; the fail-safe direction, never over-derivation).

   exec_sound: derive_exec fuel K phi = Some t ==> derivable K phi.
   The meet point with Iyun's spec (Derivable.thy). Split-choice is an
   ORACLE PARAMETER (the spec never sees it - soundness oracle-independent
   by construction); the emitted tree records each split for deterministic
   kernel replay. Vacuous/reachability-quotient coverage: DEFERRED to
   increment 5 (Doresh's ablation: n10-optimal closes without it).
   ============================================================================ *)

section \<open>Derivation trees (the certificate)\<close>

datatype 'a dtree =
    DLeaf "('a config \<Rightarrow> bool)"
      \<comment> \<open>fact holds directly on this context (d_assume)\<close>
  | DTrans nat nat nat "'a dtree" "'a dtree"
      \<comment> \<open>le a b + le b c => le a c (d_trans); wires recorded\<close>
  | DSplit comparator "'a dtree" "'a dtree"
      \<comment> \<open>branch on a comparator: Ox-subtree, tx-subtree;
          the {K Int Ox, K Int tx} family is exhaustive (d_cover)\<close>

section \<open>Branch-context denotations\<close>

definition Ox_ctx :: "comparator \<Rightarrow> ('a::linorder) context_den \<Rightarrow> 'a context_den" where
  "Ox_ctx c K = {v \<in> K. branch_Ox c v}"

definition tx_ctx :: "comparator \<Rightarrow> ('a::linorder) context_den \<Rightarrow> 'a context_den" where
  "tx_ctx c K = {v \<in> K. branch_tx c v}"

lemma branch_split_exhaustive:
  "exhaustive_over {Ox_ctx c K, tx_ctx c K} K"
  unfolding exhaustive_over_def Ox_ctx_def tx_ctx_def
  using branch_exhaustive by fastforce

section \<open>The executable deriver\<close>

text \<open>The split-choice oracle: given the context and goal, propose which
  comparator to branch on. Soundness never depends on it.\<close>

type_synonym 'a splitter = "('a context_den) \<Rightarrow> ('a fact) \<Rightarrow> comparator"

text \<open>Checking a fact directly on a context is not executable for
  arbitrary infinite contexts; the executable layer works on the
  0-1 (bool) instance where contexts are finite and checkable.
  Here we keep the deriver ABSTRACT over a decision procedure
  'chk' for the base case, instantiated on the bool instance with
  the finite check; chk is required SOUND (chk K phi ==> implies_fact
  K phi) as a locale assumption.\<close>

locale deriver =
  fixes chk :: "('a::linorder) context_den \<Rightarrow> 'a fact \<Rightarrow> bool"
  assumes chk_sound: "chk K phi \<Longrightarrow> implies_fact K phi"
begin

fun derive_exec :: "nat \<Rightarrow> 'a splitter \<Rightarrow> 'a context_den \<Rightarrow> 'a fact \<Rightarrow> 'a dtree option" where
  "derive_exec 0 orc K phi = None"
| "derive_exec (Suc fuel) orc K phi =
     (if chk K phi then Some (DLeaf phi)
      else (let c = orc K phi in
        (case (derive_exec fuel orc (Ox_ctx c K) phi,
               derive_exec fuel orc (tx_ctx c K) phi) of
           (Some tO, Some tT) \<Rightarrow> Some (DSplit c tO tT)
         | _ \<Rightarrow> None)))"

section \<open>The meet point: exec_sound\<close>

theorem exec_sound:
  "derive_exec fuel orc K phi = Some t \<Longrightarrow> derivable K phi"
proof (induction fuel arbitrary: K t)
  case 0 then show ?case by simp
next
  case (Suc fuel)
  show ?case
  proof (cases "chk K phi")
    case True
    then show ?thesis using chk_sound d_assume by blast
  next
    case False
    let ?c = "orc K phi"
    from False Suc.prems obtain tO tT where
      split: "derive_exec fuel orc (Ox_ctx ?c K) phi = Some tO"
             "derive_exec fuel orc (tx_ctx ?c K) phi = Some tT"
      by (auto simp: Let_def split: option.splits)
    from Suc.IH[OF split(1)] Suc.IH[OF split(2)]
    have "derivable (Ox_ctx ?c K) phi" "derivable (tx_ctx ?c K) phi" .
    then have fam: "\<forall>Kf \<in> {Ox_ctx ?c K, tx_ctx ?c K}. derivable Kf phi"
      by blast
    show ?thesis
      by (rule d_cover[OF fam branch_split_exhaustive])
  qed
qed

text \<open>Fail-safe asymmetry, executable side: None = under-derivation only.
  (Nothing to prove - derive_exec returns Some only via exec_sound-
  justified paths; fuel exhaustion cannot fabricate a certificate.)\<close>

end  (* locale deriver *)

end
