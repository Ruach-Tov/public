(* Advancing toward (A) operational completeness — the tractable ~20%. Iyun, 2026-07-29.
   A1: fuel monotonicity. The lesson (via show_types, Mavdil's diagnostic): the fuel variable
   F MUST be annotated ::nat, else derive_exec's fuel unifies polymorphically and `induction F`
   cannot find the nat induction rule ("Unable to figure out induct rule"). A goal that will not
   induct is often a hidden type-generality bug -- show_types reveals it (derive_exec printed as
   'b => 'c => 'd => 'e => 'a option, all polymorphic = F not nat). *)
theory DeriveExecComplete
  imports DeriveExec
begin

section \<open>A1: fuel monotonicity --- more fuel never breaks a success\<close>

lemma derive_exec_mono_fuel:
  "\<forall>K phi t G. derive_exec (F::nat) orc K phi = Some t \<longrightarrow> F \<le> G \<longrightarrow>
     (\<exists>t'. derive_exec G orc K phi = Some t')"
proof (induction F)
  case 0
  show ?case by simp
next
  case (Suc F)
  show ?case
  proof (intro allI impI)
    fix K phi t G
    assume prem: "derive_exec (Suc F) orc K phi = Some t" and le: "Suc F \<le> G"
    from le obtain G' where G: "G = Suc G'" and le': "F \<le> G'" by (cases G) auto
    show "\<exists>t'. derive_exec G orc K phi = Some t'"
    proof (cases "chk K phi")
      case True thus ?thesis using G by simp
    next
      case False
      let ?c = "orc K phi"
      from prem False obtain tO tT where
        dO: "derive_exec F orc (Ox_ctx ?c K) phi = Some tO" and
        dT: "derive_exec F orc (tx_ctx ?c K) phi = Some tT"
        by (auto split: option.splits)
      from Suc.IH have
        "\<exists>t'. derive_exec G' orc (Ox_ctx ?c K) phi = Some t'" using dO le' by blast
      moreover from Suc.IH have
        "\<exists>t'. derive_exec G' orc (tx_ctx ?c K) phi = Some t'" using dT le' by blast
      ultimately show ?thesis using False G by (auto split: option.splits)
    qed
  qed
qed

text \<open>Clean corollary form (existential premise).\<close>
corollary derive_exec_mono:
  assumes "derive_exec (F::nat) orc K phi = Some t" and "F \<le> G"
  shows "\<exists>t'. derive_exec G orc K phi = Some t'"
  using derive_exec_mono_fuel assms by blast

end
