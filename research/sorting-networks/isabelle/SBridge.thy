theory SBridge imports CertificateA begin
(* sorted_bools (adjacent scan) equals the full pairwise monotone property on bool lists *)
lemma sorted_bools_iff:
  "sorted_bools v \<longleftrightarrow> (\<forall>i j. i < j \<longrightarrow> j < length v \<longrightarrow> (v!i \<longrightarrow> v!j))"
proof (induction v rule: sorted_bools.induct)
  case 1 thus ?case by simp
next
  case (2 x) thus ?case by simp
next
  case (3 x y rest)
  show ?case
  proof
    assume "sorted_bools (x # y # rest)"
    hence xy: "x \<longrightarrow> y" and rest: "sorted_bools (y # rest)" by auto
    from rest 3 have IH: "\<forall>i j. i<j \<longrightarrow> j<length (y#rest) \<longrightarrow> ((y#rest)!i \<longrightarrow> (y#rest)!j)" by simp
    show "\<forall>i j. i<j \<longrightarrow> j<length (x#y#rest) \<longrightarrow> ((x#y#rest)!i \<longrightarrow> (x#y#rest)!j)"
    proof (intro allI impI)
      fix i j assume ij: "i<j" and jl: "j < length (x#y#rest)"
      show "(x#y#rest)!i \<longrightarrow> (x#y#rest)!j"
      proof (cases i)
        case 0
        show ?thesis
        proof (cases j)
          case 0 with ij show ?thesis by simp
        next
          case (Suc j') 
          (* need: x --> (y#rest)!j'. x-->y, and monotone from y up. *)
          from \<open>i=0\<close> Suc ij jl IH xy show ?thesis 
            by (metis One_nat_def Suc_less_eq Suc_mono length_Cons less_Suc0 nth_Cons_0 nth_Cons_Suc zero_less_Suc)
        qed
      next
        case (Suc i')
        with ij obtain j' where "j = Suc j'" using less_imp_Suc_add by (metis Suc_lessE)
        with Suc ij jl IH show ?thesis by auto
      qed
    qed
  next
    assume A: "\<forall>i j. i<j \<longrightarrow> j<length (x#y#rest) \<longrightarrow> ((x#y#rest)!i \<longrightarrow> (x#y#rest)!j)"
    have "x \<longrightarrow> y" using A[rule_format, of 0 1] by simp
    moreover have "sorted_bools (y#rest)"
      using 3 A by (metis Suc_less_eq length_Cons nth_Cons_Suc)
    ultimately show "sorted_bools (x # y # rest)" by simp
  qed
qed
end
