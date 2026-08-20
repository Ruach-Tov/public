theory Ctree
  imports Derivable TransGen
begin

(* ============================================================================
   ROUTE B v1.2-final — the UNIFIED certificate tree (Bocher's datatype call, Iyun's pen).

   DtreeSketch's dtree (Leaf|CoverN|TransN|WeakN) and TransGen's gtree (GLeaf|GTrans) are
   merged into ONE grammar. Rationale (Bocher ed1f6f69): one datatype = one thing a skeptic
   audits; the annotate adapter targets a single claimed-tree type (no bridges); the two
   soundness proofs merge into ONE theorem = smaller trusted base.

   ctree = CLeaf | CCover | CTrans | CWeak, with CTrans in the GENERAL value-expression
   form (vle lhs rhs). le_fact's wire-index transitivity is the special case
   CTrans (\<lambda>v. v a) (\<lambda>v. v b) (\<lambda>v. v c). So CTrans subsumes both the old
   le_fact-TransN and the GTrans. One soundness theorem: cwf_derivable.
   ============================================================================ *)

section \<open>The unified certificate tree\<close>

datatype ('a) ctree =
    CLeaf  "'a context_den" "'a fact"
  | CCover "'a context_den" "'a fact" "('a ctree) list"
  | CTrans "'a context_den" "('a config \<Rightarrow> 'a)" "('a config \<Rightarrow> 'a)" "('a config \<Rightarrow> 'a)"
           "'a ctree" "'a ctree"
  | CWeak  "'a context_den" "'a fact" "'a ctree"

fun cctx :: "('a::linorder) ctree \<Rightarrow> 'a context_den" where
  "cctx (CLeaf K phi)             = K"
| "cctx (CCover K phi ts)         = K"
| "cctx (CTrans K lhs mid rhs a b)= K"
| "cctx (CWeak K phi t)           = K"

fun cfact :: "('a::linorder) ctree \<Rightarrow> 'a fact" where
  "cfact (CLeaf K phi)             = phi"
| "cfact (CCover K phi ts)         = phi"
| "cfact (CTrans K lhs mid rhs a b)= vle lhs rhs"
| "cfact (CWeak K phi t)           = phi"

text \<open>The single structural well-formedness check (subsumes wf_tree_derivable's and
  gwell_formed's clauses). CLeaf: fact holds on K. CCover: children well-formed, prove
  phi, contexts exhaustive over K. CTrans: children prove (lhs<=mid) and (mid<=rhs) on K.
  CWeak: child proves phi on a bigger context.\<close>

fun cwf :: "('a::linorder) ctree \<Rightarrow> bool" where
  "cwf (CLeaf K phi) = implies_fact K phi"
| "cwf (CCover K phi ts) =
     ((\<forall>t \<in> set ts. cwf t \<and> cfact t = phi) \<and> exhaustive_over (cctx ` set ts) K)"
| "cwf (CTrans K lhs mid rhs a b) =
     (cwf a \<and> cwf b \<and> cctx a = K \<and> cctx b = K
      \<and> cfact a = vle lhs mid \<and> cfact b = vle mid rhs)"
| "cwf (CWeak K phi t) = (cwf t \<and> cfact t = phi \<and> K \<subseteq> cctx t)"

section \<open>★ THE UNIFIED SOUNDNESS THEOREM ★\<close>

text \<open>One theorem covering all node types: a well-formed ctree witnesses derivability of
  its claim. Merges wf_tree_derivable (DtreeSketch) and gwf_derivable (TransGen).\<close>

theorem cwf_derivable:
  "cwf t \<Longrightarrow> derivable (cctx t) (cfact t)"
proof (induction t)
  case (CLeaf K phi)
  thus ?case by (auto intro: d_assume)
next
  case (CCover K phi ts)
  have children: "\<forall>t \<in> set ts. cwf t \<and> cfact t = phi"
    and exh: "exhaustive_over (cctx ` set ts) K" using CCover.prems by auto
  have fam: "\<forall>Kf \<in> (cctx ` set ts). derivable Kf phi"
  proof
    fix Kf assume "Kf \<in> cctx ` set ts"
    then obtain t where t: "t \<in> set ts" "Kf = cctx t" by auto
    with children have "cwf t" "cfact t = phi" by auto
    from CCover.IH[OF t(1) \<open>cwf t\<close>] have "derivable (cctx t) (cfact t)" .
    with \<open>cfact t = phi\<close> t(2) show "derivable Kf phi" by simp
  qed
  have "derivable K phi" using fam exh by (rule d_cover)
  thus ?case by simp
next
  case (CTrans K lhs mid rhs a b)
  have wa: "cwf a" and wb: "cwf b" and ka: "cctx a = K" and kb: "cctx b = K"
    and fa: "cfact a = vle lhs mid" and fb: "cfact b = vle mid rhs"
    using CTrans.prems by auto
  from CTrans.IH(1)[OF wa] ka fa have "derivable K (vle lhs mid)" by simp
  moreover from CTrans.IH(2)[OF wb] kb fb have "derivable K (vle mid rhs)" by simp
  ultimately have "derivable K (vle lhs rhs)" by (rule derivable_vle_trans)
  thus ?case by simp
next
  case (CWeak K phi t)
  have w: "cwf t" and f: "cfact t = phi" and sub: "K \<subseteq> cctx t" using CWeak.prems by auto
  from CWeak.IH[OF w] f have "derivable (cctx t) phi" by simp
  from d_weaken[OF this sub] show ?case by simp
qed

section \<open>le_fact transitivity is the wire-index special case of CTrans\<close>

text \<open>The old le_fact-TransN is recovered: CTrans with the coordinate projections
  (\<lambda>v. v a), (\<lambda>v. v b), (\<lambda>v. v c) proves le_fact a c, since
  vle (\<lambda>v. v a) (\<lambda>v. v c) = le_fact a c. So the unified grammar loses nothing.\<close>

lemma le_fact_as_vle: "le_fact a b = vle (\<lambda>v. v a) (\<lambda>v. v b)"
  by (simp add: le_fact_def vle_def)

section \<open>v1.2-final status\<close>

text \<open>ONE certificate grammar (ctree), ONE structural check (cwf), ONE soundness theorem
  (cwf_derivable) subsuming both prior trees. CTrans in value-expression form subsumes the
  wire-index TransN (le_fact_as_vle) AND the GTrans. The annotate adapter now targets ctree
  alone; the final DSplit assembly (CCover with structural CTrans tc-branch + Oc CLeaf) is
  native, no bridges. Smaller trusted base: a skeptic audits one datatype + one theorem.
  Machine-checked via ./check.sh --clean.\<close>

end
