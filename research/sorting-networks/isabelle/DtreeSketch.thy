theory DtreeSketch
  imports Derivable
begin

(* ============================================================================
   ROUTE B, INCREMENT 4 — Iyun's INDEPENDENT sketch of the dtree -> derivable
   mapping lemma (the exec_sound meeting point), BEFORE seeing Bocher's derive_exec.

   Purpose (Heath's instruction): build my version from the spec side, then compare
   with Bocher's when his derive_exec lands — learn from the divergence (same pattern
   that worked for the two generators / two oracles).

   Bocher's proposed datatype (4e81cc23): dtree = Leaf fact ledger | Split atom dtree
   dtree | Cover fact (dtree list). I'll sketch a dtree + a "checks out" predicate
   (well_formed_tree) + the mapping theorem: a well-formed tree at (K, phi) witnesses
   derivable K phi. This is the SHAPE derive_exec must satisfy; comparing my
   well_formed_tree to Bocher's derive_exec return conditions is the divergence test.

   My design choice (to compare against his): make the tree carry its OWN context and
   fact at each node, and well_formed_tree check LOCAL soundness of each node against
   the derivable intro rules. Then the mapping is a structural induction where each
   node's check invokes the matching intro. This keeps the tree self-certifying — the
   certificate carries enough to replay each step without re-searching.
   ============================================================================ *)

section \<open>A self-certifying derivation tree\<close>

text \<open>Each node records the context K and fact phi it proves, plus the justification.
  Leaf: phi holds directly on K (d_assume). CoverNode: phi proved in each child, and
  the children's contexts form an exhaustive family over K (d_cover). TransNode: phi =
  (a<=c) via children (a<=b) and (b<=c) on the same K (d_trans). WeakenNode: child
  proves phi on a bigger K' >= K (d_weaken).\<close>

datatype ('a) dtree =
    Leaf   "'a context_den" "'a fact"
  | CoverN "'a context_den" "'a fact" "('a dtree) list"
  | TransN "'a context_den" nat nat nat "'a dtree" "'a dtree"
  | WeakN  "'a context_den" "'a fact" "'a dtree"

text \<open>The (context, fact) a node claims to prove.\<close>
fun claim_ctx :: "('a::linorder) dtree \<Rightarrow> 'a context_den" where
  "claim_ctx (Leaf K phi)          = K"
| "claim_ctx (CoverN K phi ts)     = K"
| "claim_ctx (TransN K a b c t1 t2)= K"
| "claim_ctx (WeakN K phi t)       = K"

fun claim_fact :: "('a::linorder) dtree \<Rightarrow> 'a fact" where
  "claim_fact (Leaf K phi)          = phi"
| "claim_fact (CoverN K phi ts)     = phi"
| "claim_fact (TransN K a b c t1 t2)= le_fact a c"
| "claim_fact (WeakN K phi t)       = phi"

text \<open>well_formed_tree t : every node's local justification checks out (matches the
  derivable intro rule it stands for). Structural recursion.\<close>

fun well_formed_tree :: "('a::linorder) dtree \<Rightarrow> bool" where
  "well_formed_tree (Leaf K phi) = implies_fact K phi"
| "well_formed_tree (CoverN K phi ts) =
     ((\<forall>t \<in> set ts. well_formed_tree t \<and> claim_fact t = phi)
      \<and> exhaustive_over (claim_ctx ` set ts) K)"
| "well_formed_tree (TransN K a b c t1 t2) =
     (well_formed_tree t1 \<and> well_formed_tree t2
      \<and> claim_ctx t1 = K \<and> claim_ctx t2 = K
      \<and> claim_fact t1 = le_fact a b \<and> claim_fact t2 = le_fact b c)"
| "well_formed_tree (WeakN K phi t) =
     (well_formed_tree t \<and> claim_fact t = phi \<and> K \<subseteq> claim_ctx t)"

section \<open>THE MAPPING LEMMA (my version of exec_sound's core)\<close>

text \<open>A well-formed tree witnesses derivability of its claim. This is the shape
  derive_exec must satisfy: derive_exec ... = Some t  ==>  well_formed_tree t
  \<and> claim_ctx t = K \<and> claim_fact t = phi, and THEN this lemma gives derivable K phi.\<close>

theorem wf_tree_derivable:
  "well_formed_tree t \<Longrightarrow> derivable (claim_ctx t) (claim_fact t)"
proof (induction t)
  case (Leaf K phi)
  thus ?case by (auto intro: derivable.d_assume)
next
  case (CoverN K phi ts)
  have children: "\<forall>t \<in> set ts. well_formed_tree t \<and> claim_fact t = phi"
    and exh: "exhaustive_over (claim_ctx ` set ts) K" using CoverN.prems by auto
  \<comment> \<open>each child proves phi on its own context (by IH), family exhaustive over K => d_cover\<close>
  have fam: "\<forall>Kf \<in> (claim_ctx ` set ts). derivable Kf phi"
  proof
    fix Kf assume "Kf \<in> claim_ctx ` set ts"
    then obtain t where t: "t \<in> set ts" "Kf = claim_ctx t" by auto
    with children have "well_formed_tree t" "claim_fact t = phi" by auto
    from CoverN.IH[OF t(1) \<open>well_formed_tree t\<close>]
    have "derivable (claim_ctx t) (claim_fact t)" .
    with \<open>claim_fact t = phi\<close> t(2) show "derivable Kf phi" by simp
  qed
  have "derivable K phi" using fam exh by (rule derivable.d_cover)
  thus ?case by simp
next
  case (TransN K a b c t1 t2)
  have w1: "well_formed_tree t1" and w2: "well_formed_tree t2"
     and k1: "claim_ctx t1 = K" and k2: "claim_ctx t2 = K"
     and f1: "claim_fact t1 = le_fact a b" and f2: "claim_fact t2 = le_fact b c"
    using TransN.prems by auto
  from TransN.IH(1)[OF w1] k1 f1 have ab: "derivable K (le_fact a b)" by simp
  from TransN.IH(2)[OF w2] k2 f2 have bc: "derivable K (le_fact b c)" by simp
  from ab bc have "derivable K (le_fact a c)" by (rule derivable.d_trans)
  thus ?case by simp
next
  case (WeakN K phi t)
  from WeakN.prems have w: "well_formed_tree t" and f: "claim_fact t = phi"
    and sub: "K \<subseteq> claim_ctx t" by auto
  from w WeakN.IH have "derivable (claim_ctx t) (claim_fact t)" by simp
  hence "derivable (claim_ctx t) phi" using f by simp
  from derivable.d_weaken[OF this sub] have "derivable K phi" .
  thus ?case by simp
qed

section \<open>Sketch status + the comparison hook\<close>

text \<open>MY VERSION of the exec_sound meeting point: a self-certifying dtree with a
  structural well_formed_tree check, and wf_tree_derivable mapping it to the derivable
  spec. derive_exec's obligation reduces to: return a tree t with well_formed_tree t,
  claim_ctx t = K, claim_fact t = phi. Then derivable K phi is immediate.

  DIVERGENCE TO COMPARE with Bocher's derive_exec (when it lands):
   - I made the tree carry (context, fact) at EACH node and check LOCAL soundness
     structurally (self-certifying / kernel-replayable without search). Bocher's Split
     node splits on an ATOM (Ox/tx) rather than carrying an arbitrary exhaustive family;
     my CoverN carries the family directly. The atom-split is the SPECIFIC case where
     the family is {K∩Ox_c, K∩tx_c} — a specialization of CoverN. Question for the
     compare: does his derive_exec emit atom-splits (needs a d_branch_split lemma tying
     {Ox,tx} exhaustiveness via branch_exhaustive), or general families (my CoverN)?
   - My well_formed_tree is a pure structural check (no fuel); his derive_exec carries
     fuel and returns None on exhaustion. These compose: derive_exec builds t under fuel;
     the RESULT tree is then fuel-free and well_formed — so wf_tree_derivable applies to
     whatever derive_exec successfully returns, fuel notwithstanding. Clean seam.
  Machine-checked (via ./check.sh). Hold for Bocher, then compare + merge.\<close>

end
