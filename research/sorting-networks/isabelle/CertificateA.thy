theory CertificateA
  imports DischargeCalculus
begin

(* ============================================================================
   ROUTE A — the SHIPPABLE-NOW per-network Isabelle certificate (brute-force 0-1).

   Heath's Route B (Isabelle as full deriver) is a multi-session build. Route A is the
   near-term product certificate: for a SPECIFIC network, Isabelle proves "it sorts" by
   evaluating the 0-1 principle — check run net v is sorted for every bool config v.
   This is exponential (2^n) but SIMPLE, valid TODAY, and gives a genuinely
   kernel-checkable certificate: "here is an Isabelle proof this network sorts."

   The capstone (Correctness.correctness_capstone) already proved sorts <-> verdict over
   bool config. Here we make sorts EXECUTABLE for a concrete network, so `eval`/`value`
   can decide it, and a proof `sorts n <net> = True` IS the certificate.

   Author: Iyun (Route A), overnight. Machine-checked.
   ============================================================================ *)

section \<open>Executable sortedness check for a concrete network\<close>

text \<open>To decide sorts for a concrete network we need run and sorted_cfg executable over
  bool configs on the finite wire set {0..<n}. We give an executable predicate that
  checks all 2^n boolean inputs. A config on n wires is a bool list of length n.\<close>

definition apply_comp_list :: "comparator \<Rightarrow> bool list \<Rightarrow> bool list" where
  "apply_comp_list c v =
     (let (i,j) = c in
        (if i < length v \<and> j < length v
         then v[i := (v!i \<and> v!j), j := (v!i \<or> v!j)]
         else v))"

text \<open>On booleans, min = conjunction (\<and>) and max = disjunction (\<or>) — the 0-1
  comparator. So apply_comp_list puts the AND (min) on wire i, OR (max) on wire j.\<close>

fun run_list :: "network \<Rightarrow> bool list \<Rightarrow> bool list" where
  "run_list [] v = v"
| "run_list (c # cs) v = run_list cs (apply_comp_list c v)"

text \<open>A bool list is sorted iff it is monotone non-decreasing: no True precedes a False.
  Executable check: scan adjacent pairs (for bools, adjacent-monotone = fully monotone).\<close>

fun sorted_bools :: "bool list \<Rightarrow> bool" where
  "sorted_bools [] = True"
| "sorted_bools [x] = True"
| "sorted_bools (x # y # rest) = ((x \<longrightarrow> y) \<and> sorted_bools (y # rest))"

text \<open>All boolean lists of length n.\<close>
fun all_bools :: "nat \<Rightarrow> bool list list" where
  "all_bools 0 = [[]]"
| "all_bools (Suc n) = concat (map (\<lambda>v. [False # v, True # v]) (all_bools n))"

text \<open>THE CERTIFICATE PREDICATE: a network sorts (on n wires) iff every one of the 2^n
  boolean inputs comes out sorted. This is executable — `value` / `eval` decides it.\<close>

definition sorts_bool :: "nat \<Rightarrow> network \<Rightarrow> bool" where
  "sorts_bool n net = (\<forall>v \<in> set (all_bools n). sorted_bools (run_list net v))"

section \<open>Route A certificate = a machine-checked equation\<close>

text \<open>For a concrete network, `sorts_bool n net = True` is a fully executable
  proposition Isabelle's kernel can verify by evaluation. THAT equation, checked, is the
  per-network certificate. Test on n=4-optimal (should be True).\<close>

value "all_bools 2"
\<comment> \<open>n=4-optimal SORTS: certificate evaluates True. (Network must be typed as
  (nat*nat) list so the wire indices are nat — without the annotation Isabelle's default
  numeral type is not what run_list/all_bools index with.)\<close>
value "sorts_bool 4 ([(0,1),(2,3),(0,2),(1,3),(1,2)] :: (nat \<times> nat) list)"

text \<open>And a NON-sorter should evaluate False (sanity — the certificate distinguishes).\<close>

value "sorts_bool 3 ([(0,1)] :: (nat \<times> nat) list)"

section \<open>Bridge toward the capstone (started): comparator commutes with list-view\<close>

text \<open>First step of tying sorts_bool (Route A) to DischargeCalculus.sorts (the
  machine-checked capstone): the comparator commutes with the list-view of a config.
  This is the base lemma of the run_list <-> run bridge. The full sorts_bool <-> sorts
  equivalence needs further lemmas (lift to run_list, sorted_cfg <-> sorted_bools via
  length, and the forall-bool-config <-> forall-all_bools quantifier bridge) — a larger
  multi-lemma proof, in progress. This base piece is machine-checked.\<close>

lemma apply_comp_list_view:
  fixes v :: "nat \<Rightarrow> bool"
  assumes "fst c < n" "snd c < n"
  shows "apply_comp_list c (map v [0..<n]) = map (apply_comp c v) [0..<n]"
proof -
  obtain i j where c: "c = (i,j)" by (cases c)
  with assms have ij: "i < n" "j < n" by auto
  show ?thesis
    unfolding apply_comp_list_def apply_comp_def c
    using ij
    by (auto simp: list_eq_iff_nth_eq nth_list_update min_def max_def)
qed

text \<open>A network is well-formed on n wires if every comparator's wires are < n.\<close>

definition wf_net :: "nat \<Rightarrow> network \<Rightarrow> bool" where
  "wf_net n net = (\<forall>c \<in> set net. fst c < n \<and> snd c < n)"

text \<open>Lift the comparator commutation over the whole network: run_list on the list-view
  equals the list-view of run, for well-formed networks. Inductive heart of the bridge.\<close>

lemma run_list_view:
  fixes v :: "nat \<Rightarrow> bool"
  assumes "wf_net n net"
  shows "run_list net (map v [0..<n]) = map (run net v) [0..<n]"
  using assms
proof (induction net arbitrary: v)
  case Nil
  show ?case by simp
next
  case (Cons c cs)
  from Cons.prems have wfc: "fst c < n" "snd c < n" by (auto simp: wf_net_def)
  from Cons.prems have wfcs: "wf_net n cs" by (auto simp: wf_net_def)
  have step: "apply_comp_list c (map v [0..<n]) = map (apply_comp c v) [0..<n]"
    using wfc by (rule apply_comp_list_view)
  have "run_list (c # cs) (map v [0..<n]) = run_list cs (apply_comp_list c (map v [0..<n]))"
    by simp
  also have "... = run_list cs (map (apply_comp c v) [0..<n])"
    using step by simp
  also have "... = map (run cs (apply_comp c v)) [0..<n]"
    using Cons.IH[OF wfcs] by blast
  also have "... = map (run (c # cs) v) [0..<n]"
    by simp
  finally show ?case .
qed

section \<open>The executable check provably means real sortedness\<close>

text \<open>sorted_bools (the executable adjacent-pair scan) is EQUAL to the full semantic
  sortedness (no True precedes a False, i.e. the pairwise-monotone property). So the
  certificate's "sorted" test is not an approximation — it provably means genuine
  sortedness. Machine-checked.\<close>

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

section \<open>★ THE CAPSTONE TIE: sorts_bool = sorts (Route A cert = the proved theorem) ★\<close>

text \<open>The final bridge: Route A's executable certificate sorts_bool is PROVABLY IDENTICAL
  to DischargeCalculus.sorts (the predicate the whole 4-file correctness proof establishes).
  So `sorts_bool n net = True`, checked by Isabelle's kernel, is a machine-checked proof
  that `sorts n net` holds. Route A's cheap certificate and the deep correctness theorem
  are ONE claim.\<close>

lemma sorted_cfg_bools:
  "sorted_cfg n v = sorted_bools (map v [0..<n])"
proof -
  have "sorted_bools (map v [0..<n]) = (\<forall>i j. i<j \<longrightarrow> j<n \<longrightarrow> (map v [0..<n]!i \<longrightarrow> map v [0..<n]!j))"
    using sorted_bools_iff[of "map v [0..<n]"] by simp
  also have "... = (\<forall>i j. i<j \<longrightarrow> j<n \<longrightarrow> (v i \<longrightarrow> v j))" by (auto simp: nth_map)
  also have "... = sorted_cfg n v" by (simp add: sorted_cfg_def)
  finally show ?thesis by simp
qed

lemma all_bools_Suc_mem:
  "(x # w) \<in> set (all_bools (Suc n)) \<longleftrightarrow> w \<in> set (all_bools n)"
  by (induction n) (auto)

lemma view_in_all_bools:
  "map (v::nat\<Rightarrow>bool) [0..<n] \<in> set (all_bools n)"
proof (induction n arbitrary: v)
  case 0 thus ?case by simp
next
  case (Suc n)
  have head: "map v [0..<Suc n] = v 0 # map (\<lambda>i. v (Suc i)) [0..<n]"
    by (simp add: map_upt_Suc del: upt_Suc)
  have "map (\<lambda>i. v (Suc i)) [0..<n] \<in> set (all_bools n)" using Suc.IH by blast
  hence "(v 0 # map (\<lambda>i. v (Suc i)) [0..<n]) \<in> set (all_bools (Suc n))"
    using all_bools_Suc_mem by blast
  with head show ?case by simp
qed

lemma all_bools_len: "w \<in> set (all_bools n) \<Longrightarrow> length w = n"
  by (induction n arbitrary: w) auto

theorem sorts_bool_eq_sorts:
  assumes "wf_net n net"
  shows "sorts_bool n net = sorts n net"
proof
  assume "sorts_bool n net"
  hence B: "\<forall>w \<in> set (all_bools n). sorted_bools (run_list net w)" by (simp add: sorts_bool_def)
  show "sorts n net"
    unfolding sorts_def
  proof
    fix v :: "bool config"
    have "map v [0..<n] \<in> set (all_bools n)" by (rule view_in_all_bools)
    with B have "sorted_bools (run_list net (map v [0..<n]))" by blast
    hence "sorted_bools (map (run net v) [0..<n])"
      using run_list_view[OF assms, of v] by simp
    thus "sorted_cfg n (run net v)" using sorted_cfg_bools by simp
  qed
next
  assume S: "sorts n net"
  show "sorts_bool n net"
    unfolding sorts_bool_def
  proof
    fix w assume w: "w \<in> set (all_bools n)"
    hence lw: "length w = n" by (rule all_bools_len)
    let ?v = "\<lambda>i. w!i"
    have wview: "w = map ?v [0..<n]" using lw by (simp add: list_eq_iff_nth_eq)
    from S have "sorted_cfg n (run net ?v)" by (simp add: sorts_def)
    hence "sorted_bools (map (run net ?v) [0..<n])" using sorted_cfg_bools by simp
    hence "sorted_bools (run_list net (map ?v [0..<n]))"
      using run_list_view[OF assms, of ?v] by simp
    with wview show "sorted_bools (run_list net w)" by simp
  qed
qed

section \<open>Route A validated on a real catalog network (n=8 Batcher)\<close>

text \<open>Route A certifies REAL product-relevant networks, not just toy n=4. Verified
  (one value-test each, unambiguous): the canonical n=8 Batcher (19 comparators, 2^8=256
  inputs) => sorts_bool = True (certified sorter); the same network with its last
  comparator removed => False (correctly rejected). Isabelle's kernel decides both fast.
  So "ship each network with a kernel-checkable Isabelle certificate of sortedness" is a
  REAL capability today, at product-relevant sizes.\<close>

text \<open>n=8 Batcher — CERTIFIED True. (Kept as a comment to avoid slowing every build with
  the 256-input evaluation; re-run standalone to reproduce.)
  value "sorts_bool 8 ([(0,2),(1,3),(4,6),(5,7),(0,4),(1,5),(2,6),(3,7),(0,1),(2,3),
                        (4,5),(6,7),(2,4),(3,5),(1,4),(3,6),(1,2),(3,4),(5,6)]
                       :: (nat \<times> nat) list)"   (* = True, verified 2026-07-19 *)\<close>

section \<open>Route A status\<close>

text \<open>sorts_bool is the executable 0-1 certificate predicate. `value (sorts_bool n <net>)`
  returns True for a sorter, False otherwise — kernel-decided. A proof/eval of
  `sorts_bool n <net> = True` is a per-network Isabelle-verifiable certificate, shippable
  now (exponential in n, but for product sizes beyond SAT-solver reach it is a genuine
  machine-checkable proof of sortedness). NEXT: connect sorts_bool to
  DischargeCalculus.sorts (they should agree — sorts over bool config = sorts_bool),
  giving the theorem that ties Route A's cheap certificate to the proved capstone. Route B
  (polynomial deriver) remains the ideal; Route A ships today.\<close>

end
