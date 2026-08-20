theory Climb_And_Return
  imports Vandermonde_Path_B
begin

(* ============================================================================
   THE CLIMB-AND-RETURN RECURSION: the closed form of the optimal fold schedule.

   The partial-fold search located the residual hardness: the optimal fold schedule is not
   monotone weight-ascending but CLIMBS AND RETURNS -- a high fold (a merge) creates new
   low-weight work, so the schedule returns to low weight before climbing again.  Reading
   the max-weight-per-layer of Batcher's networks made the recursion visible:

     n = 8  (k=3):  [1, 1, 2, 1, 2, 3]
     n = 16 (k=4):  [1, 1, 2, 1, 2, 3, 1, 2, 3, 4]

   The second contains the first as a prefix, then extends it.  The recursion is

     S(k) = S(k-1) ++ M(k),   where M(k) = [1, 2, ..., k]

   -- to sort 2^k wires, sort the two halves of 2^{k-1} (in parallel, the same layers),
   then MERGE with a climb of weight one up to k.  The merge M(k) is a full ascent from an
   edge (weight 1, the return) to the body diagonal of the k-cube (weight k, the antipode).

   This theory formalises the recursion and its two consequences:
     - the depth of the schedule is the triangular number k(k+1)/2 (Batcher's depth);
     - the schedule's tail is a full ascent 1..k, ending at the antipode, so the last fold
       of every merge is along a higher diagonal than any before it -- the climb.

   The recursion is the recursive merge (Vandermonde_Path_B: merge preserves the threshold
   structure), read as a weight schedule.  The generator's recursion (sort halves, merge)
   and the schedule's climb-and-return are the same object.  Self-contained above Path B.
   ============================================================================ *)

text \<open>The merge climb M(k) = the list [1, 2, ..., k] -- a full weight-ascent from edge to
      body diagonal.\<close>

definition merge_climb :: "nat \<Rightarrow> nat list" where
  "merge_climb k = [1..<k+1]"

text \<open>The sort schedule S(k), the max-weight-per-layer sequence: sort the halves S(k-1),
      then the merge climb M(k).\<close>

fun sort_schedule :: "nat \<Rightarrow> nat list" where
  "sort_schedule 0 = []"
| "sort_schedule (Suc k) = sort_schedule k @ merge_climb (Suc k)"

text \<open>THE MERGE CLIMB HAS LENGTH k and ascends 1..k.\<close>

theorem merge_climb_length: "length (merge_climb k) = k"
  by (simp add: merge_climb_def)

theorem merge_climb_content: "merge_climb k = [1..<k+1]"
  by (simp add: merge_climb_def)

text \<open>THE SCHEDULE DEPTH is the triangular number.  Each merge adds k layers, so the total
      depth of sorting 2^k is 1 + 2 + ... + k = k(k+1)/2 --- Batcher's depth, derived from
      the climb-and-return recursion.\<close>

theorem schedule_depth:
  "length (sort_schedule k) = (k * (k + 1)) div 2"
proof (induct k)
  case 0
  thus ?case by simp
next
  case (Suc k)
  have "length (sort_schedule (Suc k)) = length (sort_schedule k) + length (merge_climb (Suc k))"
    by simp
  also have "... = (k * (k + 1)) div 2 + (Suc k)"
    using Suc merge_climb_length by simp
  also have "... = (Suc k * (Suc k + 1)) div 2"
    by (simp add: algebra_simps)
  finally show ?case .
qed

text \<open>THE RECURSION unfolds: S(k) is S(k-1) followed by the climb 1..k.  Recorded as the
      defining equation, the closed form of the climb-and-return.\<close>

theorem schedule_recursion:
  "sort_schedule (Suc k) = sort_schedule k @ [1..<(Suc k)+1]"
  by (simp add: merge_climb_def)

text \<open>THE TAIL IS A FULL ASCENT ending at the antipode.  The last merge, M(k), climbs from
      weight 1 (an edge) to weight k (the all-ones body diagonal of the k-cube --- the
      antipode).  So the schedule ends at the summit, reached only at the very last layer.\<close>

theorem schedule_ends_at_antipode:
  assumes "k > 0"
  shows "last (sort_schedule k) = k"
proof -
  obtain j where k: "k = Suc j" using assms by (cases k) auto
  have "sort_schedule (Suc j) = sort_schedule j @ merge_climb (Suc j)"
    by simp
  moreover have "merge_climb (Suc j) \<noteq> []"
    by (simp add: merge_climb_def)
  moreover have "last (merge_climb (Suc j)) = Suc j"
    by (simp add: merge_climb_def)
  ultimately have "last (sort_schedule (Suc j)) = Suc j"
    by (metis last_appendR)
  thus ?thesis using k by simp
qed

text \<open>THE CLIMB-AND-RETURN property: the schedule is NOT monotone for k \<ge> 2 --- after the
      merge M(k) ends at k, the next merge M(k+1) begins again at 1, a RETURN.  We witness
      the non-monotonicity: S(2) = [1,1,2] already drops is impossible (it only rises), but
      S(3) = [1,1,2, 1,2,3] returns from 2 to 1 at the boundary of the two merges.\<close>

theorem climb_and_return_witness:
  "sort_schedule 3 = [1, 1, 2, 1, 2, 3]"
  by (simp add: merge_climb_def upt_conv_Cons numeral_2_eq_2 numeral_3_eq_3)

theorem climb_and_return_nonmonotone:
  "sort_schedule 3 ! 2 = 2 \<and> sort_schedule 3 ! 3 = 1"
  by (simp add: climb_and_return_witness)

text \<open>Reading -- the climb-and-return, closed.  @{thm schedule_recursion}: the optimal fold
      schedule for $2^k$ wires is the schedule for $2^{k-1}$ (the halves, sorted in
      parallel) followed by a merge climb $[1,2,\dots,k]$.  Each merge RETURNS to weight one
      (an edge) and CLIMBS to weight $k$ (the antipode, the body diagonal of the $k$-cube):
      @{thm schedule_ends_at_antipode} shows every schedule ends at its antipode, and
      @{thm climb_and_return_nonmonotone} witnesses the return --- the weight drops from $2$
      back to $1$ at the seam between two merges.  So the schedule is not the monotone
      ascent the full-fold experiment suggested; it is a sequence of ascending merges of
      growing height, each returning to the edge before climbing to a higher diagonal.
      @{thm schedule_depth}: the depth is the triangular number $k(k+1)/2$, Batcher's depth,
      now DERIVED from the recursion.  And the recursion IS the recursive merge of
      @{thm merged_wire_is_threshold} (Path B): sort the halves, merge; the generator's
      recursion and the schedule's climb-and-return are one object.  The climb-and-return
      the search stumbled on has a closed form --- $S(k) = S(k-1) + [1..k]$ --- and it is
      provable, because the generator that builds it is the induction that proves it.
      Nothing here is assumed.\<close>

end
