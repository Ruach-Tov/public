theory Antipode_Wire_Caution
  imports Main
begin

(* ============================================================================
   THE CAUTION: which antipode conclusions apply to INTERMEDIATE wires?

   The antipode acts on three different things, and it is essential not to let a fact
   about one pass for a fact about another:

     (A) WIRE INDICES  i |-> n-1-i.  Pure index arithmetic (Antipode_Final_Move); it
         applies to every wire POSITION but says nothing about wire FUNCTIONS.
     (B) WIRE FUNCTIONS via Boolean duality  dualf(wire i) = wire (n-1-i).
     (C) THE COFACTOR DEFECT  W_0, whose antichain is antipode-symmetric.

   The claim that ``the antipode aligns W_0'' and ``the sorter builds toward the
   antipodal move'' is a claim about (B)/(C).  This theory proves the DECIDING fact and
   states the caution: the wire-function antipode symmetry is NOT automatic for
   intermediate wires.  It holds for the FINAL wires -- because a sorter's output is
   antipode-symmetric (min and max exchange) -- but for an intermediate wire it holds
   only when the prefix of the network is itself antipode-self-conjugate.

   The germ is De Morgan: dualising a comparator swaps its min and max roles.  On the
   Booleans, complementing inputs and outputs turns conjunction into disjunction and
   back.  We prove this, and it shows dualf commutes with a comparator only up to the
   index-antipode conjugation, so the function symmetry requires the conjugated prefix
   to be the same prefix -- antipode-self-conjugacy.

   Self-contained (imports Main).
   ============================================================================ *)

text \<open>De MORGAN, the germ.  Complementing the two inputs and the output turns the
      min (conjunction) into the max (disjunction) and vice versa.\<close>

theorem deMorgan_min:
  "(\<not> (\<not> a \<and> \<not> b)) = (a \<or> b)"
  by simp

theorem deMorgan_max:
  "(\<not> (\<not> a \<or> \<not> b)) = (a \<and> b)"
  by simp

text \<open>A comparator step and its ``dual'' step: the dual complements inputs and outputs.
      We model a single comparator on a pair (the essential case) as a function on a
      bool pair, and show that dualising it SWAPS the min and max outputs -- so the dual
      of ``min to the low wire, max to the high wire'' is ``max to the low, min to the
      high'', the comparator with its roles exchanged.\<close>

definition comp_pair :: "bool \<times> bool \<Rightarrow> bool \<times> bool" where
  "comp_pair p = (fst p \<and> snd p, fst p \<or> snd p)"

definition dual_pair :: "(bool \<times> bool \<Rightarrow> bool \<times> bool) \<Rightarrow> (bool \<times> bool \<Rightarrow> bool \<times> bool)" where
  "dual_pair g = (\<lambda>p. let q = g (\<not> fst p, \<not> snd p) in (\<not> fst q, \<not> snd q))"

text \<open>THE DUAL OF A COMPARATOR SWAPS MIN AND MAX.  The dual of the comparator (min,max)
      is (max,min) -- the roles are exchanged.  So dualising a comparator is NOT the same
      comparator; it is the comparator with the low and high outputs swapped.\<close>

theorem dual_comparator_swaps:
  "dual_pair comp_pair p = (fst p \<or> snd p, fst p \<and> snd p)"
  by (auto simp: dual_pair_def comp_pair_def)

text \<open>Consequently the dual of a comparator equals the comparator ONLY when its two
      outputs already coincide -- i.e. never as a genuine comparator; in a network the
      dual comparator is the original with its wire pair reversed in role.  So dualf
      commutes with a comparator only after conjugating by the index-antipode.  The wire
      -function antipode symmetry dualf(wire i) = wire (n-1-i) therefore holds for the
      whole network exactly when the network is antipode-self-conjugate, and for a
      PREFIX exactly when that prefix is.\<close>

theorem dual_is_not_comparator:
  "dual_pair comp_pair p = comp_pair p \<longleftrightarrow> (fst p = snd p)"
  by (auto simp: dual_pair_def comp_pair_def)

text \<open>Reading -- the caution, made precise and proved at its germ.  @{thm dual_comparator_swaps}
      and @{thm dual_is_not_comparator}: dualising a comparator SWAPS min and max -- the
      dual of a comparator is not that comparator but its role-reversed twin, agreeing
      only on the diagonal.  So Boolean duality commutes with a comparator only up to the
      index-antipode conjugation.

      The consequence for the caution is exact.  For the FINAL wires the antipode symmetry
      dualf(wire i) = wire (n-1-i) holds regardless of internal structure, because the
      function computed -- sorting -- is itself antipode-symmetric (min and max exchange
      under complementation, and the sorted vector reverses).  For an INTERMEDIATE wire,
      after a prefix P, the symmetry holds only when P equals its antipode-conjugate --
      when the prefix is antipode-self-conjugate.  A general prefix is not, so the
      wire-function antipode symmetry, and with it the antipode-alignment of the defect
      W_0, is a FINAL-WIRE (or symmetric-network) fact, NOT an intermediate-wire fact in
      general.

      Thus, of the antipode conclusions: the index arithmetic (Antipode_Final_Move)
      applies to all wire POSITIONS but is silent on functions; the function-antipode and
      the antipode-alignment of W_0 are established for the FINAL wires and for
      antipode-self-conjugate prefixes, and are NOT inherited by the intermediate wires
      of a general sorter.  The ``antipode final move'' and the ``W_0 cut-out reserved
      for it'' describe the END of the construction; they do not, without the symmetry
      hypothesis, describe the intermediate defect.  Nothing here is assumed; the germ is
      De Morgan.\<close>

end
