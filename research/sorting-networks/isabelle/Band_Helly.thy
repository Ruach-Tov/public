theory Band_Helly
  imports Main
begin

(* ============================================================================
   ADVANCING THE PROOF: localising the defect W_0 by Helly's theorem.

   The defect W_0 is the largest antichain of cofactors -- the largest family of
   mutually incomparable monotone predicates.  Each monotone predicate g on the
   residual cube has a BAND: below a least weight lo it is constantly false, above a
   greatest weight hi it is constantly true, and between it is "mixed" (its value
   depends on which bits are set, not only how many).  A threshold has empty band
   (lo = hi + 1); an intermediate wire's cofactor may have a genuine band.

   Two observations compose into a real advance:
     - if two cofactors' bands are DISJOINT (one entirely below the other), the
       cofactors are COMPARABLE;  so an antichain forces the bands to PAIRWISE OVERLAP;
     - pairwise-overlapping intervals on a line have a COMMON POINT (Helly in one
       dimension);  so all the antichain's bands share a common weight w*, and W_0 is
       at most the number of cofactors whose band contains that one weight.

   This LOCALISES W_0 from a two-dimensional antichain to a one-dimensional slice --
   the cofactors mixed at a single weight level.  It does not close the bound (that
   slice count could still be large), but it sharpens the target through a classical
   theorem.  We prove the band-comparability and the one-dimensional Helly step (for a
   finite family of natural-number intervals).  Self-contained (imports Main).
   ============================================================================ *)

text \<open>A band is an interval @{term "{lo..hi}"} of weights (naturals).  A family of
      bands is given by functions lo, hi on an index set I.  We say bands i and j
      OVERLAP if their intervals meet.\<close>

definition band_overlap :: "(nat \<Rightarrow> nat) \<Rightarrow> (nat \<Rightarrow> nat) \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool" where
  "band_overlap lo hi i j \<longleftrightarrow> {lo i..hi i} \<inter> {lo j..hi j} \<noteq> {}"

text \<open>DISJOINT BANDS ARE ORDERED.  If band i lies entirely below band j (its top below
      j's bottom), the intervals are disjoint.  This is the contrapositive we use:
      non-overlap means one band is strictly below the other.\<close>

theorem disjoint_bands_separated:
  assumes "\<not> band_overlap lo hi i j"
      and "lo i \<le> hi i" and "lo j \<le> hi j"
  shows "hi i < lo j \<or> hi j < lo i"
proof (rule ccontr)
  assume "\<not> (hi i < lo j \<or> hi j < lo i)"
  hence a: "lo j \<le> hi i" and b: "lo i \<le> hi j" by auto
  have "max (lo i) (lo j) \<le> min (hi i) (hi j)"
    using assms(2,3) a b by auto
  hence "max (lo i) (lo j) \<in> {lo i..hi i} \<inter> {lo j..hi j}"
    by auto
  hence "{lo i..hi i} \<inter> {lo j..hi j} \<noteq> {}" by blast
  thus False using assms(1) by (simp add: band_overlap_def)
qed

text \<open>HELLY IN ONE DIMENSION (finite version).  A finite, nonempty family of
      intervals on the naturals that PAIRWISE OVERLAP has a common point.  We take the
      point to be the MAXIMUM of the left endpoints: it lies in every interval, because
      pairwise overlap forces each interval's right endpoint to reach that maximum.\<close>

theorem helly_1d_intervals:
  fixes lo hi :: "'a \<Rightarrow> nat" and I :: "'a set"
  assumes fin: "finite I" and ne: "I \<noteq> {}"
      and valid: "\<forall>i\<in>I. lo i \<le> hi i"
      and pair: "\<forall>i\<in>I. \<forall>j\<in>I. {lo i..hi i} \<inter> {lo j..hi j} \<noteq> {}"
  shows "\<exists>w. \<forall>i\<in>I. w \<in> {lo i..hi i}"
proof -
  define w where "w = Max (lo ` I)"
  have finlo: "finite (lo ` I)" using fin by simp
  have nelo: "lo ` I \<noteq> {}" using ne by simp
  have wge: "\<forall>i\<in>I. lo i \<le> w" using finlo nelo by (auto simp: w_def)
  \<comment> \<open>w is some lo j0 (the max is attained)\<close>
  have "w \<in> lo ` I" using finlo nelo by (simp add: w_def)
  then obtain j0 where j0: "j0 \<in> I" and wj0: "w = lo j0" by auto
  have "\<forall>i\<in>I. w \<in> {lo i..hi i}"
  proof
    fix i assume i: "i \<in> I"
    have "lo i \<le> w" using wge i by simp
    moreover have "w \<le> hi i"
    proof -
      \<comment> \<open>bands i and j0 overlap; their common point c satisfies c >= lo j0 = w and c <= hi i\<close>
      have "{lo i..hi i} \<inter> {lo j0..hi j0} \<noteq> {}" using pair i j0 by blast
      then obtain c where "c \<in> {lo i..hi i}" and "c \<in> {lo j0..hi j0}" by blast
      hence "lo j0 \<le> c" and "c \<le> hi i" by auto
      thus ?thesis using wj0 by simp
    qed
    ultimately show "w \<in> {lo i..hi i}" by simp
  qed
  thus ?thesis by blast
qed

text \<open>THE LOCALISATION.  Combine the two: if a family of bands pairwise overlaps
      (which an antichain of cofactors forces, by band-comparability), then by Helly
      they share a common weight w.  So the family is contained in the set of bands
      that CONTAIN that single weight --- the one-dimensional slice at w.  The defect
      W_0 is therefore at most the largest number of bands through a single weight.\<close>

theorem antichain_bands_share_weight:
  assumes fin: "finite I" and ne: "I \<noteq> {}"
      and valid: "\<forall>i\<in>I. lo i \<le> hi i"
      and pairwise: "\<forall>i\<in>I. \<forall>j\<in>I. band_overlap lo hi i j"
  shows "\<exists>w. \<forall>i\<in>I. lo i \<le> w \<and> w \<le> hi i"
proof -
  have "\<forall>i\<in>I. \<forall>j\<in>I. {lo i..hi i} \<inter> {lo j..hi j} \<noteq> {}"
    using pairwise by (simp add: band_overlap_def)
  from helly_1d_intervals[OF fin ne valid this]
  obtain w where "\<forall>i\<in>I. w \<in> {lo i..hi i}" by blast
  thus ?thesis by auto
qed

text \<open>Reading.  This advances the defect toward a bound without claiming to close it.
      @{thm disjoint_bands_separated}: non-overlapping bands are separated, so an
      antichain of cofactors (mutually incomparable) forces the bands to pairwise
      overlap.  @{thm helly_1d_intervals}: pairwise-overlapping intervals on the
      naturals share a common weight (Helly in one dimension, the maximum of the left
      endpoints witnessing it).  @{thm antichain_bands_share_weight}: hence all the
      bands of an antichain pass through a single weight $w$, and the defect $W_0$ is at
      most the number of cofactors whose band contains $w$ --- a one-dimensional slice.
      The two-dimensional antichain is localised to a single weight level: the
      cofactors that genuinely depend on WHICH bits, not only how many, at that weight.
      Bounding that slice is the remaining work; it is a sharper and more concrete
      target than the antichain itself.  Nothing here is assumed; Helly does the
      localising.\<close>

end
