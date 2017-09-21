theory "cos-problem-4"
  imports "../GenerateATP"
    "~/Documents/internship/verified-metitarski/isabelle-proofs/CosBounds"
    "~/Documents/internship/verified-metitarski/isabelle-proofs/PiBounds"
begin
  
(* Looks like "decision" accepts pi but sos doesn't *)  
lemma "\<forall>(X::real).((((0 <= X) \<and> (X <= pi)) --> (cos(X) <= 1)))"
  apply(tactic {*fn st => (writeln (isar_proof st [] @{context}); Seq.single st) *})
proof -
  { fix rr :: real
    have ff1: "\<And>r ra. \<not> lgen False (cos ra) r \<or> cos ra \<le> r"
      using lgen_le_neg by blast (* 0.0 ms *)
    have "\<And>r ra. \<not> lgen False (1 - ra\<^sup>2 / 2 + ra ^ 4 / 24) r \<or> lgen False (cos ra) r"
      using cos_upper_bound_0 by blast (* 0.0 ms *)
    then have "\<And>r ra. \<not> lgen False (1 - ra\<^sup>2 / 2 + ra ^ 4 / 24) r \<or> cos ra \<le> r"
      using ff1 by blast (* 0.0 ms *)
    then have "\<And>r ra. (ra::real) < 1 + r * (r * (- 1 / 2 + r * (r * (1 / 24)))) \<or> cos r \<le> ra"
      by mt_arith_rule (* failed *)
    then have ff2: "1 < 1 + rr * (rr * (- 1 / 2 + rr * (rr * (1 / 24)))) \<or> cos rr \<le> 1"
      by auto (* 4 ms *)
    have "\<not> rr * (rr * (- 1 / 2 + rr * (rr * (1 / 24)))) \<le> 0 \<or> \<not> 0 < rr * (rr * (- 1 / 2 + rr * (rr * (1 / 24))))"
      by auto (* 12 ms *)
    moreover
    { assume "\<not> 0 < rr * (rr * (- 1 / 2 + rr * (rr * (1 / 24))))"
      then have "\<not> 1 < 1 + rr * (rr * (- 1 / 2 + rr * (rr * (1 / 24))))"
        by mt_arith_rule (* 24 ms *)
      then have "\<not> 1 < cos rr"
        using ff2 by fastforce (* 44 ms *)
      then have "\<not> 1 < cos rr \<or> \<not> 0 \<le> rr \<or> \<not> rr \<le> pi"
        by metis (* 4 ms *) }
    moreover
    { assume "\<not> rr * (rr * (- 1 / 2 + rr * (rr * (1 / 24)))) \<le> 0"
      then have "\<not> rr \<le> pi \<or> \<not> 0 \<le> rr"
        using pi_lower_bound pi_upper_bound by sos (* failed *)
      moreover
      { assume "\<not> 0 \<le> rr"
        then have "\<not> 1 < cos rr \<or> \<not> 0 \<le> rr \<or> \<not> rr \<le> pi"
          by metis (* 4 ms *) }
      moreover
      { assume "\<not> rr \<le> pi"
        then have "\<not> 1 < cos rr \<or> \<not> 0 \<le> rr \<or> \<not> rr \<le> pi"
          by metis (* 4 ms *) }
      ultimately have "\<not> 1 < cos rr \<or> \<not> 0 \<le> rr \<or> \<not> rr \<le> pi"
        by metis (* 4 ms *) }
    ultimately have "\<not> 1 < cos rr \<or> \<not> 0 \<le> rr \<or> \<not> rr \<le> pi"
      by metis (* 16 ms *) }
  then have "\<forall>r. \<not> 1 < cos r \<or> \<not> r \<le> pi \<or> \<not> 0 \<le> r"
    by blast (* 4 ms *)
  then show ?thesis
    by auto (* 4 ms *)
qed
  
end
  