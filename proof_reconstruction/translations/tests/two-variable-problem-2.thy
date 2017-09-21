theory "two-variable-problem-2"
  imports "../GenerateATP"
    "~/Documents/internship/verified-metitarski/isabelle-proofs/ExpBounds"
begin
 
(* SOS takes more than 5 sec*)  
lemma "\<forall>(X::real).(\<forall>(Y::real).(((Not((X <= 0)) \<and> Not((Y <= 0))) --> Not((exp(X) <= exp(((X * Y) / (X + Y))))))))"
  apply(tactic {*fn st => (writeln (isar_proof st [] @{context}); Seq.single st) *})
proof -
  { fix rr :: real and rra :: real
    have ff1: "exp (rra * rr / (rr + rra)) < exp rr \<or> rr \<le> rra * rr / (rr + rra)"
      using exp_monotone2 by blast (* 0.0 ms *)
    have ff2: "rra * rr / (rr + rra) < rr \<or> rr * (rr + rra) \<le> rra * rr \<or> rr + rra \<le> 0"
      using leq_left_mul_divide_pos by auto (* 4 ms *)
    have "\<not> rr * - 1 < rra \<or> \<not> rra \<le> rr * - 1"
      by simp (* 0.0 ms *)
    moreover
    { assume "\<not> rra \<le> rr * - 1"
      then have "\<not> 0 < rr * rr \<and> \<not> rra \<le> rr * - 1 \<or> \<not> rr * rr \<le> 0 \<and> \<not> rra \<le> rr * - 1"
        by fastforce (* 4 ms *)
      moreover
      { assume "\<not> rr * rr \<le> 0 \<and> \<not> rra \<le> rr * - 1"
        then have "\<not> rr * (rr + rra) \<le> rra * rr \<and> \<not> rr + rra \<le> 0"
          by mt_arith_rule (* 12 ms *)
        then have "\<not> rr \<le> rra * rr / (rr + rra)"
          using ff2 by force (* 4 ms *)
        then have "\<not> exp rr \<le> exp (rra * rr / (rr + rra))"
          using ff1 by fastforce (* 0.0 ms *)
        then have "\<not> exp rr \<le> exp (rr * rra / (rr + rra))"
          by mt_arith_rule (* 60 ms *)
        then have "\<not> 0 < rr \<or> \<not> 0 < rra \<or> \<not> exp rr \<le> exp (rr * rra / (rr + rra))"
          by metis (* 4 ms *) }
      moreover
      { assume "\<not> 0 < rr * rr \<and> \<not> rra \<le> rr * - 1"
        then have "\<not> 0 < rr \<or> \<not> 0 < rra"
          sorry (*by sos*) (* > 5.0 s, timed out *) }
      ultimately have "0 < rra \<and> 0 < rr \<longrightarrow> \<not> 0 < rr \<or> \<not> 0 < rra \<or> \<not> exp rr \<le> exp (rr * rra / (rr + rra))"
        by metis (* 16 ms *) }
    moreover
    { assume "\<not> rr * - 1 < rra"
      then have "\<not> 0 < rr \<or> \<not> 0 < rra"
        by sos (* 20 ms *) }
    ultimately have "0 < rra \<and> 0 < rr \<longrightarrow> \<not> 0 < rr \<or> \<not> 0 < rra \<or> \<not> exp rr \<le> exp (rr * rra / (rr + rra))"
      by metis (* 12 ms *)
    moreover
    { assume "\<not> 0 < rra"
      then have "\<not> 0 < rr \<or> \<not> 0 < rra \<or> \<not> exp rr \<le> exp (rr * rra / (rr + rra))"
        by metis (* 4 ms *) }
    moreover
    { assume "\<not> 0 < rr"
      then have "\<not> 0 < rr \<or> \<not> 0 < rra \<or> \<not> exp rr \<le> exp (rr * rra / (rr + rra))"
        by metis (* 4 ms *) }
    ultimately have "\<not> 0 < rr \<or> \<not> 0 < rra \<or> \<not> exp rr \<le> exp (rr * rra / (rr + rra))"
      by metis (* 8 ms *) }
  then have "\<forall>r ra. \<not> (0::real) < r \<or> \<not> 0 < ra \<or> \<not> exp r \<le> exp (r * ra / (r + ra))"
    by blast (* 0.0 ms *)
  then show ?thesis
    by auto (* 12 ms *)
qed
  
end
  