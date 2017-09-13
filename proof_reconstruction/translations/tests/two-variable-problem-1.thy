theory "two-variable-problem-1"
  imports "../GenerateATP"
begin
 
(*SOS fails! And it's not because of division*)
(*Need to change "show" statement*)  
lemma "\<forall>(X::real).(\<forall>(Y::real).(((Not((Y <= 0)) \<and> Not((X <= Y))) --> Not(((ln((X / Y)) / 2) <= ((X - Y) / (X + Y)))))))"  
  apply(tactic {*fn st => (writeln (isar_proof st [] @{context}); Seq.single st) *})
proof -
  { fix rr :: real and rra :: real
    have ff1: "0 < rra / rr \<or> rra \<le> 0 * rr \<or> rr \<le> 0"
      using leq_right_mul_divide_pos by blast (* 4 ms *)
    have ff2: "rra + rr * - 1 < (rra * (rra * (rra * (5 / 4))) + rr * (rra * (rra * (1 / 4)) + rr * (rra * (- 5 / 4) + rr * (- 1 / 4)))) / (rra * rra + rr * (rra * 2)) \<or> rra * (rra * (rra * (5 / 4))) + rr * (rra * (rra * (1 / 4)) + rr * (rra * (- 5 / 4) + rr * (- 1 / 4))) \<le> (rra + rr * - 1) * (rra * rra + rr * (rra * 2)) \<or> rra * rra + rr * (rra * 2) \<le> 0"
      using leq_right_mul_divide_pos by blast (* 4 ms *)
    have ff3: "(rra + rr * - 1) / (rra * (1 / 2) + rr * (1 / 2)) < (rra * (rra * (5 / 2)) + rr * (rra * - 2 + rr * (- 1 / 2))) / (rra * rra + rr * (rra * 2)) \<or> (rra * (rra * (5 / 2)) + rr * (rra * - 2 + rr * (- 1 / 2))) / (rra * rra + rr * (rra * 2)) * (rra * (1 / 2) + rr * (1 / 2)) \<le> rra + rr * - 1 \<or> rra * (1 / 2) + rr * (1 / 2) \<le> 0"
      using leq_left_mul_divide_pos by blast (* 4 ms *)
    have ff4: "(rra + rr * - 1) / (rra + rr) < ln (rra / rr) * (1 / 2) \<or> ln (rra / rr) * (1 / 2) * (rra + rr) \<le> rra + rr * - 1 \<or> rra + rr \<le> 0"
      using leq_left_mul_divide_pos by blast (* 4 ms *)
    have ff5: "\<And>r ra. ra < ln r \<or> \<not> lgen True ra (ln r)"
      using lgen_less_neg by auto (* 0.0 ms *)
    have "\<And>r ra. \<not> lgen True ra (1 / 2 * (1 + 5 * r) * (r - 1) / (r * (2 + r))) \<or> r \<le> 0 \<or> lgen True ra (ln r)"
      using ln_lower_bound_cf3 by blast (* 4 ms *)
    then have "\<And>r ra. ra < ln r \<or> \<not> lgen True ra (1 / 2 * (1 + 5 * r) * (r - 1) / (r * (2 + r))) \<or> r \<le> 0"
      using ff5 by blast (* 4 ms *)
    then have "\<And>r ra. (ra::real) < ln r \<or> r \<le> 0 \<or> (- 1 / 2 + r * (- 2 + r * (5 / 2))) / (r * (2 + r)) \<le> ra"
      sorry (* failed *)
    then have ff6: "(rra + rr * - 1) / (rra * (1 / 2) + rr * (1 / 2)) < ln (rra / rr) \<or> (- 1 / 2 + rra / rr * (- 2 + rra / rr * (5 / 2))) / (rra / rr * (2 + rra / rr)) \<le> (rra + rr * - 1) / (rra * (1 / 2) + rr * (1 / 2)) \<or> rra / rr \<le> 0"
      by blast (* 0.0 ms *)
    have "\<not> 0 < rra \<or> \<not> rra \<le> 0"
      by auto (* 0.0 ms *)
    moreover
    { assume "\<not> rra \<le> 0"
      then have "\<not> rra \<le> 0 * rr"
        sorry (* failed *)
      then have "0 < rr \<longrightarrow> \<not> rra \<le> 0 * rr \<and> \<not> rr \<le> 0"
        by simp (* 0.0 ms *)
      moreover
      { assume "\<not> rra \<le> 0 * rr \<and> \<not> rr \<le> 0"
        then have "\<not> rra / rr \<le> 0"
          using ff1 by fastforce (* 4 ms *)
        then have "rra * (rra * - 1) < rr * (rra * 2) \<longrightarrow> \<not> rr * (rra * 2) \<le> rra * (rra * - 1) \<and> \<not> rra / rr \<le> 0"
          by auto (* 4 ms *)
        moreover
        { assume "\<not> rr * (rra * 2) \<le> rra * (rra * - 1) \<and> \<not> rra / rr \<le> 0"
          then have "\<not> rra * (rra * (rra * (- 1 / 4))) < rr * (rra * (rra * (- 3 / 4)) + rr * (rra * (3 / 4) + rr * (- 1 / 4))) \<and> \<not> rr * (rra * 2) \<le> rra * (rra * - 1) \<or> \<not> rr * (rra * 2) \<le> rra * (rra * - 1) \<and> \<not> rr * (rra * (rra * (- 3 / 4)) + rr * (rra * (3 / 4) + rr * (- 1 / 4))) \<le> rra * (rra * (rra * (- 1 / 4))) \<and> \<not> rra / rr \<le> 0"
            by auto (* 40 ms *)
          moreover
          { assume "\<not> rr * (rra * 2) \<le> rra * (rra * - 1) \<and> \<not> rr * (rra * (rra * (- 3 / 4)) + rr * (rra * (3 / 4) + rr * (- 1 / 4))) \<le> rra * (rra * (rra * (- 1 / 4))) \<and> \<not> rra / rr \<le> 0"
            then have "\<not> rra * (rra * (rra * (5 / 4))) + rr * (rra * (rra * (1 / 4)) + rr * (rra * (- 5 / 4) + rr * (- 1 / 4))) \<le> (rra + rr * - 1) * (rra * rra + rr * (rra * 2)) \<and> \<not> rra * rra + rr * (rra * 2) \<le> 0 \<and> \<not> rra / rr \<le> 0"
              sorry (* failed *)
            then have "\<not> (rra * (rra * (rra * (5 / 4))) + rr * (rra * (rra * (1 / 4)) + rr * (rra * (- 5 / 4) + rr * (- 1 / 4)))) / (rra * rra + rr * (rra * 2)) \<le> rra + rr * - 1 \<and> \<not> rra / rr \<le> 0"
              using ff2 by auto (* 76 ms *)
            then have "rra * - 1 < rr \<longrightarrow> \<not> (rra * (rra * (rra * (5 / 4))) + rr * (rra * (rra * (1 / 4)) + rr * (rra * (- 5 / 4) + rr * (- 1 / 4)))) / (rra * rra + rr * (rra * 2)) \<le> rra + rr * - 1 \<and> \<not> rra / rr \<le> 0 \<and> \<not> rr \<le> rra * - 1"
              by simp (* 8 ms *)
            moreover
            { assume "\<not> (rra * (rra * (rra * (5 / 4))) + rr * (rra * (rra * (1 / 4)) + rr * (rra * (- 5 / 4) + rr * (- 1 / 4)))) / (rra * rra + rr * (rra * 2)) \<le> rra + rr * - 1 \<and> \<not> rra / rr \<le> 0 \<and> \<not> rr \<le> rra * - 1"
              then have "\<not> (rra * (rra * (5 / 2)) + rr * (rra * - 2 + rr * (- 1 / 2))) / (rra * rra + rr * (rra * 2)) * (rra * (1 / 2) + rr * (1 / 2)) \<le> rra + rr * - 1 \<and> \<not> rra * (1 / 2) + rr * (1 / 2) \<le> 0 \<and> \<not> rra / rr \<le> 0"
                sorry (* failed *)
              then have "\<not> (rra * (rra * (5 / 2)) + rr * (rra * - 2 + rr * (- 1 / 2))) / (rra * rra + rr * (rra * 2)) \<le> (rra + rr * - 1) / (rra * (1 / 2) + rr * (1 / 2)) \<and> \<not> rra / rr \<le> 0"
                using ff3 by simp (* 76 ms *)
              then have "rr = 0 \<or> \<not> (rra * (rra * (5 / 2)) + rr * (rra * - 2 + rr * (- 1 / 2))) / (rra * rra + rr * (rra * 2)) \<le> (rra + rr * - 1) / (rra * (1 / 2) + rr * (1 / 2)) \<and> \<not> rra / rr \<le> 0 \<and> rr \<noteq> 0"
                by fastforce (* 0.0 ms *)
              moreover
              { assume "\<not> (rra * (rra * (5 / 2)) + rr * (rra * - 2 + rr * (- 1 / 2))) / (rra * rra + rr * (rra * 2)) \<le> (rra + rr * - 1) / (rra * (1 / 2) + rr * (1 / 2)) \<and> \<not> rra / rr \<le> 0 \<and> rr \<noteq> 0"
                then have "rr * rr = 0 \<and> rr \<noteq> 0 \<or> \<not> (rra * (rra * (5 / 2)) + rr * (rra * - 2 + rr * (- 1 / 2))) / (rra * rra + rr * (rra * 2)) \<le> (rra + rr * - 1) / (rra * (1 / 2) + rr * (1 / 2)) \<and> \<not> rra / rr \<le> 0 \<and> rr * rr \<noteq> 0 \<and> rr \<noteq> 0"
                  by force (* 0.0 ms *)
                moreover
                { assume "\<not> (rra * (rra * (5 / 2)) + rr * (rra * - 2 + rr * (- 1 / 2))) / (rra * rra + rr * (rra * 2)) \<le> (rra + rr * - 1) / (rra * (1 / 2) + rr * (1 / 2)) \<and> \<not> rra / rr \<le> 0 \<and> rr * rr \<noteq> 0 \<and> rr \<noteq> 0"
                  then have "\<not> (- 1 / 2 + rra / rr * (- 2 + rra / rr * (5 / 2))) / (rra / rr * (2 + rra / rr)) \<le> (rra + rr * - 1) / (rra * (1 / 2) + rr * (1 / 2)) \<and> \<not> rra / rr \<le> 0"
                    sorry (* failed *)
                  then have "\<not> ln (rra / rr) \<le> (rra + rr * - 1) / (rra * (1 / 2) + rr * (1 / 2))"
                    using ff6 by simp (* 16 ms *)
                  then have "rra * - 1 < rr \<longrightarrow> \<not> ln (rra / rr) \<le> (rra + rr * - 1) / (rra * (1 / 2) + rr * (1 / 2)) \<and> \<not> rr \<le> rra * - 1"
                    by auto (* 4 ms *)
                  moreover
                  { assume "\<not> ln (rra / rr) \<le> (rra + rr * - 1) / (rra * (1 / 2) + rr * (1 / 2)) \<and> \<not> rr \<le> rra * - 1"
                    then have "\<not> ln (rra / rr) * (rra * (1 / 2) + rr * (1 / 2)) \<le> rra + rr * - 1"
                      sorry (* failed *)
                    then have "rra * - 1 < rr \<longrightarrow> \<not> ln (rra / rr) * (rra * (1 / 2) + rr * (1 / 2)) \<le> rra + rr * - 1 \<and> \<not> rr \<le> rra * - 1"
                      by auto (* 4 ms *)
                    moreover
                    { assume "\<not> ln (rra / rr) * (rra * (1 / 2) + rr * (1 / 2)) \<le> rra + rr * - 1 \<and> \<not> rr \<le> rra * - 1"
                      then have "\<not> ln (rra / rr) * (1 / 2) * (rra + rr) \<le> rra + rr * - 1 \<and> \<not> rra + rr \<le> 0"
                        sorry (* failed *)
                      then have "\<not> ln (rra / rr) * (1 / 2) \<le> (rra + rr * - 1) / (rra + rr)"
                        using ff4 by simp (* 12 ms *)
                      then have "\<not> ln (rra / rr) / 2 \<le> (rra - rr) / (rra + rr)"
                        sorry (* failed *)
                      then have "\<not> rr < rra \<or> \<not> 0 < rr \<or> \<not> ln (rra / rr) / 2 \<le> (rra - rr) / (rra + rr)"
                        by metis (* 4 ms *) }
                    ultimately have "rra * - 1 < rr \<longrightarrow> \<not> rr < rra \<or> \<not> 0 < rr \<or> \<not> ln (rra / rr) / 2 \<le> (rra - rr) / (rra + rr)"
                      by metis (* 8 ms *) }
                  ultimately have "rra * - 1 < rr \<longrightarrow> \<not> rr < rra \<or> \<not> 0 < rr \<or> \<not> ln (rra / rr) / 2 \<le> (rra - rr) / (rra + rr)"
                    by metis (* 12 ms *) }
                moreover
                { assume "rr * rr = 0 \<and> rr \<noteq> 0"
                  then have "\<not> rr < rra \<or> \<not> 0 < rr"
                    by sos (* 56 ms *) }
                ultimately have "rra * - 1 < rr \<and> 0 < rr \<and> rr < rra \<longrightarrow> \<not> rr < rra \<or> \<not> 0 < rr \<or> \<not> ln (rra / rr) / 2 \<le> (rra - rr) / (rra + rr)"
                  by metis (* 48 ms *) }
              moreover
              { assume "rr = 0"
                then have "\<not> rr < rra \<or> \<not> 0 < rr"
                  by sos (* 12 ms *) }
              ultimately have "rra * - 1 < rr \<and> 0 < rr \<and> rr < rra \<longrightarrow> \<not> rr < rra \<or> \<not> 0 < rr \<or> \<not> ln (rra / rr) / 2 \<le> (rra - rr) / (rra + rr)"
                by metis (* 20 ms *) }
            ultimately have "rra * - 1 < rr \<and> 0 < rr \<and> rr < rra \<longrightarrow> \<not> rr < rra \<or> \<not> 0 < rr \<or> \<not> ln (rra / rr) / 2 \<le> (rra - rr) / (rra + rr)"
              by metis (* 16 ms *)
            moreover
            { assume "\<not> rra * - 1 < rr"
              then have "\<not> rr < rra \<or> \<not> 0 < rr"
                by sos (* 44 ms *) }
            ultimately have "0 < rr \<and> rr < rra \<longrightarrow> \<not> rr < rra \<or> \<not> 0 < rr \<or> \<not> ln (rra / rr) / 2 \<le> (rra - rr) / (rra + rr)"
              by metis (* 8 ms *) }
          moreover
          { assume "\<not> rra * (rra * (rra * (- 1 / 4))) < rr * (rra * (rra * (- 3 / 4)) + rr * (rra * (3 / 4) + rr * (- 1 / 4))) \<and> \<not> rr * (rra * 2) \<le> rra * (rra * - 1)"
            then have "\<not> rr < rra \<or> \<not> 0 < rr"
              by sos (* > 5.0 s, timed out *) }
          ultimately have "0 < rr \<and> rr < rra \<longrightarrow> \<not> rr < rra \<or> \<not> 0 < rr \<or> \<not> ln (rra / rr) / 2 \<le> (rra - rr) / (rra + rr)"
            by metis (* 40 ms *) }
        moreover
        { assume "\<not> rra * (rra * - 1) < rr * (rra * 2)"
          then have "\<not> rr < rra \<or> \<not> 0 < rr"
            by sos (* 16 ms *) }
        ultimately have "0 < rr \<and> rr < rra \<longrightarrow> \<not> rr < rra \<or> \<not> 0 < rr \<or> \<not> ln (rra / rr) / 2 \<le> (rra - rr) / (rra + rr)"
          by metis (* 56 ms *) }
      ultimately have "0 < rr \<and> rr < rra \<longrightarrow> \<not> rr < rra \<or> \<not> 0 < rr \<or> \<not> ln (rra / rr) / 2 \<le> (rra - rr) / (rra + rr)"
        by metis (* 12 ms *) }
    moreover
    { assume "\<not> 0 < rra"
      then have "\<not> rr < rra \<or> \<not> 0 < rr"
        by sos (* 16 ms *) }
    ultimately have "0 < rr \<and> rr < rra \<longrightarrow> \<not> rr < rra \<or> \<not> 0 < rr \<or> \<not> ln (rra / rr) / 2 \<le> (rra - rr) / (rra + rr)"
      by metis (* 12 ms *)
    moreover
    { assume "\<not> 0 < rr"
      then have "\<not> rr < rra \<or> \<not> 0 < rr \<or> \<not> ln (rra / rr) / 2 \<le> (rra - rr) / (rra + rr)"
        by metis (* 0.0 ms *) }
    moreover
    { assume "\<not> rr < rra"
      then have "\<not> rr < rra \<or> \<not> 0 < rr \<or> \<not> ln (rra / rr) / 2 \<le> (rra - rr) / (rra + rr)"
        by metis (* 4 ms *) }
    ultimately have "\<not> rr < rra \<or> \<not> 0 < rr \<or> \<not> ln (rra / rr) / 2 \<le> (rra - rr) / (rra + rr)"
      by metis (* 8 ms *) }
  then have "\<forall>r ra. \<not> (ra::real) < r \<or> \<not> 0 < ra \<or> \<not> ln (r / ra) / 2 \<le> (r - ra) / (r + ra)"
    by blast (* 0.0 ms *)
  then show ?thesis
    by auto (* 4 ms *)
qed

end
  