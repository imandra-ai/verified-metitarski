theory "abs-problem-4"
  imports "../GenerateATP"
begin 
  
lemma "\<forall>(X::real).((Not((X <= -1)) --> (((2 * abs(X)) / (2 + X)) <= abs(ln((1 + X))))))" 
  apply(tactic {*fn st => (writeln (isar_proof st [] @{context}); Seq.single st) *})
proof -
  { fix rr :: real
    have ff1: "rr * (3 + rr * (5 / 2)) * (2 + rr) < rr * (6 + rr * (8 + rr * 2)) \<or> 2 + rr \<le> 0 \<or> rr * (6 + rr * (8 + rr * 2)) / (2 + rr) \<le> rr * (3 + rr * (5 / 2))"
      using leq_left_divide_mul_pos by blast (* 8 ms *)
    have ff2: "rr * (3 + rr * (5 / 2)) < rr * 2 / (2 + rr) * (3 + rr * (4 + rr)) \<or> 3 + rr * (4 + rr) \<le> 0 \<or> rr * 2 / (2 + rr) \<le> rr * (3 + rr * (5 / 2)) / (3 + rr * (4 + rr))"
      using leq_right_divide_mul_pos by blast (* 4 ms *)
    have ff3: "rr < 0 \<or> \<bar>rr\<bar> = rr"
      using abs_nonnegative by blast (* 0.0 ms *)
    have "\<bar>ln (1 + rr)\<bar> < rr * 2 / (2 + rr) \<or> \<bar>rr\<bar> \<noteq> rr \<or> \<bar>rr\<bar> * 2 / (2 + rr) \<le> \<bar>ln (1 + rr)\<bar>"
      by auto (* 20 ms *)
    then have ff4: "rr < 0 \<or> \<bar>ln (1 + rr)\<bar> < rr * 2 / (2 + rr) \<or> \<bar>rr\<bar> * 2 / (2 + rr) \<le> \<bar>ln (1 + rr)\<bar>"
      using ff3 by fastforce (* 0.0 ms *)
    have ff5: "ln (1 + rr) < 0 \<or> \<bar>ln (1 + rr)\<bar> = ln (1 + rr)"
      using abs_nonnegative by blast (* 0.0 ms *)
    have "ln (1 + rr) < rr * 2 / (2 + rr) \<or> \<bar>ln (1 + rr)\<bar> \<noteq> ln (1 + rr) \<or> rr * 2 / (2 + rr) \<le> \<bar>ln (1 + rr)\<bar>"
      by auto (* 12 ms *)
    then have ff6: "ln (1 + rr) < 0 \<or> ln (1 + rr) < rr * 2 / (2 + rr) \<or> rr * 2 / (2 + rr) \<le> \<bar>ln (1 + rr)\<bar>"
      using ff5 by fastforce (* 0.0 ms *)
    have ff7: "\<And>r ra. \<not> lgen False ra (ln r) \<or> ra \<le> ln r"
      using lgen_le_neg by auto (* 0.0 ms *)
    have "\<And>r ra. \<not> lgen False ra (1 / 2 * (1 + 5 * r) * (r - 1) / (r * (2 + r))) \<or> r \<le> 0 \<or> lgen False ra (ln r)"
      using ln_lower_bound_cf3 by blast (* 4 ms *)
    then have "\<And>r ra. \<not> lgen False ra (1 / 2 * (1 + 5 * r) * (r - 1) / (r * (2 + r))) \<or> r \<le> 0 \<or> ra \<le> ln r"
      using ff7 by blast (* 12 ms *)
    then have "\<And>r ra. (- (1::real) / 2 + ra * (- 2 + ra * (5 / 2))) / (ra * (2 + ra)) < r \<or> ra \<le> 0 \<or> r \<le> ln ra"
      by mt_arith_rule (* failed *)
    then have ff8: "(- 1 / 2 + (1 + rr) * (- 2 + (1 + rr) * (5 / 2))) / ((1 + rr) * (2 + (1 + rr))) < rr * 2 / (2 + rr) \<or> 1 + rr \<le> 0 \<or> rr * 2 / (2 + rr) \<le> ln (1 + rr)"
      by blast (* 8 ms *)
    have ff9: "rr * (- 3 + rr * (- 1 / 2)) * (2 + rr) < rr * (- 6 + rr * - 4) \<or> 2 + rr \<le> 0 \<or> rr * (- 6 + rr * - 4) / (2 + rr) \<le> rr * (- 3 + rr * (- 1 / 2))"
      using leq_left_divide_mul_pos by blast (* 12 ms *)
    have ff10: "rr * 2 / (2 + rr) * (3 + rr * 2) < rr * (3 + rr * (1 / 2)) \<or> 3 + rr * 2 \<le> 0 \<or> rr * (3 + rr * (1 / 2)) / (3 + rr * 2) \<le> rr * 2 / (2 + rr)"
      using leq_left_divide_mul_pos by blast (* 20 ms *)
    have ff11: "0 \<le> rr \<or> \<bar>rr\<bar> = - rr"
      using abs_negative by blast (* 4 ms *)
    have "\<bar>ln (1 + rr)\<bar> < - rr * 2 / (2 + rr) \<or> \<bar>rr\<bar> \<noteq> - rr \<or> \<bar>rr\<bar> * 2 / (2 + rr) \<le> \<bar>ln (1 + rr)\<bar>"
      by auto (* 36 ms *)
    then have ff12: "\<bar>ln (1 + rr)\<bar> < - rr * 2 / (2 + rr) \<or> 0 \<le> rr \<or> \<bar>rr\<bar> * 2 / (2 + rr) \<le> \<bar>ln (1 + rr)\<bar>"
      using ff11 by force (* 0.0 ms *)
    have ff13: "0 \<le> ln (1 + rr) \<or> \<bar>ln (1 + rr)\<bar> = - ln (1 + rr)"
      using abs_negative by blast (* 0.0 ms *)
    have "- ln (1 + rr) < rr * - 2 / (2 + rr) \<or> \<bar>ln (1 + rr)\<bar> \<noteq> - ln (1 + rr) \<or> rr * - 2 / (2 + rr) \<le> \<bar>ln (1 + rr)\<bar>"
      by auto (* 12 ms *)
    then have ff14: "- ln (1 + rr) < rr * - 2 / (2 + rr) \<or> 0 \<le> ln (1 + rr) \<or> rr * - 2 / (2 + rr) \<le> \<bar>ln (1 + rr)\<bar>"
      using ff13 by fastforce (* 0.0 ms *)
    have ff15: "ln (1 + rr) * - 1 * (2 + rr) < rr * - 2 \<or> 2 + rr \<le> 0 \<or> rr * - 2 / (2 + rr) \<le> ln (1 + rr) * - 1"
      using leq_left_divide_mul_pos by blast (* 4 ms *)
    have ff16: "\<And>r ra. \<not> lgen False (ln ra) r \<or> ln ra \<le> r"
      using lgen_le_neg by auto (* 0.0 ms *)
    have "\<And>r ra. \<not> lgen False (1 / 2 * (ra + 5) * (ra - 1) / (2 * ra + 1)) r \<or> ra \<le> 0 \<or> lgen False (ln ra) r"
      using ln_upper_bound_cf3 by blast (* 4 ms *)
    then have "\<And>r ra. \<not> lgen False (1 / 2 * (ra + 5) * (ra - 1) / (2 * ra + 1)) r \<or> ra \<le> 0 \<or> ln ra \<le> r"
      using ff16 by blast (* 0.0 ms *)
    then have "\<And>r ra. (ra::real) < (- 5 / 2 + r * (2 + r * (1 / 2))) / (1 + r * 2) \<or> r \<le> 0 \<or> ln r \<le> ra"
      by mt_arith_rule (* failed *)
    then have ff17: "rr * 2 / (2 + rr) < (- 5 / 2 + (1 + rr) * (2 + (1 + rr) * (1 / 2))) / (1 + (1 + rr) * 2) \<or> 1 + rr \<le> 0 \<or> ln (1 + rr) \<le> rr * 2 / (2 + rr)"
      by blast (* 4 ms *)
    have ff18: "rr * (2 + rr) < rr * (2 + rr * 2) \<or> 2 + rr \<le> 0 \<or> rr * (2 + rr * 2) / (2 + rr) \<le> rr"
      using leq_left_divide_mul_pos by auto (* 4 ms *)
    have ff19: "rr < rr * 2 / (2 + rr) * (1 + rr) \<or> 1 + rr \<le> 0 \<or> rr * 2 / (2 + rr) \<le> rr / (1 + rr)"
      using leq_right_divide_mul_pos by blast (* 4 ms *)
    have ff20: "\<And>r ra. \<not> lgen False ra (ln r) \<or> ra \<le> ln r"
      using lgen_le_neg by auto (* 0.0 ms *)
    have "\<And>r ra. \<not> lgen False ra ((r - 1) / r) \<or> r \<le> 0 \<or> lgen False ra (ln r)"
      using ln_lower_bound_cf1 by blast (* 0.0 ms *)
    then have "\<And>r ra. \<not> lgen False ra ((r - 1) / r) \<or> r \<le> 0 \<or> ra \<le> ln r"
      using ff20 by blast (* 4 ms *)
    then have "\<And>r ra. (- (1::real) + ra) / ra < r \<or> ra \<le> 0 \<or> r \<le> ln ra"
      by mt_arith_rule (* failed *)
    then have ff21: "(- 1 + (1 + rr)) / (1 + rr) < rr * 2 / (2 + rr) \<or> 1 + rr \<le> 0 \<or> rr * 2 / (2 + rr) \<le> ln (1 + rr)"
      by blast (* 4 ms *)
    have "\<not> - 2 < rr \<or> \<not> rr \<le> - 2"
      by fastforce (* 0.0 ms *)
    moreover
    { assume "\<not> rr \<le> - 2"
      then have "\<not> rr * (rr * (rr * (- 1 / 2))) \<le> 0 \<and> \<not> rr \<le> - 2 \<or> \<not> 0 < rr * (rr * (rr * (- 1 / 2))) \<and> \<not> rr \<le> - 2"
        by simp (* 8 ms *)
      moreover
      { assume "\<not> 0 < rr * (rr * (rr * (- 1 / 2))) \<and> \<not> rr \<le> - 2"
        then have "\<not> rr * (3 + rr * (5 / 2)) * (2 + rr) < rr * (6 + rr * (8 + rr * 2)) \<and> \<not> 2 + rr \<le> 0"
          by mt_arith_rule (* failed *)
        then have "\<not> rr * (3 + rr * (5 / 2)) < rr * (6 + rr * (8 + rr * 2)) / (2 + rr)"
          using ff1 by auto (* 84 ms *)
        then have "- 3 < rr * (4 + rr) \<longrightarrow> \<not> rr * (3 + rr * (5 / 2)) < rr * (6 + rr * (8 + rr * 2)) / (2 + rr) \<and> \<not> rr * (4 + rr) \<le> - 3"
          by force (* 12 ms *)
        moreover
        { assume "\<not> rr * (3 + rr * (5 / 2)) < rr * (6 + rr * (8 + rr * 2)) / (2 + rr) \<and> \<not> rr * (4 + rr) \<le> - 3"
          then have "\<not> rr * (3 + rr * (5 / 2)) < rr * 2 / (2 + rr) * (3 + rr * (4 + rr)) \<and> \<not> 3 + rr * (4 + rr) \<le> 0"
            by mt_arith_rule (* failed *)
          then have "\<not> rr * (3 + rr * (5 / 2)) / (3 + rr * (4 + rr)) < rr * 2 / (2 + rr)"
            using ff2 by auto (* 16 ms *)
          then have "- 1 < rr \<longrightarrow> \<not> rr * (3 + rr * (5 / 2)) / (3 + rr * (4 + rr)) < rr * 2 / (2 + rr) \<and> \<not> rr \<le> - 1"
            by fastforce (* 4 ms *)
          moreover
          { assume "\<not> rr * (3 + rr * (5 / 2)) / (3 + rr * (4 + rr)) < rr * 2 / (2 + rr) \<and> \<not> rr \<le> - 1"
            then have "\<not> 0 \<le> rr \<and> \<not> rr \<le> - 1 \<or> \<not> rr < 0 \<and> \<not> rr * (3 + rr * (5 / 2)) / (3 + rr * (4 + rr)) < rr * 2 / (2 + rr) \<and> \<not> rr \<le> - 1"
              by fastforce (* 8 ms *)
            moreover
            { assume "\<not> rr < 0 \<and> \<not> rr * (3 + rr * (5 / 2)) / (3 + rr * (4 + rr)) < rr * 2 / (2 + rr) \<and> \<not> rr \<le> - 1"
              then have "\<not> rr < 0 \<and> \<not> (- 1 / 2 + (1 + rr) * (- 2 + (1 + rr) * (5 / 2))) / ((1 + rr) * (2 + (1 + rr))) < rr * 2 / (2 + rr) \<and> \<not> 1 + rr \<le> 0"
                by mt_arith_rule (* failed *)
              then have "\<not> rr < 0 \<and> \<not> ln (1 + rr) < rr * 2 / (2 + rr)"
                using ff8 by force (* 48 ms *) }
            ultimately have "\<not> 0 \<le> rr \<and> \<not> rr \<le> - 1 \<or> \<not> rr < 0 \<and> \<not> ln (1 + rr) < rr * 2 / (2 + rr)"
              by metis (* 12 ms *) }
          ultimately have "- 1 < rr \<longrightarrow> \<not> rr < 0 \<and> \<not> ln (1 + rr) < rr * 2 / (2 + rr) \<or> \<not> 0 \<le> rr \<and> \<not> rr \<le> - 1"
            by metis (* 12 ms *) }
        moreover
        { assume "\<not> - 3 < rr * (4 + rr)"
          then have "\<not> - 1 < rr \<or> \<not> 0 < rr * rr \<or> \<not> 0 \<le> rr"
            by sos (* 12 ms *) }
        ultimately have "0 \<le> rr \<and> 0 < rr * rr \<and> - 1 < rr \<longrightarrow> \<not> rr < 0 \<and> \<not> ln (1 + rr) < rr * 2 / (2 + rr) \<or> \<not> 0 \<le> rr \<and> \<not> rr \<le> - 1"
          by metis (* 20 ms *) }
      moreover
      { assume "\<not> rr * (rr * (rr * (- 1 / 2))) \<le> 0 \<and> \<not> rr \<le> - 2"
        then have "\<not> - 1 < rr \<or> \<not> 0 < rr * rr \<or> \<not> 0 \<le> rr"
          by sos (* 60 ms *) }
      ultimately have "0 \<le> rr \<and> 0 < rr * rr \<and> - 1 < rr \<longrightarrow> \<not> rr < 0 \<and> \<not> ln (1 + rr) < rr * 2 / (2 + rr) \<or> \<not> 0 \<le> rr \<and> \<not> rr \<le> - 1"
        by metis (* 16 ms *) }
    moreover
    { assume "\<not> - 2 < rr"
      then have "\<not> - 1 < rr \<or> \<not> 0 < rr * rr \<or> \<not> 0 \<le> rr"
        by sos (* 12 ms *) }
    ultimately have "0 \<le> rr \<and> 0 < rr * rr \<and> - 1 < rr \<longrightarrow> \<not> rr < 0 \<and> \<not> ln (1 + rr) < rr * 2 / (2 + rr) \<or> \<not> 0 \<le> rr \<and> \<not> rr \<le> - 1"
      by metis (* 12 ms *)
    moreover
    { assume "\<not> 0 < rr * rr"
      then have "\<not> 0 < rr * rr \<and> \<not> - 2 < rr \<or> \<not> 0 < rr * rr \<and> \<not> rr \<le> - 2"
        by auto (* 4 ms *)
      moreover
      { assume "\<not> 0 < rr * rr \<and> \<not> rr \<le> - 2"
        then have "\<not> rr * (2 + rr) < rr * (2 + rr * 2) \<and> \<not> 2 + rr \<le> 0"
          by mt_arith_rule (* failed *)
        then have "\<not> rr < rr * (2 + rr * 2) / (2 + rr)"
          using ff18 by auto (* 24 ms *)
        then have "- 1 < rr \<longrightarrow> \<not> rr < rr * (2 + rr * 2) / (2 + rr) \<and> \<not> rr \<le> - 1"
          by auto (* 4 ms *)
        moreover
        { assume "\<not> rr < rr * (2 + rr * 2) / (2 + rr) \<and> \<not> rr \<le> - 1"
          then have "\<not> rr < rr * 2 / (2 + rr) * (1 + rr) \<and> \<not> 1 + rr \<le> 0"
            by mt_arith_rule (* failed *)
          then have "\<not> rr / (1 + rr) < rr * 2 / (2 + rr)"
            using ff19 by force (* 12 ms *)
          then have "- 1 < rr \<longrightarrow> \<not> rr / (1 + rr) < rr * 2 / (2 + rr) \<and> \<not> rr \<le> - 1"
            by auto (* 8 ms *)
          moreover
          { assume "\<not> rr / (1 + rr) < rr * 2 / (2 + rr) \<and> \<not> rr \<le> - 1"
            then have "\<not> rr < 0 \<and> \<not> rr / (1 + rr) < rr * 2 / (2 + rr) \<and> \<not> rr \<le> - 1 \<or> \<not> 0 \<le> rr \<and> \<not> rr \<le> - 1"
              by simp (* 4 ms *)
            moreover
            { assume "\<not> rr < 0 \<and> \<not> rr / (1 + rr) < rr * 2 / (2 + rr) \<and> \<not> rr \<le> - 1"
              then have "\<not> rr < 0 \<and> \<not> (- 1 + (1 + rr)) / (1 + rr) < rr * 2 / (2 + rr) \<and> \<not> 1 + rr \<le> 0"
                by mt_arith_rule (* failed *)
              then have "\<not> rr < 0 \<and> \<not> ln (1 + rr) < rr * 2 / (2 + rr)"
                using ff21 by simp (* 12 ms *) }
            ultimately have "\<not> 0 \<le> rr \<and> \<not> rr \<le> - 1 \<or> \<not> rr < 0 \<and> \<not> ln (1 + rr) < rr * 2 / (2 + rr)"
              by metis (* 12 ms *) }
          ultimately have "- 1 < rr \<longrightarrow> \<not> rr < 0 \<and> \<not> ln (1 + rr) < rr * 2 / (2 + rr) \<or> \<not> 0 \<le> rr \<and> \<not> rr \<le> - 1"
            by metis (* 8 ms *) }
        ultimately have "- 1 < rr \<longrightarrow> \<not> rr < 0 \<and> \<not> ln (1 + rr) < rr * 2 / (2 + rr) \<or> \<not> 0 \<le> rr \<and> \<not> rr \<le> - 1"
          by metis (* 12 ms *) }
      moreover
      { assume "\<not> 0 < rr * rr \<and> \<not> - 2 < rr"
        then have "\<not> - 1 < rr \<or> \<not> 0 \<le> rr"
          by sos (* 8 ms *) }
      ultimately have "0 \<le> rr \<and> - 1 < rr \<longrightarrow> \<not> rr < 0 \<and> \<not> ln (1 + rr) < rr * 2 / (2 + rr) \<or> \<not> 0 \<le> rr \<and> \<not> rr \<le> - 1"
        by metis (* 40 ms *) }
    ultimately have "0 \<le> rr \<and> - 1 < rr \<longrightarrow> \<not> rr < 0 \<and> \<not> ln (1 + rr) < rr * 2 / (2 + rr) \<or> \<not> 0 \<le> rr \<and> \<not> rr \<le> - 1"
      by metis (* 20 ms *)
    moreover
    { assume "\<not> rr < 0 \<and> \<not> ln (1 + rr) < rr * 2 / (2 + rr)"
      then have "\<not> rr < 0 \<and> \<not> - 1 < rr \<or> \<not> rr < 0 \<and> \<not> ln (1 + rr) < rr * 2 / (2 + rr) \<and> \<not> rr \<le> - 1"
        by force (* 4 ms *)
      moreover
      { assume "\<not> rr < 0 \<and> \<not> ln (1 + rr) < rr * 2 / (2 + rr) \<and> \<not> rr \<le> - 1"
        then have "\<not> ln (1 + rr) < 0 \<and> \<not> rr < 0 \<and> \<not> ln (1 + rr) < rr * 2 / (2 + rr)"
          by mt_arith_rule (* failed *)
        then have "\<not> rr < 0 \<and> \<not> \<bar>ln (1 + rr)\<bar> < rr * 2 / (2 + rr)"
          using ff6 by simp (* 12 ms *)
        then have "\<not> \<bar>ln (1 + rr)\<bar> < \<bar>rr\<bar> * 2 / (2 + rr)"
          using ff4 by auto (* 104 ms *) }
      moreover
      { assume "\<not> rr < 0 \<and> \<not> - 1 < rr"
        then have "\<not> - 1 < rr"
          by sos (* 8 ms *) }
      ultimately have "\<not> - 1 < rr \<or> \<not> \<bar>ln (1 + rr)\<bar> < \<bar>rr\<bar> * 2 / (2 + rr)"
        by metis (* 16 ms *) }
    moreover
    { assume "\<not> 0 \<le> rr \<and> \<not> rr \<le> - 1"
      then have "\<not> - 1 < rr \<or> \<not> 0 \<le> rr"
        by sos (* 24 ms *) }
    ultimately have "\<not> - 1 < rr \<or> \<not> 0 \<le> rr \<or> \<not> \<bar>ln (1 + rr)\<bar> < \<bar>rr\<bar> * 2 / (2 + rr)"
      by metis (* 12 ms *)
    moreover
    { assume "\<not> 0 \<le> rr"
      then have "\<not> 0 \<le> rr \<and> \<not> rr \<le> - 2 \<or> \<not> - 2 < rr \<and> \<not> 0 \<le> rr"
        by auto (* 4 ms *)
      moreover
      { assume "\<not> 0 \<le> rr \<and> \<not> rr \<le> - 2"
        then have "\<not> 0 \<le> rr \<and> \<not> rr * (rr * (rr * (1 / 2))) \<le> 0 \<and> \<not> rr \<le> - 2 \<or> \<not> 0 < rr * (rr * (rr * (1 / 2))) \<and> \<not> 0 \<le> rr \<and> \<not> rr \<le> - 2"
          by simp (* 4 ms *)
        moreover
        { assume "\<not> 0 < rr * (rr * (rr * (1 / 2))) \<and> \<not> 0 \<le> rr \<and> \<not> rr \<le> - 2"
          then have "\<not> rr * (- 3 + rr * (- 1 / 2)) * (2 + rr) < rr * (- 6 + rr * - 4) \<and> \<not> 0 \<le> rr \<and> \<not> 2 + rr \<le> 0"
            by mt_arith_rule (* failed *)
          then have "\<not> rr * (- 3 + rr * (- 1 / 2)) < rr * (- 6 + rr * - 4) / (2 + rr) \<and> \<not> 0 \<le> rr"
            using ff9 by simp (* 56 ms *)
          then have "\<not> - 3 / 2 < rr \<and> \<not> 0 \<le> rr \<or> \<not> rr * (- 3 + rr * (- 1 / 2)) < rr * (- 6 + rr * - 4) / (2 + rr) \<and> \<not> 0 \<le> rr \<and> \<not> rr \<le> - 3 / 2"
            by auto (* 8 ms *)
          moreover
          { assume "\<not> rr * (- 3 + rr * (- 1 / 2)) < rr * (- 6 + rr * - 4) / (2 + rr) \<and> \<not> 0 \<le> rr \<and> \<not> rr \<le> - 3 / 2"
            then have "\<not> rr * 2 / (2 + rr) * (3 + rr * 2) < rr * (3 + rr * (1 / 2)) \<and> \<not> 0 \<le> rr \<and> \<not> 3 + rr * 2 \<le> 0"
              by mt_arith_rule (* failed *)
            then have "\<not> rr * 2 / (2 + rr) < rr * (3 + rr * (1 / 2)) / (3 + rr * 2) \<and> \<not> 0 \<le> rr"
              using ff10 by auto (* 16 ms *)
            then have "\<not> rr * 2 / (2 + rr) < rr * (3 + rr * (1 / 2)) / (3 + rr * 2) \<and> \<not> 0 \<le> rr \<and> \<not> rr \<le> - 1 \<or> \<not> - 1 < rr \<and> \<not> 0 \<le> rr"
              by auto (* 8 ms *)
            moreover
            { assume "\<not> rr * 2 / (2 + rr) < rr * (3 + rr * (1 / 2)) / (3 + rr * 2) \<and> \<not> 0 \<le> rr \<and> \<not> rr \<le> - 1"
              then have "\<not> rr * 2 / (2 + rr) < (- 5 / 2 + (1 + rr) * (2 + (1 + rr) * (1 / 2))) / (1 + (1 + rr) * 2) \<and> \<not> 0 \<le> rr \<and> \<not> 1 + rr \<le> 0"
                by mt_arith_rule (* failed *)
              then have "\<not> rr * 2 / (2 + rr) < ln (1 + rr) \<and> \<not> 0 \<le> rr"
                using ff17 by fastforce (* 32 ms *)
              then have "\<not> rr * 2 / (2 + rr) < ln (1 + rr) \<and> \<not> 0 \<le> rr \<and> \<not> rr \<le> - 2 \<or> \<not> - 2 < rr \<and> \<not> 0 \<le> rr"
                by auto (* 8 ms *)
              moreover
              { assume "\<not> rr * 2 / (2 + rr) < ln (1 + rr) \<and> \<not> 0 \<le> rr \<and> \<not> rr \<le> - 2"
                then have "\<not> rr * 2 < ln (1 + rr) * (2 + rr) \<and> \<not> 0 \<le> rr"
                  by mt_arith_rule (* failed *)
                then have "\<not> - 2 < rr \<and> \<not> 0 \<le> rr \<or> \<not> rr * 2 < ln (1 + rr) * (2 + rr) \<and> \<not> 0 \<le> rr \<and> \<not> rr \<le> - 2"
                  by auto (* 8 ms *)
                moreover
                { assume "\<not> rr * 2 < ln (1 + rr) * (2 + rr) \<and> \<not> 0 \<le> rr \<and> \<not> rr \<le> - 2"
                  then have "\<not> ln (1 + rr) * - 1 * (2 + rr) < rr * - 2 \<and> \<not> 0 \<le> rr \<and> \<not> 2 + rr \<le> 0"
                    by mt_arith_rule (* failed *)
                  then have "\<not> ln (1 + rr) * - 1 < rr * - 2 / (2 + rr) \<and> \<not> 0 \<le> rr"
                    using ff15 by simp (* 8 ms *)
                  then have "\<not> - 1 < rr \<and> \<not> 0 \<le> rr \<or> \<not> ln (1 + rr) * - 1 < rr * - 2 / (2 + rr) \<and> \<not> 0 \<le> rr \<and> \<not> rr \<le> - 1"
                    by auto (* 4 ms *)
                  moreover
                  { assume "\<not> ln (1 + rr) * - 1 < rr * - 2 / (2 + rr) \<and> \<not> 0 \<le> rr \<and> \<not> rr \<le> - 1"
                    then have "\<not> - ln (1 + rr) < rr * - 2 / (2 + rr) \<and> \<not> 0 \<le> ln (1 + rr) \<and> \<not> 0 \<le> rr"
                      by mt_arith_rule (* failed *)
                    then have "\<not> \<bar>ln (1 + rr)\<bar> < rr * - 2 / (2 + rr) \<and> \<not> 0 \<le> rr"
                      using ff14 by force (* 40 ms *)
                    then have "\<not> \<bar>ln (1 + rr)\<bar> < - rr * 2 / (2 + rr) \<and> \<not> 0 \<le> rr"
                      by mt_arith_rule (* failed *)
                    then have "\<not> \<bar>ln (1 + rr)\<bar> < \<bar>rr\<bar> * 2 / (2 + rr)"
                      using ff12 by auto (* 88 ms *) }
                  ultimately have "\<bar>ln (1 + rr)\<bar> < \<bar>rr\<bar> * 2 / (2 + rr) \<longrightarrow> \<not> - 1 < rr \<and> \<not> 0 \<le> rr"
                    by metis (* 20 ms *) }
                ultimately have "\<bar>ln (1 + rr)\<bar> < \<bar>rr\<bar> * 2 / (2 + rr) \<longrightarrow> \<not> - 1 < rr \<and> \<not> 0 \<le> rr \<or> \<not> - 2 < rr \<and> \<not> 0 \<le> rr"
                  by metis (* 52 ms *) }
              ultimately have "\<bar>ln (1 + rr)\<bar> < \<bar>rr\<bar> * 2 / (2 + rr) \<longrightarrow> \<not> - 1 < rr \<and> \<not> 0 \<le> rr \<or> \<not> - 2 < rr \<and> \<not> 0 \<le> rr"
                by metis (* 52 ms *) }
            ultimately have "\<bar>ln (1 + rr)\<bar> < \<bar>rr\<bar> * 2 / (2 + rr) \<longrightarrow> \<not> - 1 < rr \<and> \<not> 0 \<le> rr \<or> \<not> - 2 < rr \<and> \<not> 0 \<le> rr"
              by metis (* 24 ms *)
            moreover
            { assume "\<not> - 1 < rr \<and> \<not> 0 \<le> rr"
              then have "\<not> - 1 < rr"
                by sos (* 64 ms *) }
            ultimately have "\<bar>ln (1 + rr)\<bar> < \<bar>rr\<bar> * 2 / (2 + rr) \<and> - 1 < rr \<longrightarrow> \<not> - 2 < rr \<and> \<not> 0 \<le> rr"
              by metis (* 16 ms *) }
          moreover
          { assume "\<not> - 3 / 2 < rr \<and> \<not> 0 \<le> rr"
            then have "\<not> - 1 < rr"
              by sos (* 8 ms *) }
          ultimately have "\<bar>ln (1 + rr)\<bar> < \<bar>rr\<bar> * 2 / (2 + rr) \<and> - 1 < rr \<longrightarrow> \<not> - 2 < rr \<and> \<not> 0 \<le> rr"
            by metis (* 36 ms *) }
        moreover
        { assume "\<not> 0 \<le> rr \<and> \<not> rr * (rr * (rr * (1 / 2))) \<le> 0 \<and> \<not> rr \<le> - 2"
          then have "\<not> - 1 < rr"
            by sos (* 40 ms *) }
        ultimately have "\<bar>ln (1 + rr)\<bar> < \<bar>rr\<bar> * 2 / (2 + rr) \<and> - 1 < rr \<longrightarrow> \<not> - 2 < rr \<and> \<not> 0 \<le> rr"
          by metis (* 28 ms *) }
      ultimately have "\<bar>ln (1 + rr)\<bar> < \<bar>rr\<bar> * 2 / (2 + rr) \<and> - 1 < rr \<longrightarrow> \<not> - 2 < rr \<and> \<not> 0 \<le> rr"
        by metis (* 16 ms *)
      moreover
      { assume "\<not> - 2 < rr \<and> \<not> 0 \<le> rr"
        then have "\<not> - 1 < rr"
          by sos (* 24 ms *) }
      ultimately have "\<not> - 1 < rr \<or> \<not> \<bar>ln (1 + rr)\<bar> < \<bar>rr\<bar> * 2 / (2 + rr)"
        by metis (* 20 ms *) }
    ultimately have "\<not> - 1 < rr \<or> \<not> \<bar>ln (1 + rr)\<bar> < \<bar>rr\<bar> * 2 / (2 + rr)"
      by metis (* 16 ms *)
    moreover
    { assume "\<not> \<bar>ln (1 + rr)\<bar> < \<bar>rr\<bar> * 2 / (2 + rr)"
      then have "\<not> \<bar>ln (1 + rr)\<bar> < 2 * \<bar>rr\<bar> / (2 + rr)"
        by mt_arith_rule (* failed *)
      then have "\<not> \<bar>ln (1 + rr)\<bar> < 2 * \<bar>rr\<bar> / (2 + rr) \<or> \<not> - 1 < rr"
        by metis (* 4 ms *) }
    moreover
    { assume "\<not> - 1 < rr"
      then have "\<not> \<bar>ln (1 + rr)\<bar> < 2 * \<bar>rr\<bar> / (2 + rr) \<or> \<not> - 1 < rr"
        by metis (* 4 ms *) }
    ultimately have "\<not> \<bar>ln (1 + rr)\<bar> < 2 * \<bar>rr\<bar> / (2 + rr) \<or> \<not> - 1 < rr"
      by metis (* 16 ms *) }
  then have "\<forall>r. \<not> - (1::real) < r \<or> \<not> \<bar>ln (1 + r)\<bar> < 2 * \<bar>r\<bar> / (2 + r)"
    by blast (* 0.0 ms *)
  then show ?thesis
    by auto (* 24 ms *)
qed


end  