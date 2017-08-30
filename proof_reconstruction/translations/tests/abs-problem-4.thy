theory "abs-problem-4"
  imports "../GenerateATP"
begin

lemma "\<forall>(X::real).((Not((X <= -1)) --> (((2 * abs(X)) / (2 + X)) <= abs(ln((1 + X))))))" 
  apply(tactic {*fn st => (writeln (isar_proof st @{context}); Seq.single st) *})
proof -
  { fix rr :: real
    have "\<bar>ln (1 + rr)\<bar> < rr * 2 / (2 + rr) \<or> \<bar>rr\<bar> \<noteq> rr \<or> \<bar>rr\<bar> * 2 / (2 + rr) \<le> \<bar>ln (1 + rr)\<bar>"
      by auto (* 16 ms *)
    then have ff1: "rr < 0 \<or> \<bar>ln (1 + rr)\<bar> < rr * 2 / (2 + rr) \<or> \<bar>rr\<bar> * 2 / (2 + rr) \<le> \<bar>ln (1 + rr)\<bar>"
      using abs_nonnegative by blast (* 4 ms *)
    have "ln (1 + rr) < rr * 2 / (2 + rr) \<or> \<bar>ln (1 + rr)\<bar> \<noteq> ln (1 + rr) \<or> rr * 2 / (2 + rr) \<le> \<bar>ln (1 + rr)\<bar>"
      by auto (* 12 ms *)
    then have ff2: "ln (1 + rr) < 0 \<or> ln (1 + rr) < rr * 2 / (2 + rr) \<or> rr * 2 / (2 + rr) \<le> \<bar>ln (1 + rr)\<bar>"
      using abs_nonnegative by blast (* 0.0 ms *)
    have "\<not> lgen False X_000061 (1 / 2 * (1 + 5 * X_000060) * (X_000060 - 1) / (X_000060 * (2 + X_000060))) \<or> X_000060 \<le> 0 \<or> X_000061 \<le> ln X_000060"
      (*by (metis lgen_le_neg ln_lower_bound_cf3)*) sorry (* failed *)
    then have ff3: "(- 1 / 2 + X_000060 * (- 2 + X_000060 * (5 / 2))) / (X_000060 * (2 + X_000060)) < X_000061 \<or> X_000060 \<le> 0 \<or> X_000061 \<le> ln X_000060"
      by (simp add: field_simps) (* failed *)
    have "\<bar>ln (1 + rr)\<bar> < - rr * 2 / (2 + rr) \<or> \<bar>rr\<bar> \<noteq> - rr \<or> \<bar>rr\<bar> * 2 / (2 + rr) \<le> \<bar>ln (1 + rr)\<bar>"
      by auto (* 28 ms *)
    then have ff4: "\<bar>ln (1 + rr)\<bar> < - rr * 2 / (2 + rr) \<or> 0 \<le> rr \<or> \<bar>rr\<bar> * 2 / (2 + rr) \<le> \<bar>ln (1 + rr)\<bar>"
      using abs_negative by blast (* 4 ms *)
    have "- ln (1 + rr) < rr * - 2 / (2 + rr) \<or> \<bar>ln (1 + rr)\<bar> \<noteq> - ln (1 + rr) \<or> rr * - 2 / (2 + rr) \<le> \<bar>ln (1 + rr)\<bar>"
      by auto (* 12 ms *)
    then have ff5: "- ln (1 + rr) < rr * - 2 / (2 + rr) \<or> 0 \<le> ln (1 + rr) \<or> rr * - 2 / (2 + rr) \<le> \<bar>ln (1 + rr)\<bar>"
      using abs_negative by blast (* 0.0 ms *)
    have "\<not> lgen False (1 / 2 * (X_000053 + 5) * (X_000053 - 1) / (2 * X_000053 + 1)) X_000054 \<or> X_000053 \<le> 0 \<or> ln X_000053 \<le> X_000054"
      by (metis lgen_le_neg ln_upper_bound_cf3) (* failed *)
    then have ff6: "X_000054 < (- 5 / 2 + X_000053 * (2 + X_000053 * (1 / 2))) / (1 + X_000053 * 2) \<or> X_000053 \<le> 0 \<or> ln X_000053 \<le> X_000054"
      by (auto simp add: metitarski_simps algebra_simps divide_simps) (* failed *)
    have "\<not> lgen False X_000051 ((X_000050 - 1) / X_000050) \<or> X_000050 \<le> 0 \<or> X_000051 \<le> ln X_000050"
      using lgen_le_neg ln_lower_bound_cf1 by blast (* 8 ms *)
    then have ff7: "(- 1 + X_000050) / X_000050 < X_000051 \<or> X_000050 \<le> 0 \<or> X_000051 \<le> ln X_000050"
      using metitarski_simps algebra_simps by auto (* 112 ms *)
    have "\<not> - 2 < rr \<or> \<not> rr \<le> - 2"
      by auto (* 4 ms *)
    moreover
    { assume "\<not> rr \<le> - 2"
      then have "\<not> rr * (rr * (rr * (- 1 / 2))) \<le> 0 \<and> \<not> rr \<le> - 2 \<or> \<not> 0 < rr * (rr * (rr * (- 1 / 2))) \<and> \<not> rr \<le> - 2"
        by simp (* 8 ms *)
      moreover
      { assume "\<not> 0 < rr * (rr * (rr * (- 1 / 2))) \<and> \<not> rr \<le> - 2"
        then have "\<not> rr * (3 + rr * (5 / 2)) * (2 + rr) < rr * (6 + rr * (8 + rr * 2)) \<and> \<not> 2 + rr \<le> 0"
          by (simp add: metitarski_simps algebra_simps) (* 20 ms *)
        then have "\<not> rr * (3 + rr * (5 / 2)) < rr * (6 + rr * (8 + rr * 2)) / (2 + rr)"
          using leq_left_divide_mul_pos by fastforce (* 112 ms *)
        then have "- 3 < rr * (4 + rr) \<longrightarrow> \<not> rr * (3 + rr * (5 / 2)) < rr * (6 + rr * (8 + rr * 2)) / (2 + rr) \<and> \<not> rr * (4 + rr) \<le> - 3"
          by auto (* 8 ms *)
        moreover
        { assume "\<not> rr * (3 + rr * (5 / 2)) < rr * (6 + rr * (8 + rr * 2)) / (2 + rr) \<and> \<not> rr * (4 + rr) \<le> - 3"
          then have "\<not> rr * (3 + rr * (5 / 2)) < rr * 2 / (2 + rr) * (3 + rr * (4 + rr)) \<and> \<not> 3 + rr * (4 + rr) \<le> 0"
            by (auto simp add: field_simps) (* failed *)
          then have "\<not> rr * (3 + rr * (5 / 2)) / (3 + rr * (4 + rr)) < rr * 2 / (2 + rr)"
            using leq_right_divide_mul_pos by blast (* > 5.0 s, timed out *)
          then have "- 1 < rr \<longrightarrow> \<not> rr * (3 + rr * (5 / 2)) / (3 + rr * (4 + rr)) < rr * 2 / (2 + rr) \<and> \<not> rr \<le> - 1"
            by simp (* 4 ms *)
          moreover
          { assume "\<not> rr * (3 + rr * (5 / 2)) / (3 + rr * (4 + rr)) < rr * 2 / (2 + rr) \<and> \<not> rr \<le> - 1"
            then have "\<not> 0 \<le> rr \<and> \<not> rr \<le> - 1 \<or> \<not> rr < 0 \<and> \<not> rr * (3 + rr * (5 / 2)) / (3 + rr * (4 + rr)) < rr * 2 / (2 + rr) \<and> \<not> rr \<le> - 1"
              by auto (* 4 ms *)
            moreover
            { assume "\<not> rr < 0 \<and> \<not> rr * (3 + rr * (5 / 2)) / (3 + rr * (4 + rr)) < rr * 2 / (2 + rr) \<and> \<not> rr \<le> - 1"
              then have "\<not> rr < 0 \<and> \<not> (- 1 / 2 + (1 + rr) * (- 2 + (1 + rr) * (5 / 2))) / ((1 + rr) * (2 + (1 + rr))) < rr * 2 / (2 + rr) \<and> \<not> 1 + rr \<le> 0"
                by (simp add: field_simps) (* failed *)
              then have "\<not> rr < 0 \<and> \<not> ln (1 + rr) < rr * 2 / (2 + rr)"
                using ff3 by metis (* failed *) }
            ultimately have "\<not> 0 \<le> rr \<and> \<not> rr \<le> - 1 \<or> \<not> rr < 0 \<and> \<not> ln (1 + rr) < rr * 2 / (2 + rr)"
              by metis (* 12 ms *) }
          ultimately have "- 1 < rr \<longrightarrow> \<not> rr < 0 \<and> \<not> ln (1 + rr) < rr * 2 / (2 + rr) \<or> \<not> 0 \<le> rr \<and> \<not> rr \<le> - 1"
            by metis (* 16 ms *) }
        moreover
        { assume "\<not> - 3 < rr * (4 + rr)"
          then have "\<not> - 1 < rr \<or> \<not> 0 < rr * rr \<or> \<not> 0 \<le> rr"
            by sos (* 28 ms *) }
        ultimately have "0 \<le> rr \<and> 0 < rr * rr \<and> - 1 < rr \<longrightarrow> \<not> rr < 0 \<and> \<not> ln (1 + rr) < rr * 2 / (2 + rr) \<or> \<not> 0 \<le> rr \<and> \<not> rr \<le> - 1"
          by metis (* 32 ms *) }
      moreover
      { assume "\<not> rr * (rr * (rr * (- 1 / 2))) \<le> 0 \<and> \<not> rr \<le> - 2"
        then have "\<not> - 1 < rr \<or> \<not> 0 < rr * rr \<or> \<not> 0 \<le> rr"
          by sos (* 92 ms *) }
      ultimately have "0 \<le> rr \<and> 0 < rr * rr \<and> - 1 < rr \<longrightarrow> \<not> rr < 0 \<and> \<not> ln (1 + rr) < rr * 2 / (2 + rr) \<or> \<not> 0 \<le> rr \<and> \<not> rr \<le> - 1"
        by metis (* 20 ms *) }
    moreover
    { assume "\<not> - 2 < rr"
      then have "\<not> - 1 < rr \<or> \<not> 0 < rr * rr \<or> \<not> 0 \<le> rr"
        by sos (* 20 ms *) }
    ultimately have "0 \<le> rr \<and> 0 < rr * rr \<and> - 1 < rr \<longrightarrow> \<not> rr < 0 \<and> \<not> ln (1 + rr) < rr * 2 / (2 + rr) \<or> \<not> 0 \<le> rr \<and> \<not> rr \<le> - 1"
      by metis (* 12 ms *)
    moreover
    { assume "\<not> 0 < rr * rr"
      then have "\<not> 0 < rr * rr \<and> \<not> - 2 < rr \<or> \<not> 0 < rr * rr \<and> \<not> rr \<le> - 2"
        by auto (* 0.0 ms *)
      moreover
      { assume "\<not> 0 < rr * rr \<and> \<not> rr \<le> - 2"
        then have "\<not> rr * (2 + rr) < rr * (2 + rr * 2) \<and> \<not> 2 + rr \<le> 0"
          by (simp add: metitarski_simps algebra_simps) (* 0.0 ms *)
        then have "\<not> rr < rr * (2 + rr * 2) / (2 + rr)"
          using leq_left_divide_mul_pos by fastforce (* 80 ms *)
        then have "- 1 < rr \<longrightarrow> \<not> rr < rr * (2 + rr * 2) / (2 + rr) \<and> \<not> rr \<le> - 1"
          by auto (* 4 ms *)
        moreover
        { assume "\<not> rr < rr * (2 + rr * 2) / (2 + rr) \<and> \<not> rr \<le> - 1"
          then have "\<not> rr < rr * 2 / (2 + rr) * (1 + rr) \<and> \<not> 1 + rr \<le> 0"
            by (simp add: metitarski_simps algebra_simps) (* 16 ms *)
          then have "\<not> rr / (1 + rr) < rr * 2 / (2 + rr)"
            using leq_right_divide_mul_pos by fastforce (* 4.8 s *)
          then have "- 1 < rr \<longrightarrow> \<not> rr / (1 + rr) < rr * 2 / (2 + rr) \<and> \<not> rr \<le> - 1"
            by simp (* 0.0 ms *)
          moreover
          { assume "\<not> rr / (1 + rr) < rr * 2 / (2 + rr) \<and> \<not> rr \<le> - 1"
            then have "\<not> rr < 0 \<and> \<not> rr / (1 + rr) < rr * 2 / (2 + rr) \<and> \<not> rr \<le> - 1 \<or> \<not> 0 \<le> rr \<and> \<not> rr \<le> - 1"
              by auto (* 4 ms *)
            moreover
            { assume "\<not> rr < 0 \<and> \<not> rr / (1 + rr) < rr * 2 / (2 + rr) \<and> \<not> rr \<le> - 1"
              then have "\<not> rr < 0 \<and> \<not> (- 1 + (1 + rr)) / (1 + rr) < rr * 2 / (2 + rr) \<and> \<not> 1 + rr \<le> 0"
                by (simp add: metitarski_simps algebra_simps) (* 8 ms *)
              then have "\<not> rr < 0 \<and> \<not> ln (1 + rr) < rr * 2 / (2 + rr)"
                using ff7 by metis (* failed *) }
            ultimately have "\<not> 0 \<le> rr \<and> \<not> rr \<le> - 1 \<or> \<not> rr < 0 \<and> \<not> ln (1 + rr) < rr * 2 / (2 + rr)"
              by metis (* 12 ms *) }
          ultimately have "- 1 < rr \<longrightarrow> \<not> rr < 0 \<and> \<not> ln (1 + rr) < rr * 2 / (2 + rr) \<or> \<not> 0 \<le> rr \<and> \<not> rr \<le> - 1"
            by metis (* 12 ms *) }
        ultimately have "- 1 < rr \<longrightarrow> \<not> rr < 0 \<and> \<not> ln (1 + rr) < rr * 2 / (2 + rr) \<or> \<not> 0 \<le> rr \<and> \<not> rr \<le> - 1"
          by metis (* 16 ms *) }
      moreover
      { assume "\<not> 0 < rr * rr \<and> \<not> - 2 < rr"
        then have "\<not> - 1 < rr \<or> \<not> 0 \<le> rr"
          by sos (* 12 ms *) }
      ultimately have "0 \<le> rr \<and> - 1 < rr \<longrightarrow> \<not> rr < 0 \<and> \<not> ln (1 + rr) < rr * 2 / (2 + rr) \<or> \<not> 0 \<le> rr \<and> \<not> rr \<le> - 1"
        by metis (* 20 ms *) }
    ultimately have "0 \<le> rr \<and> - 1 < rr \<longrightarrow> \<not> rr < 0 \<and> \<not> ln (1 + rr) < rr * 2 / (2 + rr) \<or> \<not> 0 \<le> rr \<and> \<not> rr \<le> - 1"
      by metis (* 20 ms *)
    moreover
    { assume "\<not> rr < 0 \<and> \<not> ln (1 + rr) < rr * 2 / (2 + rr)"
      then have "\<not> rr < 0 \<and> \<not> - 1 < rr \<or> \<not> rr < 0 \<and> \<not> ln (1 + rr) < rr * 2 / (2 + rr) \<and> \<not> rr \<le> - 1"
        by auto (* 4 ms *)
      moreover
      { assume "\<not> rr < 0 \<and> \<not> ln (1 + rr) < rr * 2 / (2 + rr) \<and> \<not> rr \<le> - 1"
        then have "\<not> ln (1 + rr) < 0 \<and> \<not> rr < 0 \<and> \<not> ln (1 + rr) < rr * 2 / (2 + rr)"
          by (simp add: metitarski_simps algebra_simps) (* 4 ms *)
        then have "\<not> rr < 0 \<and> \<not> \<bar>ln (1 + rr)\<bar> < rr * 2 / (2 + rr)"
          using ff2 by auto (* 8 ms *)
        then have "\<not> \<bar>ln (1 + rr)\<bar> < \<bar>rr\<bar> * 2 / (2 + rr)"
          using ff1 by force (* 24 ms *) }
      moreover
      { assume "\<not> rr < 0 \<and> \<not> - 1 < rr"
        then have "\<not> - 1 < rr"
          by sos (* 8 ms *) }
      ultimately have "\<not> - 1 < rr \<or> \<not> \<bar>ln (1 + rr)\<bar> < \<bar>rr\<bar> * 2 / (2 + rr)"
        by metis (* 20 ms *) }
    moreover
    { assume "\<not> 0 \<le> rr \<and> \<not> rr \<le> - 1"
      then have "\<not> - 1 < rr \<or> \<not> 0 \<le> rr"
        by sos (* 32 ms *) }
    ultimately have "\<not> - 1 < rr \<or> \<not> 0 \<le> rr \<or> \<not> \<bar>ln (1 + rr)\<bar> < \<bar>rr\<bar> * 2 / (2 + rr)"
      by metis (* 24 ms *)
    moreover
    { assume "\<not> 0 \<le> rr"
      then have "\<not> 0 \<le> rr \<and> \<not> rr \<le> - 2 \<or> \<not> - 2 < rr \<and> \<not> 0 \<le> rr"
        by auto (* 4 ms *)
      moreover
      { assume "\<not> 0 \<le> rr \<and> \<not> rr \<le> - 2"
        then have "\<not> 0 \<le> rr \<and> \<not> rr * (rr * (rr * (1 / 2))) \<le> 0 \<and> \<not> rr \<le> - 2 \<or> \<not> 0 < rr * (rr * (rr * (1 / 2))) \<and> \<not> 0 \<le> rr \<and> \<not> rr \<le> - 2"
          by auto (* 24 ms *)
        moreover
        { assume "\<not> 0 < rr * (rr * (rr * (1 / 2))) \<and> \<not> 0 \<le> rr \<and> \<not> rr \<le> - 2"
          then have "\<not> rr * (- 3 + rr * (- 1 / 2)) * (2 + rr) < rr * (- 6 + rr * - 4) \<and> \<not> 0 \<le> rr \<and> \<not> 2 + rr \<le> 0"
            by (simp add: metitarski_simps algebra_simps) (* 100 ms *)
          then have "\<not> rr * (- 3 + rr * (- 1 / 2)) < rr * (- 6 + rr * - 4) / (2 + rr) \<and> \<not> 0 \<le> rr"
            using leq_left_divide_mul_pos sorry  by blast (* > 5.0 s, timed out *)
          then have "\<not> - 3 / 2 < rr \<and> \<not> 0 \<le> rr \<or> \<not> rr * (- 3 + rr * (- 1 / 2)) < rr * (- 6 + rr * - 4) / (2 + rr) \<and> \<not> 0 \<le> rr \<and> \<not> rr \<le> - 3 / 2"
            by simp (* 24 ms *)
          moreover
          { assume "\<not> rr * (- 3 + rr * (- 1 / 2)) < rr * (- 6 + rr * - 4) / (2 + rr) \<and> \<not> 0 \<le> rr \<and> \<not> rr \<le> - 3 / 2"
            then have "\<not> rr * 2 / (2 + rr) * (3 + rr * 2) < rr * (3 + rr * (1 / 2)) \<and> \<not> 0 \<le> rr \<and> \<not> 3 + rr * 2 \<le> 0"
              by (simp add: metitarski_simps algebra_simps divide_simps) (* failed *)
            then have "\<not> rr * 2 / (2 + rr) < rr * (3 + rr * (1 / 2)) / (3 + rr * 2) \<and> \<not> 0 \<le> rr"
              using leq_left_divide_mul_pos sorry  by blast (* > 5.0 s, timed out *)
            then have "\<not> rr * 2 / (2 + rr) < rr * (3 + rr * (1 / 2)) / (3 + rr * 2) \<and> \<not> 0 \<le> rr \<and> \<not> rr \<le> - 1 \<or> \<not> - 1 < rr \<and> \<not> 0 \<le> rr"
              by auto (* 12 ms *)
            moreover
            { assume "\<not> rr * 2 / (2 + rr) < rr * (3 + rr * (1 / 2)) / (3 + rr * 2) \<and> \<not> 0 \<le> rr \<and> \<not> rr \<le> - 1"
              then have "\<not> rr * 2 / (2 + rr) < (- 5 / 2 + (1 + rr) * (2 + (1 + rr) * (1 / 2))) / (1 + (1 + rr) * 2) \<and> \<not> 0 \<le> rr \<and> \<not> 1 + rr \<le> 0"
                by (simp add: metitarski_simps algebra_simps divide_simps) (* failed *)
              then have "\<not> rr * 2 / (2 + rr) < ln (1 + rr) \<and> \<not> 0 \<le> rr"
                using ff6 sorry (*by force*) (* > 5.0 s, timed out *)
              then have "\<not> rr * 2 / (2 + rr) < ln (1 + rr) \<and> \<not> 0 \<le> rr \<and> \<not> rr \<le> - 2 \<or> \<not> - 2 < rr \<and> \<not> 0 \<le> rr"
                by force (* 4 ms *)
              moreover
              { assume "\<not> rr * 2 / (2 + rr) < ln (1 + rr) \<and> \<not> 0 \<le> rr \<and> \<not> rr \<le> - 2"
                then have "\<not> rr * 2 < ln (1 + rr) * (2 + rr) \<and> \<not> 0 \<le> rr"
                  by (simp add: field_simps) (* failed *)
                then have "\<not> - 2 < rr \<and> \<not> 0 \<le> rr \<or> \<not> rr * 2 < ln (1 + rr) * (2 + rr) \<and> \<not> 0 \<le> rr \<and> \<not> rr \<le> - 2"
                  by auto (* 8 ms *)
                moreover
                { assume "\<not> rr * 2 < ln (1 + rr) * (2 + rr) \<and> \<not> 0 \<le> rr \<and> \<not> rr \<le> - 2"
                  then have "\<not> ln (1 + rr) * - 1 * (2 + rr) < rr * - 2 \<and> \<not> 0 \<le> rr \<and> \<not> 2 + rr \<le> 0"
                    by (simp add: metitarski_simps algebra_simps) (* 20 ms *)
                  then have "\<not> ln (1 + rr) * - 1 < rr * - 2 / (2 + rr) \<and> \<not> 0 \<le> rr"
                    using leq_left_divide_mul_pos sorry (*by blast*) (* > 5.0 s, timed out *)
                  then have "\<not> - 1 < rr \<and> \<not> 0 \<le> rr \<or> \<not> ln (1 + rr) * - 1 < rr * - 2 / (2 + rr) \<and> \<not> 0 \<le> rr \<and> \<not> rr \<le> - 1"
                    by auto (* 4 ms *)
                  moreover
                  { assume "\<not> ln (1 + rr) * - 1 < rr * - 2 / (2 + rr) \<and> \<not> 0 \<le> rr \<and> \<not> rr \<le> - 1"
                    then have "\<not> - ln (1 + rr) < rr * - 2 / (2 + rr) \<and> \<not> 0 \<le> ln (1 + rr) \<and> \<not> 0 \<le> rr"
                      by (simp add: metitarski_simps algebra_simps) (* 20 ms *)
                    then have "\<not> \<bar>ln (1 + rr)\<bar> < rr * - 2 / (2 + rr) \<and> \<not> 0 \<le> rr"
                      using ff5 by auto (* 40 ms *)
                    then have "\<not> \<bar>ln (1 + rr)\<bar> < - rr * 2 / (2 + rr) \<and> \<not> 0 \<le> rr"
                      by (simp add: metitarski_simps algebra_simps) (* 16 ms *)
                    then have "\<not> \<bar>ln (1 + rr)\<bar> < \<bar>rr\<bar> * 2 / (2 + rr)"
                      using ff4 by simp (* 72 ms *) }
                  ultimately have "\<bar>ln (1 + rr)\<bar> < \<bar>rr\<bar> * 2 / (2 + rr) \<longrightarrow> \<not> - 1 < rr \<and> \<not> 0 \<le> rr"
                    by metis (* 36 ms *) }
                ultimately have "\<bar>ln (1 + rr)\<bar> < \<bar>rr\<bar> * 2 / (2 + rr) \<longrightarrow> \<not> - 1 < rr \<and> \<not> 0 \<le> rr \<or> \<not> - 2 < rr \<and> \<not> 0 \<le> rr"
                  by metis (* 36 ms *) }
              ultimately have "\<bar>ln (1 + rr)\<bar> < \<bar>rr\<bar> * 2 / (2 + rr) \<longrightarrow> \<not> - 1 < rr \<and> \<not> 0 \<le> rr \<or> \<not> - 2 < rr \<and> \<not> 0 \<le> rr"
                by metis (* 40 ms *) }
            ultimately have "\<bar>ln (1 + rr)\<bar> < \<bar>rr\<bar> * 2 / (2 + rr) \<longrightarrow> \<not> - 1 < rr \<and> \<not> 0 \<le> rr \<or> \<not> - 2 < rr \<and> \<not> 0 \<le> rr"
              by metis (* 64 ms *)
            moreover
            { assume "\<not> - 1 < rr \<and> \<not> 0 \<le> rr"
              then have "\<not> - 1 < rr"
                by sos (* 92 ms *) }
            ultimately have "\<bar>ln (1 + rr)\<bar> < \<bar>rr\<bar> * 2 / (2 + rr) \<and> - 1 < rr \<longrightarrow> \<not> - 2 < rr \<and> \<not> 0 \<le> rr"
              by metis (* 28 ms *) }
          moreover
          { assume "\<not> - 3 / 2 < rr \<and> \<not> 0 \<le> rr"
            then have "\<not> - 1 < rr"
              by sos (* 12 ms *) }
          ultimately have "\<bar>ln (1 + rr)\<bar> < \<bar>rr\<bar> * 2 / (2 + rr) \<and> - 1 < rr \<longrightarrow> \<not> - 2 < rr \<and> \<not> 0 \<le> rr"
            by metis (* 72 ms *) }
        moreover
        { assume "\<not> 0 \<le> rr \<and> \<not> rr * (rr * (rr * (1 / 2))) \<le> 0 \<and> \<not> rr \<le> - 2"
          then have "\<not> - 1 < rr"
            by sos (* 48 ms *) }
        ultimately have "\<bar>ln (1 + rr)\<bar> < \<bar>rr\<bar> * 2 / (2 + rr) \<and> - 1 < rr \<longrightarrow> \<not> - 2 < rr \<and> \<not> 0 \<le> rr"
          by metis (* 72 ms *) }
      ultimately have "\<bar>ln (1 + rr)\<bar> < \<bar>rr\<bar> * 2 / (2 + rr) \<and> - 1 < rr \<longrightarrow> \<not> - 2 < rr \<and> \<not> 0 \<le> rr"
        by metis (* 44 ms *)
      moreover
      { assume "\<not> - 2 < rr \<and> \<not> 0 \<le> rr"
        then have "\<not> - 1 < rr"
          by sos (* 56 ms *) }
      ultimately have "\<not> - 1 < rr \<or> \<not> \<bar>ln (1 + rr)\<bar> < \<bar>rr\<bar> * 2 / (2 + rr)"
        by metis (* 28 ms *) }
    ultimately have "\<not> - 1 < rr \<or> \<not> \<bar>ln (1 + rr)\<bar> < \<bar>rr\<bar> * 2 / (2 + rr)"
      by metis (* 24 ms *)
    moreover
    { assume "\<not> \<bar>ln (1 + rr)\<bar> < \<bar>rr\<bar> * 2 / (2 + rr)"
      then have "\<not> \<bar>ln (1 + rr)\<bar> < 2 * \<bar>rr\<bar> / (2 + rr)"
        by (simp add: metitarski_simps algebra_simps) (* 32 ms *)
      then have "\<not> \<bar>ln (1 + rr)\<bar> < 2 * \<bar>rr\<bar> / (2 + rr) \<or> \<not> - 1 < rr"
        by metis (* 8 ms *) }
    moreover
    { assume "\<not> - 1 < rr"
      then have "\<not> \<bar>ln (1 + rr)\<bar> < 2 * \<bar>rr\<bar> / (2 + rr) \<or> \<not> - 1 < rr"
        by metis (* 8 ms *) }
    ultimately have "\<not> \<bar>ln (1 + rr)\<bar> < 2 * \<bar>rr\<bar> / (2 + rr) \<or> \<not> - 1 < rr"
      by metis (* 16 ms *) }
  then have "\<forall>r. \<not> - (1::real) < r \<or> \<not> \<bar>ln (1 + r)\<bar> < 2 * \<bar>r\<bar> / (2 + r)"
    by blast (* 0.0 ms *)
  then show "\<forall>r>- (1::real). 2 * \<bar>r\<bar> / (2 + r) \<le> \<bar>ln (1 + r)\<bar>"
    by auto (* 44 ms *)
qed
  
end  