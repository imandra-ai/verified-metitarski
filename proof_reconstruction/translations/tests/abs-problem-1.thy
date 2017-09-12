theory "abs-problem-1"
  imports "../GenerateATP"
begin
  
lemma "abs-problem-1": "\<forall>(X::real).(0\<le>X \<longrightarrow> abs(ln(1+X)-X) \<le> X^2)"
  apply(tactic {*fn st => (writeln (isar_proof st [] @{context}); Seq.single st) *})
proof -
  { fix rr :: real
    have ff1: "rr < rr * (1 + rr * - 1) * (1 + rr) \<or> rr * (1 + rr * - 1) \<le> rr / (1 + rr) \<or> 1 + rr \<le> 0"
      using leq_right_divide_mul_pos by blast (* 12 ms *)
    have ff2: "rr * - 1 + ln (1 + rr) < 0 \<or> \<bar>rr * - 1 + ln (1 + rr)\<bar> = rr * - 1 + ln (1 + rr)"
      using abs_nonnegative by blast (* 4 ms *)
    have "rr * rr < rr * - 1 + ln (1 + rr) \<or> \<bar>rr * - 1 + ln (1 + rr)\<bar> \<noteq> rr * - 1 + ln (1 + rr) \<or> \<bar>rr * - 1 + ln (1 + rr)\<bar> \<le> rr * rr"
      by auto (* 52 ms *)
    then have ff3: "rr * - 1 + ln (1 + rr) < 0 \<or> rr * rr < rr * - 1 + ln (1 + rr) \<or> \<bar>rr * - 1 + ln (1 + rr)\<bar> \<le> rr * rr"
      using ff2 by blast (* 0.0 ms *)
    have ff4: "\<And>r ra. \<not> lgen False (ln ra) r \<or> ln ra \<le> r"
      using lgen_le_neg by blast (* 4 ms *)
    have "\<And>r ra. \<not> lgen False (ra - 1) r \<or> ra \<le> 0 \<or> lgen False (ln ra) r"
      using ln_upper_bound_cf1 by blast (* 8 ms *)
    then have "\<And>r ra. \<not> lgen False (ra - 1) r \<or> ra \<le> 0 \<or> ln ra \<le> r"
      using ff4 by blast (* 8 ms *)
    then have "\<And>r ra. (ra::real) < - 1 + r \<or> r \<le> 0 \<or> ln r \<le> ra"
      sorry (* failed *)
    then have ff5: "rr * (1 + rr) < - 1 + (1 + rr) \<or> 1 + rr \<le> 0 \<or> ln (1 + rr) \<le> rr * (1 + rr)"
      by blast (* 4 ms *)
    have ff6: "0 \<le> rr * - 1 + ln (1 + rr) \<or> \<bar>rr * - 1 + ln (1 + rr)\<bar> = - (rr * - 1 + ln (1 + rr))"
      using abs_negative by blast (* 0.0 ms *)
    have "rr * rr < - (rr * - 1 + ln (1 + rr)) \<or> \<bar>rr * - 1 + ln (1 + rr)\<bar> \<noteq> - (rr * - 1 + ln (1 + rr)) \<or> \<bar>rr * - 1 + ln (1 + rr)\<bar> \<le> rr * rr"
      by auto (* 24 ms *)
    then have ff7: "rr * rr < - (rr * - 1 + ln (1 + rr)) \<or> 0 \<le> rr * - 1 + ln (1 + rr) \<or> \<bar>rr * - 1 + ln (1 + rr)\<bar> \<le> rr * rr"
      using ff6 by force (* 0.0 ms *)
    have ff8: "\<And>r ra. \<not> lgen False ra (ln r) \<or> ra \<le> ln r"
      using lgen_le_neg by blast (* 0.0 ms *)
    have "\<And>r ra. \<not> lgen False ra ((r - 1) / r) \<or> r \<le> 0 \<or> lgen False ra (ln r)"
      using ln_lower_bound_cf1 by blast (* 8 ms *)
    then have "\<And>r ra. \<not> lgen False ra ((r - 1) / r) \<or> r \<le> 0 \<or> ra \<le> ln r"
      using ff8 by blast (* 8 ms *)
    then have ff9: "\<And>r ra. (- (1::real) + ra) / ra < r \<or> ra \<le> 0 \<or> r \<le> ln ra"
      sorry (* failed *)
    then have ff10: "(- 1 + (1 + rr)) / (1 + rr) < rr * (1 + rr * - 1) \<or> rr * (1 + rr * - 1) \<le> ln (1 + rr) \<or> 1 + rr \<le> 0"
      by blast (* 4 ms *)
    have ff11: "rr < rr * (1 + rr) \<or> 1 + rr \<le> 0 \<or> rr \<le> rr / (1 + rr)"
      using leq_right_divide_mul_pos by blast (* 12 ms *)
    have ff12: "(- 1 + (1 + rr)) / (1 + rr) < rr \<or> 1 + rr \<le> 0 \<or> rr \<le> ln (1 + rr)"
      using ff9 by blast (* 8 ms *)
    have "\<not> rr \<le> - 1 \<or> \<not> - 1 < rr"
      by simp (* 8 ms *)
    moreover
    { assume "\<not> rr \<le> - 1"
      then have "\<not> rr * (rr * (rr * - 1)) \<le> 0 \<and> \<not> rr \<le> - 1 \<or> \<not> 0 < rr * (rr * (rr * - 1)) \<and> \<not> rr \<le> - 1"
        by force (* 32 ms *)
      moreover
      { assume "\<not> 0 < rr * (rr * (rr * - 1)) \<and> \<not> rr \<le> - 1"
        then have "\<not> rr < rr * (1 + rr * - 1) * (1 + rr) \<and> \<not> 1 + rr \<le> 0"
          sorry (* failed *)
        then have "\<not> rr / (1 + rr) < rr * (1 + rr * - 1)"
          using ff1 by auto (* 96 ms *)
        then have "ln (1 + rr) < rr \<longrightarrow> \<not> rr / (1 + rr) < rr * (1 + rr * - 1) \<and> \<not> rr \<le> ln (1 + rr)"
          by simp (* 16 ms *)
        moreover
        { assume "\<not> rr / (1 + rr) < rr * (1 + rr * - 1) \<and> \<not> rr \<le> ln (1 + rr)"
          then have "- 1 < rr \<longrightarrow> \<not> rr / (1 + rr) < rr * (1 + rr * - 1) \<and> \<not> rr \<le> - 1 \<and> \<not> rr \<le> ln (1 + rr)"
            by force (* 32 ms *)
          moreover
          { assume "\<not> rr / (1 + rr) < rr * (1 + rr * - 1) \<and> \<not> rr \<le> - 1 \<and> \<not> rr \<le> ln (1 + rr)"
            then have "\<not> (- 1 + (1 + rr)) / (1 + rr) < rr * (1 + rr * - 1) \<and> \<not> 1 + rr \<le> 0 \<and> \<not> rr \<le> ln (1 + rr)"
              sorry (* failed *)
            then have "\<not> ln (1 + rr) < rr * (1 + rr * - 1) \<and> \<not> rr \<le> ln (1 + rr)"
              using ff10 by simp (* 64 ms *)
            then have "\<not> rr * rr < - (rr * - 1 + ln (1 + rr)) \<and> \<not> 0 \<le> rr * - 1 + ln (1 + rr)"
              sorry (* failed *)
            then have "\<not> rr * rr < \<bar>rr * - 1 + ln (1 + rr)\<bar>"
              using ff7 by simp (* 72 ms *) }
          ultimately have "\<not> - 1 < rr \<or> \<not> rr * rr < \<bar>rr * - 1 + ln (1 + rr)\<bar>"
            by metis (* 40 ms *) }
        ultimately have "\<not> ln (1 + rr) < rr \<or> \<not> - 1 < rr \<or> \<not> rr * rr < \<bar>rr * - 1 + ln (1 + rr)\<bar>"
          by metis (* 20 ms *) }
      moreover
      { assume "\<not> rr * (rr * (rr * - 1)) \<le> 0 \<and> \<not> rr \<le> - 1"
        then have "\<not> 0 \<le> rr \<or> \<not> 0 < rr * rr"
          by sos (* 364 ms *)
        moreover
        { assume "\<not> 0 < rr * rr"
          then have "\<not> 0 < rr * rr \<and> \<not> - 1 < rr \<or> \<not> 0 < rr * rr \<and> \<not> rr \<le> - 1"
            by auto (* 8 ms *)
          moreover
          { assume "\<not> 0 < rr * rr \<and> \<not> rr \<le> - 1"
            then have "\<not> rr < rr * (1 + rr) \<and> \<not> 1 + rr \<le> 0"
              sorry (* failed *)
            then have "\<not> rr / (1 + rr) < rr"
              using ff11 by simp (* 24 ms *)
            then have "- 1 < rr \<longrightarrow> \<not> rr / (1 + rr) < rr \<and> \<not> rr \<le> - 1"
              by auto (* 16 ms *)
            moreover
            { assume "\<not> rr / (1 + rr) < rr \<and> \<not> rr \<le> - 1"
              then have "\<not> (- 1 + (1 + rr)) / (1 + rr) < rr \<and> \<not> 1 + rr \<le> 0"
                sorry (* failed *)
              then have "\<not> ln (1 + rr) < rr"
                using ff12 by force (* 32 ms *) }
            ultimately have "\<not> ln (1 + rr) < rr \<or> \<not> - 1 < rr"
              by metis (* 36 ms *) }
          moreover
          { assume "\<not> 0 < rr * rr \<and> \<not> - 1 < rr"
            then have "\<not> 0 \<le> rr"
              by sos (* 140 ms *) }
          ultimately have "\<not> 0 \<le> rr \<or> \<not> ln (1 + rr) < rr \<or> \<not> - 1 < rr"
            by metis (* 28 ms *) }
        ultimately have "\<not> 0 \<le> rr \<or> \<not> ln (1 + rr) < rr \<or> \<not> - 1 < rr"
          by metis (* 12 ms *) }
      ultimately have "\<not> 0 \<le> rr \<or> \<not> ln (1 + rr) < rr \<or> \<not> - 1 < rr \<or> \<not> rr * rr < \<bar>rr * - 1 + ln (1 + rr)\<bar>"
        by metis (* 32 ms *)
      moreover
      { assume "\<not> ln (1 + rr) < rr"
        then have "- 1 < rr \<longrightarrow> \<not> ln (1 + rr) < rr \<and> \<not> rr \<le> - 1"
          by auto (* 8 ms *)
        moreover
        { assume "\<not> ln (1 + rr) < rr \<and> \<not> rr \<le> - 1"
          then have "\<not> rr * (rr * - 1) \<le> 0 \<and> \<not> rr \<le> - 1 \<or> \<not> 0 < rr * (rr * - 1) \<and> \<not> ln (1 + rr) < rr \<and> \<not> rr \<le> - 1"
            by fastforce (* 52 ms *)
          moreover
          { assume "\<not> 0 < rr * (rr * - 1) \<and> \<not> ln (1 + rr) < rr \<and> \<not> rr \<le> - 1"
            then have "\<not> rr * (1 + rr) < - 1 + (1 + rr) \<and> \<not> ln (1 + rr) < rr \<and> \<not> 1 + rr \<le> 0"
              sorry (* failed *)
            then have "\<not> rr * (1 + rr) < ln (1 + rr) \<and> \<not> ln (1 + rr) < rr"
              using ff5 by auto (* 180 ms *)
            then have "\<not> rr * - 1 + ln (1 + rr) < 0 \<and> \<not> rr * rr < rr * - 1 + ln (1 + rr)"
              sorry (* failed *)
            then have "\<not> rr * rr < \<bar>rr * - 1 + ln (1 + rr)\<bar>"
              using ff3 by simp (* 168 ms *) }
          moreover
          { assume "\<not> rr * (rr * - 1) \<le> 0 \<and> \<not> rr \<le> - 1"
            then have "\<not> 0 \<le> rr"
              by sos (* 292 ms *) }
          ultimately have "\<not> 0 \<le> rr \<or> \<not> rr * rr < \<bar>rr * - 1 + ln (1 + rr)\<bar>"
            by metis (* 36 ms *) }
        ultimately have "\<not> 0 \<le> rr \<or> \<not> - 1 < rr \<or> \<not> rr * rr < \<bar>rr * - 1 + ln (1 + rr)\<bar>"
          by metis (* 36 ms *) }
      ultimately have "\<not> 0 \<le> rr \<or> \<not> - 1 < rr \<or> \<not> rr * rr < \<bar>rr * - 1 + ln (1 + rr)\<bar>"
        by metis (* 72 ms *)
      moreover
      { assume "\<not> rr * rr < \<bar>rr * - 1 + ln (1 + rr)\<bar>"
        then have "\<not> rr\<^sup>2 < \<bar>ln (1 + rr) - rr\<bar>"
          sorry (* failed *)
        then have "\<not> rr\<^sup>2 < \<bar>ln (1 + rr) - rr\<bar> \<or> \<not> 0 \<le> rr"
          by metis (* 12 ms *) }
      ultimately have "- 1 < rr \<and> 0 \<le> rr \<longrightarrow> \<not> rr\<^sup>2 < \<bar>ln (1 + rr) - rr\<bar> \<or> \<not> 0 \<le> rr"
        by metis (* 28 ms *) }
    ultimately have "- 1 < rr \<and> 0 \<le> rr \<longrightarrow> \<not> rr\<^sup>2 < \<bar>ln (1 + rr) - rr\<bar> \<or> \<not> 0 \<le> rr"
      by metis (* 48 ms *)
    moreover
    { assume "\<not> - 1 < rr"
      then have "\<not> 0 \<le> rr"
        by sos (* 124 ms *) }
    ultimately have "0 \<le> rr \<longrightarrow> \<not> rr\<^sup>2 < \<bar>ln (1 + rr) - rr\<bar> \<or> \<not> 0 \<le> rr"
      by metis (* 20 ms *)
    moreover
    { assume "\<not> 0 \<le> rr"
      then have "\<not> rr\<^sup>2 < \<bar>ln (1 + rr) - rr\<bar> \<or> \<not> 0 \<le> rr"
        by metis (* 8 ms *) }
    ultimately have "\<not> rr\<^sup>2 < \<bar>ln (1 + rr) - rr\<bar> \<or> \<not> 0 \<le> rr"
      by metis (* 16 ms *) }
  then have "\<forall>r. \<not> (r::real)\<^sup>2 < \<bar>ln (1 + r) - r\<bar> \<or> \<not> 0 \<le> r"
    by blast (* 4 ms *)
  then show ?thesis
    by auto (* 2.9 s *)
qed
(*proof -
  { fix rr :: real
    have ff1: "rr < rr * (1 + rr * - 1) * (1 + rr) \<or> rr * (1 + rr * - 1) \<le> rr / (1 + rr) \<or> 1 + rr \<le> 0"
      using leq_right_divide_mul_pos by auto (* 4 ms *)
    have ff2: "rr * - 1 + ln (1 + rr) < 0 \<or> \<bar>rr * - 1 + ln (1 + rr)\<bar> = rr * - 1 + ln (1 + rr)"
      using abs_nonnegative by blast (* 0.0 ms *)
    have "rr * rr < rr * - 1 + ln (1 + rr) \<or> \<bar>rr * - 1 + ln (1 + rr)\<bar> \<noteq> rr * - 1 + ln (1 + rr) \<or> \<bar>rr * - 1 + ln (1 + rr)\<bar> \<le> rr * rr"
      by auto (* 12 ms *)
    then have ff3: "rr * - 1 + ln (1 + rr) < 0 \<or> rr * rr < rr * - 1 + ln (1 + rr) \<or> \<bar>rr * - 1 + ln (1 + rr)\<bar> \<le> rr * rr"
      using ff2 by fastforce (* 0.0 ms *)
    have ff4: "\<And>r ra. \<not> lgen False (ln ra) r \<or> ln ra \<le> r"
      using lgen_le_neg by auto (* 0.0 ms *)
    have "\<And>r ra. \<not> lgen False (ra - 1) r \<or> ra \<le> 0 \<or> lgen False (ln ra) r"
      using ln_upper_bound_cf1 by blast (* 4 ms *)
    then have "\<And>r ra. \<not> lgen False (ra - 1) r \<or> ra \<le> 0 \<or> ln ra \<le> r"
      using ff4 by blast (* 0.0 ms *)
    then have "\<And>r ra. (ra::real) < - 1 + r \<or> r \<le> 0 \<or> ln r \<le> ra"
      using metitarski_simps algebra_simps by auto (* 24 ms *)
    then have ff5: "rr * (1 + rr) < - 1 + (1 + rr) \<or> 1 + rr \<le> 0 \<or> ln (1 + rr) \<le> rr * (1 + rr)"
      by blast (* 0.0 ms *)
    have ff6: "0 \<le> rr * - 1 + ln (1 + rr) \<or> \<bar>rr * - 1 + ln (1 + rr)\<bar> = - (rr * - 1 + ln (1 + rr))"
      using abs_negative by blast (* 0.0 ms *)
    have "rr * rr < - (rr * - 1 + ln (1 + rr)) \<or> \<bar>rr * - 1 + ln (1 + rr)\<bar> \<noteq> - (rr * - 1 + ln (1 + rr)) \<or> \<bar>rr * - 1 + ln (1 + rr)\<bar> \<le> rr * rr"
      by auto (* 12 ms *)
    then have ff7: "rr * rr < - (rr * - 1 + ln (1 + rr)) \<or> 0 \<le> rr * - 1 + ln (1 + rr) \<or> \<bar>rr * - 1 + ln (1 + rr)\<bar> \<le> rr * rr"
      using ff6 by fastforce (* 0.0 ms *)
    have ff8: "\<And>r ra. \<not> lgen False ra (ln r) \<or> ra \<le> ln r"
      using lgen_le_neg by blast (* 0.0 ms *)
    have "\<And>r ra. \<not> lgen False ra ((r - 1) / r) \<or> r \<le> 0 \<or> lgen False ra (ln r)"
      using ln_lower_bound_cf1 by blast (* 0.0 ms *)
    then have "\<And>r ra. \<not> lgen False ra ((r - 1) / r) \<or> r \<le> 0 \<or> ra \<le> ln r"
      using ff8 by blast (* 4 ms *)
    then have ff9: "\<And>r ra. (- (1::real) + ra) / ra < r \<or> ra \<le> 0 \<or> r \<le> ln ra"
      using metitarski_simps algebra_simps by auto (* 44 ms *)
    then have ff10: "(- 1 + (1 + rr)) / (1 + rr) < rr * (1 + rr * - 1) \<or> rr * (1 + rr * - 1) \<le> ln (1 + rr) \<or> 1 + rr \<le> 0"
      by blast (* 4 ms *)
    have ff11: "rr < rr * (1 + rr) \<or> 1 + rr \<le> 0 \<or> rr \<le> rr / (1 + rr)"
      using leq_right_divide_mul_pos by auto (* 4 ms *)
    have ff12: "(- 1 + (1 + rr)) / (1 + rr) < rr \<or> 1 + rr \<le> 0 \<or> rr \<le> ln (1 + rr)"
      using ff9 by blast (* 4 ms *)
    have "\<not> rr \<le> - 1 \<or> \<not> - 1 < rr"
      by force (* 0.0 ms *)
    moreover
    { assume "\<not> rr \<le> - 1"
      then have "\<not> rr * (rr * (rr * - 1)) \<le> 0 \<and> \<not> rr \<le> - 1 \<or> \<not> 0 < rr * (rr * (rr * - 1)) \<and> \<not> rr \<le> - 1"
        by fastforce (* 4 ms *)
      moreover
      { assume "\<not> 0 < rr * (rr * (rr * - 1)) \<and> \<not> rr \<le> - 1"
        then have "\<not> rr < rr * (1 + rr * - 1) * (1 + rr) \<and> \<not> 1 + rr \<le> 0"
          by (simp add: metitarski_simps algebra_simps) (* 8 ms *)
        then have "\<not> rr / (1 + rr) < rr * (1 + rr * - 1)"
          using ff1 by auto (* 8 ms *)
        then have "ln (1 + rr) < rr \<longrightarrow> \<not> rr / (1 + rr) < rr * (1 + rr * - 1) \<and> \<not> rr \<le> ln (1 + rr)"
          by auto (* 0.0 ms *)
        moreover
        { assume "\<not> rr / (1 + rr) < rr * (1 + rr * - 1) \<and> \<not> rr \<le> ln (1 + rr)"
          then have "- 1 < rr \<longrightarrow> \<not> rr / (1 + rr) < rr * (1 + rr * - 1) \<and> \<not> rr \<le> - 1 \<and> \<not> rr \<le> ln (1 + rr)"
            by auto (* 0.0 ms *)
          moreover
          { assume "\<not> rr / (1 + rr) < rr * (1 + rr * - 1) \<and> \<not> rr \<le> - 1 \<and> \<not> rr \<le> ln (1 + rr)"
            then have "\<not> (- 1 + (1 + rr)) / (1 + rr) < rr * (1 + rr * - 1) \<and> \<not> 1 + rr \<le> 0 \<and> \<not> rr \<le> ln (1 + rr)"
              by (simp add: metitarski_simps algebra_simps) (* 4 ms *)
            then have "\<not> ln (1 + rr) < rr * (1 + rr * - 1) \<and> \<not> rr \<le> ln (1 + rr)"
              using ff10 by auto (* 8 ms *)
            then have "\<not> rr * rr < - (rr * - 1 + ln (1 + rr)) \<and> \<not> 0 \<le> rr * - 1 + ln (1 + rr)"
              by (simp add: metitarski_simps algebra_simps) (* 4 ms *)
            then have "\<not> rr * rr < \<bar>rr * - 1 + ln (1 + rr)\<bar>"
              using ff7 by auto (* 20 ms *) }
          ultimately have "\<not> - 1 < rr \<or> \<not> rr * rr < \<bar>rr * - 1 + ln (1 + rr)\<bar>"
            by metis (* 16 ms *) }
        ultimately have "\<not> ln (1 + rr) < rr \<or> \<not> - 1 < rr \<or> \<not> rr * rr < \<bar>rr * - 1 + ln (1 + rr)\<bar>"
          by metis (* 16 ms *) }
      moreover
      { assume "\<not> rr * (rr * (rr * - 1)) \<le> 0 \<and> \<not> rr \<le> - 1"
        then have "\<not> 0 \<le> rr \<or> \<not> 0 < rr * rr"
          by sos (* 32 ms *)
        moreover
        { assume "\<not> 0 < rr * rr"
          then have "\<not> 0 < rr * rr \<and> \<not> - 1 < rr \<or> \<not> 0 < rr * rr \<and> \<not> rr \<le> - 1"
            by auto (* 0.0 ms *)
          moreover
          { assume "\<not> 0 < rr * rr \<and> \<not> rr \<le> - 1"
            then have "\<not> rr < rr * (1 + rr) \<and> \<not> 1 + rr \<le> 0"
              by (simp add: metitarski_simps algebra_simps) (* 4 ms *)
            then have "\<not> rr / (1 + rr) < rr"
              using ff11 by simp (* 4 ms *)
            then have "- 1 < rr \<longrightarrow> \<not> rr / (1 + rr) < rr \<and> \<not> rr \<le> - 1"
              by simp (* 0.0 ms *)
            moreover
            { assume "\<not> rr / (1 + rr) < rr \<and> \<not> rr \<le> - 1"
              then have "\<not> (- 1 + (1 + rr)) / (1 + rr) < rr \<and> \<not> 1 + rr \<le> 0"
                by (simp add: metitarski_simps algebra_simps) (* 8 ms *)
              then have "\<not> ln (1 + rr) < rr"
                using ff12 by auto (* 4 ms *) }
            ultimately have "\<not> ln (1 + rr) < rr \<or> \<not> - 1 < rr"
              by metis (* 4 ms *) }
          moreover
          { assume "\<not> 0 < rr * rr \<and> \<not> - 1 < rr"
            then have "\<not> 0 \<le> rr"
              by sos (* 12 ms *) }
          ultimately have "\<not> 0 \<le> rr \<or> \<not> ln (1 + rr) < rr \<or> \<not> - 1 < rr"
            by metis (* 8 ms *) }
        ultimately have "\<not> 0 \<le> rr \<or> \<not> ln (1 + rr) < rr \<or> \<not> - 1 < rr"
          by metis (* 4 ms *) }
      ultimately have "\<not> 0 \<le> rr \<or> \<not> ln (1 + rr) < rr \<or> \<not> - 1 < rr \<or> \<not> rr * rr < \<bar>rr * - 1 + ln (1 + rr)\<bar>"
        by metis (* 20 ms *)
      moreover
      { assume "\<not> ln (1 + rr) < rr"
        then have "- 1 < rr \<longrightarrow> \<not> ln (1 + rr) < rr \<and> \<not> rr \<le> - 1"
          by auto (* 0.0 ms *)
        moreover
        { assume "\<not> ln (1 + rr) < rr \<and> \<not> rr \<le> - 1"
          then have "\<not> rr * (rr * - 1) \<le> 0 \<and> \<not> rr \<le> - 1 \<or> \<not> 0 < rr * (rr * - 1) \<and> \<not> ln (1 + rr) < rr \<and> \<not> rr \<le> - 1"
            by simp (* 0.0 ms *)
          moreover
          { assume "\<not> 0 < rr * (rr * - 1) \<and> \<not> ln (1 + rr) < rr \<and> \<not> rr \<le> - 1"
            then have "\<not> rr * (1 + rr) < - 1 + (1 + rr) \<and> \<not> ln (1 + rr) < rr \<and> \<not> 1 + rr \<le> 0"
              by (simp add: metitarski_simps algebra_simps) (* 8 ms *)
            then have "\<not> rr * (1 + rr) < ln (1 + rr) \<and> \<not> ln (1 + rr) < rr"
              using ff5 by auto (* 8 ms *)
            then have "\<not> rr * - 1 + ln (1 + rr) < 0 \<and> \<not> rr * rr < rr * - 1 + ln (1 + rr)"
              by (simp add: metitarski_simps algebra_simps) (* 4 ms *)
            then have "\<not> rr * rr < \<bar>rr * - 1 + ln (1 + rr)\<bar>"
              using ff3 by simp (* 12 ms *) }
          moreover
          { assume "\<not> rr * (rr * - 1) \<le> 0 \<and> \<not> rr \<le> - 1"
            then have "\<not> 0 \<le> rr"
              by sos (* 16 ms *) }
          ultimately have "\<not> 0 \<le> rr \<or> \<not> rr * rr < \<bar>rr * - 1 + ln (1 + rr)\<bar>"
            by metis (* 12 ms *) }
        ultimately have "\<not> 0 \<le> rr \<or> \<not> - 1 < rr \<or> \<not> rr * rr < \<bar>rr * - 1 + ln (1 + rr)\<bar>"
          by metis (* 12 ms *) }
      ultimately have "\<not> 0 \<le> rr \<or> \<not> - 1 < rr \<or> \<not> rr * rr < \<bar>rr * - 1 + ln (1 + rr)\<bar>"
        by metis (* 24 ms *)
      moreover
      { assume "\<not> rr * rr < \<bar>rr * - 1 + ln (1 + rr)\<bar>"
        then have "\<not> rr\<^sup>2 < \<bar>ln (1 + rr) - rr\<bar>"
          by (simp add: metitarski_simps algebra_simps) (* 4 ms *)
        then have "\<not> rr\<^sup>2 < \<bar>ln (1 + rr) - rr\<bar> \<or> \<not> 0 \<le> rr"
          by metis (* 4 ms *) }
      ultimately have "- 1 < rr \<and> 0 \<le> rr \<longrightarrow> \<not> rr\<^sup>2 < \<bar>ln (1 + rr) - rr\<bar> \<or> \<not> 0 \<le> rr"
        by metis (* 8 ms *) }
    ultimately have "- 1 < rr \<and> 0 \<le> rr \<longrightarrow> \<not> rr\<^sup>2 < \<bar>ln (1 + rr) - rr\<bar> \<or> \<not> 0 \<le> rr"
      by metis (* 8 ms *)
    moreover
    { assume "\<not> - 1 < rr"
      then have "\<not> 0 \<le> rr"
        by sos (* 8 ms *) }
    ultimately have "0 \<le> rr \<longrightarrow> \<not> rr\<^sup>2 < \<bar>ln (1 + rr) - rr\<bar> \<or> \<not> 0 \<le> rr"
      by metis (* 4 ms *)
    moreover
    { assume "\<not> 0 \<le> rr"
      then have "\<not> rr\<^sup>2 < \<bar>ln (1 + rr) - rr\<bar> \<or> \<not> 0 \<le> rr"
        by metis (* 4 ms *) }
    ultimately have "\<not> rr\<^sup>2 < \<bar>ln (1 + rr) - rr\<bar> \<or> \<not> 0 \<le> rr"
      by metis (* 4 ms *) }
  then have "\<forall>r. \<not> (r::real)\<^sup>2 < \<bar>ln (1 + r) - r\<bar> \<or> \<not> 0 \<le> r"
    by blast (* 0.0 ms *)
  then show ?thesis
    by auto (* 800 ms *)
qed
*)  
end
  