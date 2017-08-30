theory "abs-problem-2"
  imports "../GenerateATP"
begin
  
lemma "abs-problem-2": "\<forall>(X::real).(((abs(X) <= 1/2) --> (abs((ln((1 + X)) - X)) <= (2 * power X 2))))" 
  apply(tactic {*fn st => (writeln (isar_proof st @{context}); Seq.single st) *})
proof -
  { fix rr :: real
    have "rr * (rr * 2) < rr * - 1 + ln (1 + rr) \<or> \<bar>rr * - 1 + ln (1 + rr)\<bar> \<noteq> rr * - 1 + ln (1 + rr) \<or> \<bar>rr * - 1 + ln (1 + rr)\<bar> \<le> rr * (rr * 2)"
      by auto (* 20 ms *)
    then have ff1: "rr * - 1 + ln (1 + rr) < 0 \<or> rr * (rr * 2) < rr * - 1 + ln (1 + rr) \<or> \<bar>rr * - 1 + ln (1 + rr)\<bar> \<le> rr * (rr * 2)"
      using abs_nonnegative by blast (* 4 ms *)
    have "\<not> lgen False (X_000043 - 1) X_000044 \<or> X_000043 \<le> 0 \<or> ln X_000043 \<le> X_000044"
      using lgen_le_neg ln_upper_bound_cf1 by blast (* 4 ms *)
    then have ff2: "X_000044 < - 1 + X_000043 \<or> X_000043 \<le> 0 \<or> ln X_000043 \<le> X_000044"
      using metitarski_simps algebra_simps by auto (* 48 ms *)
    have "1 / 2 < \<bar>rr\<bar> \<or> \<bar>rr\<bar> \<noteq> - rr \<or> - rr \<le> 1 / 2"
      by auto (* 4 ms *)
    then have ff3: "1 / 2 < \<bar>rr\<bar> \<or> 0 \<le> rr \<or> - rr \<le> 1 / 2"
      using abs_negative by blast (* 0.0 ms *)
    have "1 / 2 < \<bar>rr\<bar> \<or> \<bar>rr\<bar> \<noteq> rr \<or> rr \<le> 1 / 2"
      by auto (* 8 ms *)
    then have ff4: "rr < 0 \<or> 1 / 2 < \<bar>rr\<bar> \<or> rr \<le> 1 / 2"
      using abs_nonnegative by blast (* 0.0 ms *)
    have "rr * (rr * 2) < - (rr * - 1 + ln (1 + rr)) \<or> \<bar>rr * - 1 + ln (1 + rr)\<bar> \<noteq> - (rr * - 1 + ln (1 + rr)) \<or> \<bar>rr * - 1 + ln (1 + rr)\<bar> \<le> rr * (rr * 2)"
      by auto (* 16 ms *)
    then have ff5: "rr * (rr * 2) < - (rr * - 1 + ln (1 + rr)) \<or> 0 \<le> rr * - 1 + ln (1 + rr) \<or> \<bar>rr * - 1 + ln (1 + rr)\<bar> \<le> rr * (rr * 2)"
      using abs_negative by blast (* 4 ms *)
    have "\<not> lgen False X_000051 ((X_000050 - 1) / X_000050) \<or> X_000050 \<le> 0 \<or> X_000051 \<le> ln X_000050"
      using lgen_le_neg ln_lower_bound_cf1 by blast (* 4 ms *)
    then have ff6: "(- 1 + X_000050) / X_000050 < X_000051 \<or> X_000050 \<le> 0 \<or> X_000051 \<le> ln X_000050"
      using metitarski_simps algebra_simps by auto (* 64 ms *)
    have "\<not> rr \<le> - 1 \<or> \<not> - 1 < rr"
      by force (* 0.0 ms *)
    moreover
    { assume "\<not> rr \<le> - 1"
      then have "\<not> rr * (rr * (- 1 + rr * - 2)) \<le> 0 \<and> \<not> rr \<le> - 1 \<or> \<not> 0 < rr * (rr * (- 1 + rr * - 2)) \<and> \<not> rr \<le> - 1"
        by simp (* 8 ms *)
      moreover
      { assume "\<not> 0 < rr * (rr * (- 1 + rr * - 2)) \<and> \<not> rr \<le> - 1"
        then have "\<not> rr < rr * (1 + rr * - 2) * (1 + rr) \<and> \<not> 1 + rr \<le> 0"
          by (simp add: metitarski_simps algebra_simps) (* 12 ms *)
        then have "\<not> rr / (1 + rr) < rr * (1 + rr * - 2)"
          using leq_right_divide_mul_pos by fastforce (* 56 ms *)
        then have "ln (1 + rr) < rr \<longrightarrow> \<not> rr / (1 + rr) < rr * (1 + rr * - 2) \<and> \<not> rr \<le> ln (1 + rr)"
          by auto (* 4 ms *)
        moreover
        { assume "\<not> rr / (1 + rr) < rr * (1 + rr * - 2) \<and> \<not> rr \<le> ln (1 + rr)"
          then have "- 1 < rr \<longrightarrow> \<not> rr / (1 + rr) < rr * (1 + rr * - 2) \<and> \<not> rr \<le> - 1 \<and> \<not> rr \<le> ln (1 + rr)"
            by auto (* 4 ms *)
          moreover
          { assume "\<not> rr / (1 + rr) < rr * (1 + rr * - 2) \<and> \<not> rr \<le> - 1 \<and> \<not> rr \<le> ln (1 + rr)"
            then have "\<not> (- 1 + (1 + rr)) / (1 + rr) < rr * (1 + rr * - 2) \<and> \<not> 1 + rr \<le> 0 \<and> \<not> rr \<le> ln (1 + rr)"
              by (simp add: metitarski_simps algebra_simps) (* 8 ms *)
            then have "\<not> ln (1 + rr) < rr * (1 + rr * - 2) \<and> \<not> rr \<le> ln (1 + rr)"
              using ff6 by force (* > 5.0 s, timed out *)
            then have "\<not> rr * (rr * 2) < - (rr * - 1 + ln (1 + rr)) \<and> \<not> 0 \<le> rr * - 1 + ln (1 + rr)"
              by (simp add: metitarski_simps algebra_simps) (* 4 ms *)
            then have "\<not> rr * (rr * 2) < \<bar>rr * - 1 + ln (1 + rr)\<bar>"
              using ff5 by simp (* 16 ms *) }
          ultimately have "\<not> - 1 < rr \<or> \<not> rr * (rr * 2) < \<bar>rr * - 1 + ln (1 + rr)\<bar>"
            by metis (* 16 ms *) }
        ultimately have "\<not> ln (1 + rr) < rr \<or> \<not> - 1 < rr \<or> \<not> rr * (rr * 2) < \<bar>rr * - 1 + ln (1 + rr)\<bar>"
          by metis (* 16 ms *) }
      moreover
      { assume "\<not> rr * (rr * (- 1 + rr * - 2)) \<le> 0 \<and> \<not> rr \<le> - 1"
        then have "\<not> 0 < rr * rr \<or> \<not> - 1 / 2 \<le> rr \<or> \<not> rr \<le> 1 / 2"
          by sos (* 88 ms *)
        moreover
        { assume "\<not> 0 < rr * rr"
          then have "\<not> 0 < rr * rr \<and> \<not> - 1 < rr \<or> \<not> 0 < rr * rr \<and> \<not> rr \<le> - 1"
            by auto (* 0.0 ms *)
          moreover
          { assume "\<not> 0 < rr * rr \<and> \<not> rr \<le> - 1"
            then have "\<not> rr < rr * (1 + rr) \<and> \<not> 1 + rr \<le> 0"
              by (simp add: metitarski_simps algebra_simps) (* 4 ms *)
            then have "\<not> rr / (1 + rr) < rr"
              using leq_right_divide_mul_pos by fastforce (* 68 ms *)
            then have "- 1 < rr \<longrightarrow> \<not> rr / (1 + rr) < rr \<and> \<not> rr \<le> - 1"
              by auto (* 4 ms *)
            moreover
            { assume "\<not> rr / (1 + rr) < rr \<and> \<not> rr \<le> - 1"
              then have "\<not> (- 1 + (1 + rr)) / (1 + rr) < rr \<and> \<not> 1 + rr \<le> 0"
                by (simp add: metitarski_simps algebra_simps) (* 4 ms *)
              then have "\<not> ln (1 + rr) < rr"
                using ff6 by metis (* failed *) }
            ultimately have "\<not> ln (1 + rr) < rr \<or> \<not> - 1 < rr"
              by metis (* 12 ms *) }
          moreover
          { assume "\<not> 0 < rr * rr \<and> \<not> - 1 < rr"
            then have "\<not> - 1 / 2 \<le> rr \<or> \<not> rr \<le> 1 / 2"
              by sos (* 12 ms *) }
          ultimately have "\<not> ln (1 + rr) < rr \<or> \<not> - 1 < rr \<or> \<not> - 1 / 2 \<le> rr \<or> \<not> rr \<le> 1 / 2"
            by metis (* 8 ms *) }
        ultimately have "\<not> ln (1 + rr) < rr \<or> \<not> - 1 < rr \<or> \<not> - 1 / 2 \<le> rr \<or> \<not> rr \<le> 1 / 2"
          by metis (* 12 ms *) }
      ultimately have "\<not> ln (1 + rr) < rr \<or> \<not> - 1 < rr \<or> \<not> - 1 / 2 \<le> rr \<or> \<not> rr \<le> 1 / 2 \<or> \<not> rr * (rr * 2) < \<bar>rr * - 1 + ln (1 + rr)\<bar>"
        by metis (* 32 ms *)
      moreover
      { assume "\<not> ln (1 + rr) < rr"
        then have "- 1 < rr \<longrightarrow> \<not> ln (1 + rr) < rr \<and> \<not> rr \<le> - 1"
          by auto (* 0.0 ms *)
        moreover
        { assume "\<not> ln (1 + rr) < rr \<and> \<not> rr \<le> - 1"
          then have "\<not> rr * (rr * - 2) \<le> 0 \<and> \<not> rr \<le> - 1 \<or> \<not> 0 < rr * (rr * - 2) \<and> \<not> ln (1 + rr) < rr \<and> \<not> rr \<le> - 1"
            by force (* 4 ms *)
          moreover
          { assume "\<not> 0 < rr * (rr * - 2) \<and> \<not> ln (1 + rr) < rr \<and> \<not> rr \<le> - 1"
            then have "\<not> rr * (1 + rr * 2) < - 1 + (1 + rr) \<and> \<not> ln (1 + rr) < rr \<and> \<not> 1 + rr \<le> 0"
              by (simp add: metitarski_simps algebra_simps) (* 8 ms *)
            then have "\<not> rr * (1 + rr * 2) < ln (1 + rr) \<and> \<not> ln (1 + rr) < rr"
              using ff2 by metis (* failed *)
            then have "\<not> rr * - 1 + ln (1 + rr) < 0 \<and> \<not> rr * (rr * 2) < rr * - 1 + ln (1 + rr)"
              by (simp add: metitarski_simps algebra_simps) (* 4 ms *)
            then have "\<not> rr * (rr * 2) < \<bar>rr * - 1 + ln (1 + rr)\<bar>"
              using ff1 by auto (* 12 ms *) }
          moreover
          { assume "\<not> rr * (rr * - 2) \<le> 0 \<and> \<not> rr \<le> - 1"
            then have "\<not> - 1 / 2 \<le> rr \<or> \<not> rr \<le> 1 / 2"
              by sos (* 20 ms *) }
          ultimately have "\<not> - 1 / 2 \<le> rr \<or> \<not> rr \<le> 1 / 2 \<or> \<not> rr * (rr * 2) < \<bar>rr * - 1 + ln (1 + rr)\<bar>"
            by metis (* 20 ms *) }
        ultimately have "\<not> - 1 < rr \<or> \<not> - 1 / 2 \<le> rr \<or> \<not> rr \<le> 1 / 2 \<or> \<not> rr * (rr * 2) < \<bar>rr * - 1 + ln (1 + rr)\<bar>"
          by metis (* 12 ms *) }
      ultimately have "\<not> - 1 < rr \<or> \<not> - 1 / 2 \<le> rr \<or> \<not> rr \<le> 1 / 2 \<or> \<not> rr * (rr * 2) < \<bar>rr * - 1 + ln (1 + rr)\<bar>"
        by metis (* 16 ms *)
      moreover
      { assume "\<not> rr * (rr * 2) < \<bar>rr * - 1 + ln (1 + rr)\<bar>"
        then have "\<not> 2 * rr\<^sup>2 < \<bar>ln (1 + rr) - rr\<bar>"
          by (simp add: metitarski_simps algebra_simps) (* 8 ms *)
        then have "\<not> 2 * rr\<^sup>2 < \<bar>ln (1 + rr) - rr\<bar> \<or> \<not> \<bar>rr\<bar> \<le> 1 / 2"
          by metis (* 4 ms *) }
      ultimately have "rr \<le> 1 / 2 \<and> - 1 / 2 \<le> rr \<and> - 1 < rr \<longrightarrow> \<not> 2 * rr\<^sup>2 < \<bar>ln (1 + rr) - rr\<bar> \<or> \<not> \<bar>rr\<bar> \<le> 1 / 2"
        by metis (* 12 ms *) }
    ultimately have "rr \<le> 1 / 2 \<and> - 1 / 2 \<le> rr \<and> - 1 < rr \<longrightarrow> \<not> 2 * rr\<^sup>2 < \<bar>ln (1 + rr) - rr\<bar> \<or> \<not> \<bar>rr\<bar> \<le> 1 / 2"
      by metis (* 12 ms *)
    moreover
    { assume "\<not> - 1 < rr"
      then have "\<not> - 1 / 2 \<le> rr \<or> \<not> rr \<le> 1 / 2"
        by sos (* 16 ms *) }
    ultimately have "rr \<le> 1 / 2 \<and> - 1 / 2 \<le> rr \<longrightarrow> \<not> 2 * rr\<^sup>2 < \<bar>ln (1 + rr) - rr\<bar> \<or> \<not> \<bar>rr\<bar> \<le> 1 / 2"
      by metis (* 16 ms *)
    moreover
    { assume "\<not> - 1 / 2 \<le> rr"
      then have "\<not> rr < 0 \<and> \<not> - 1 / 2 \<le> rr \<or> \<not> - 1 / 2 \<le> rr \<and> \<not> 0 \<le> rr"
        by fastforce (* 4 ms *)
      moreover
      { assume "\<not> - 1 / 2 \<le> rr \<and> \<not> 0 \<le> rr"
        then have "\<not> 0 \<le> rr \<and> \<not> - rr \<le> 1 / 2"
          by (simp add: metitarski_simps algebra_simps) (* 4 ms *)
        then have "\<not> \<bar>rr\<bar> \<le> 1 / 2"
          using ff3 by auto (* 16 ms *) }
      moreover
      { assume "\<not> rr < 0 \<and> \<not> - 1 / 2 \<le> rr"
        then have "\<not> rr \<le> 1 / 2"
          by sos (* 20 ms *) }
      ultimately have "\<not> \<bar>rr\<bar> \<le> 1 / 2 \<or> \<not> rr \<le> 1 / 2"
        by metis (* 8 ms *) }
    ultimately have "rr \<le> 1 / 2 \<and> \<bar>rr\<bar> \<le> 1 / 2 \<longrightarrow> \<not> 2 * rr\<^sup>2 < \<bar>ln (1 + rr) - rr\<bar> \<or> \<not> \<bar>rr\<bar> \<le> 1 / 2"
      by metis (* 8 ms *)
    moreover
    { assume aaa1: "\<not> rr \<le> 1 / 2"
      have "0 \<le> rr \<or> rr \<le> 1 / 2"
        by auto (* 4 ms *)
      then have "\<not> rr < 0 \<and> \<not> rr \<le> 1 / 2"
        using aaa1 by force (* 0.0 ms *)
      then have "\<not> \<bar>rr\<bar> \<le> 1 / 2"
        using ff4 by auto (* 12 ms *) }
    ultimately have "\<bar>rr\<bar> \<le> 1 / 2 \<longrightarrow> \<not> 2 * rr\<^sup>2 < \<bar>ln (1 + rr) - rr\<bar> \<or> \<not> \<bar>rr\<bar> \<le> 1 / 2"
      by metis (* 12 ms *)
    moreover
    { assume "\<not> \<bar>rr\<bar> \<le> 1 / 2"
      then have "\<not> 2 * rr\<^sup>2 < \<bar>ln (1 + rr) - rr\<bar> \<or> \<not> \<bar>rr\<bar> \<le> 1 / 2"
        by metis (* 8 ms *) }
    ultimately have "\<not> 2 * rr\<^sup>2 < \<bar>ln (1 + rr) - rr\<bar> \<or> \<not> \<bar>rr\<bar> \<le> 1 / 2"
      by metis (* 8 ms *) }
  then have "\<forall>r. \<not> 2 * (r::real)\<^sup>2 < \<bar>ln (1 + r) - r\<bar> \<or> \<not> \<bar>r\<bar> \<le> 1 / 2"
    by blast (* 0.0 ms *)
  then show ?thesis
    by auto (* 28 ms *)
qed
end