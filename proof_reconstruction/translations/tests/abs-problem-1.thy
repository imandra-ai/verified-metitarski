theory "abs-problem-1"
  imports "../GenerateATP"
begin
  
lemma "abs-problem-1": "\<forall>(X::real).(0\<le>X \<longrightarrow> abs(ln(1+X)-X) \<le> X^2)"
  apply(tactic {*fn st => (writeln (isar_proof st @{context}); Seq.single st) *})
proof -
  { fix rr :: real
    have "rr * rr < rr * - 1 + ln (1 + rr) \<or> \<bar>rr * - 1 + ln (1 + rr)\<bar> \<noteq> rr * - 1 + ln (1 + rr) \<or> \<bar>rr * - 1 + ln (1 + rr)\<bar> \<le> rr * rr"
      by auto (* 8 ms *)
    then have ff1: "rr * - 1 + ln (1 + rr) < 0 \<or> rr * rr < rr * - 1 + ln (1 + rr) \<or> \<bar>rr * - 1 + ln (1 + rr)\<bar> \<le> rr * rr"
      using abs_nonnegative by blast (* 4 ms *)
    have "\<And>r ra. \<not> lgen False (ra - 1) r \<or> ra \<le> 0 \<or> ln ra \<le> r"
      using lgen_le_neg ln_upper_bound_cf1 by blast (* 20 ms *)
    then have ff2: "\<And>r ra. (ra::real) < - 1 + r \<or> r \<le> 0 \<or> ln r \<le> ra"
      using metitarski_simps algebra_simps by auto (* 28 ms *)
    have "rr * rr < - (rr * - 1 + ln (1 + rr)) \<or> \<bar>rr * - 1 + ln (1 + rr)\<bar> \<noteq> - (rr * - 1 + ln (1 + rr)) \<or> \<bar>rr * - 1 + ln (1 + rr)\<bar> \<le> rr * rr"
      by auto (* 20 ms *)
    then have ff3: "rr * rr < - (rr * - 1 + ln (1 + rr)) \<or> 0 \<le> rr * - 1 + ln (1 + rr) \<or> \<bar>rr * - 1 + ln (1 + rr)\<bar> \<le> rr * rr"
      using abs_negative by blast (* 0.0 ms *)
    have "\<And>r ra. \<not> lgen False ra ((r - 1) / r) \<or> r \<le> 0 \<or> ra \<le> ln r"
      using lgen_le_neg ln_lower_bound_cf1 by blast (* 8 ms *)
    then have ff4: "\<And>r ra. (- (1::real) + ra) / ra < r \<or> ra \<le> 0 \<or> r \<le> ln ra"
      using metitarski_simps algebra_simps by auto (* 92 ms *)
    have "\<not> rr \<le> - 1 \<or> \<not> - 1 < rr"
      by auto (* 4 ms *)
    moreover
    { assume "\<not> rr \<le> - 1"
      then have "\<not> rr * (rr * (rr * - 1)) \<le> 0 \<and> \<not> rr \<le> - 1 \<or> \<not> 0 < rr * (rr * (rr * - 1)) \<and> \<not> rr \<le> - 1"
        by auto (* 12 ms *)
      moreover
      { assume "\<not> 0 < rr * (rr * (rr * - 1)) \<and> \<not> rr \<le> - 1"
        then have "\<not> rr < rr * (1 + rr * - 1) * (1 + rr) \<and> \<not> 1 + rr \<le> 0"
          by (simp add: metitarski_simps algebra_simps) (* 16 ms *)
        then have "\<not> rr / (1 + rr) < rr * (1 + rr * - 1)"
          using leq_right_divide_mul_pos by fastforce (* 124 ms *)
        then have "ln (1 + rr) < rr \<longrightarrow> \<not> rr / (1 + rr) < rr * (1 + rr * - 1) \<and> \<not> rr \<le> ln (1 + rr)"
          by auto (* 4 ms *)
        moreover
        { assume "\<not> rr / (1 + rr) < rr * (1 + rr * - 1) \<and> \<not> rr \<le> ln (1 + rr)"
          then have "- 1 < rr \<longrightarrow> \<not> rr / (1 + rr) < rr * (1 + rr * - 1) \<and> \<not> rr \<le> - 1 \<and> \<not> rr \<le> ln (1 + rr)"
            by simp (* 4 ms *)
          moreover
          { assume "\<not> rr / (1 + rr) < rr * (1 + rr * - 1) \<and> \<not> rr \<le> - 1 \<and> \<not> rr \<le> ln (1 + rr)"
            then have "\<not> (- 1 + (1 + rr)) / (1 + rr) < rr * (1 + rr * - 1) \<and> \<not> 1 + rr \<le> 0 \<and> \<not> rr \<le> ln (1 + rr)"
              by (simp add: metitarski_simps algebra_simps) (* 4 ms *)
            then have "\<not> ln (1 + rr) < rr * (1 + rr * - 1) \<and> \<not> rr \<le> ln (1 + rr)"
              using ff4 by fastforce (* 544 ms *)
            then have "\<not> rr * rr < - (rr * - 1 + ln (1 + rr)) \<and> \<not> 0 \<le> rr * - 1 + ln (1 + rr)"
              by (simp add: metitarski_simps algebra_simps) (* 4 ms *)
            then have "\<not> rr * rr < \<bar>rr * - 1 + ln (1 + rr)\<bar>"
              using ff3 by simp (* 60 ms *) }
          ultimately have "\<not> - 1 < rr \<or> \<not> rr * rr < \<bar>rr * - 1 + ln (1 + rr)\<bar>"
            by metis (* 12 ms *) }
        ultimately have "\<not> ln (1 + rr) < rr \<or> \<not> - 1 < rr \<or> \<not> rr * rr < \<bar>rr * - 1 + ln (1 + rr)\<bar>"
          by metis (* 12 ms *) }
      moreover
      { assume "\<not> rr * (rr * (rr * - 1)) \<le> 0 \<and> \<not> rr \<le> - 1"
        then have "\<not> 0 \<le> rr \<or> \<not> 0 < rr * rr"
          by sos (* 40 ms *)
        moreover
        { assume "\<not> 0 < rr * rr"
          then have "\<not> 0 < rr * rr \<and> \<not> - 1 < rr \<or> \<not> 0 < rr * rr \<and> \<not> rr \<le> - 1"
            by simp (* 0.0 ms *)
          moreover
          { assume "\<not> 0 < rr * rr \<and> \<not> rr \<le> - 1"
            then have "\<not> rr < rr * (1 + rr) \<and> \<not> 1 + rr \<le> 0"
              by (simp add: metitarski_simps algebra_simps) (* 0.0 ms *)
            then have "\<not> rr / (1 + rr) < rr"
              using leq_right_divide_mul_pos by fastforce (* 96 ms *)
            then have "- 1 < rr \<longrightarrow> \<not> rr / (1 + rr) < rr \<and> \<not> rr \<le> - 1"
              by auto (* 4 ms *)
            moreover
            { assume "\<not> rr / (1 + rr) < rr \<and> \<not> rr \<le> - 1"
              then have "\<not> (- 1 + (1 + rr)) / (1 + rr) < rr \<and> \<not> 1 + rr \<le> 0"
                by (simp add: metitarski_simps algebra_simps) (* 4 ms *)
              then have "\<not> ln (1 + rr) < rr"
                using ff4 by fastforce (* 112 ms *) }
            ultimately have "\<not> ln (1 + rr) < rr \<or> \<not> - 1 < rr"
              by metis (* 4 ms *) }
          moreover
          { assume "\<not> 0 < rr * rr \<and> \<not> - 1 < rr"
            then have "\<not> 0 \<le> rr"
              by sos (* 8 ms *) }
          ultimately have "\<not> 0 \<le> rr \<or> \<not> ln (1 + rr) < rr \<or> \<not> - 1 < rr"
            by metis (* 8 ms *) }
        ultimately have "\<not> 0 \<le> rr \<or> \<not> ln (1 + rr) < rr \<or> \<not> - 1 < rr"
          by metis (* 12 ms *) }
      ultimately have "\<not> 0 \<le> rr \<or> \<not> ln (1 + rr) < rr \<or> \<not> - 1 < rr \<or> \<not> rr * rr < \<bar>rr * - 1 + ln (1 + rr)\<bar>"
        by metis (* 16 ms *)
      moreover
      { assume "\<not> ln (1 + rr) < rr"
        then have "- 1 < rr \<longrightarrow> \<not> ln (1 + rr) < rr \<and> \<not> rr \<le> - 1"
          by fastforce (* 0.0 ms *)
        moreover
        { assume "\<not> ln (1 + rr) < rr \<and> \<not> rr \<le> - 1"
          then have "\<not> rr * (rr * - 1) \<le> 0 \<and> \<not> rr \<le> - 1 \<or> \<not> 0 < rr * (rr * - 1) \<and> \<not> ln (1 + rr) < rr \<and> \<not> rr \<le> - 1"
            by auto (* 4 ms *)
          moreover
          { assume "\<not> 0 < rr * (rr * - 1) \<and> \<not> ln (1 + rr) < rr \<and> \<not> rr \<le> - 1"
            then have "\<not> rr * (1 + rr) < - 1 + (1 + rr) \<and> \<not> ln (1 + rr) < rr \<and> \<not> 1 + rr \<le> 0"
              by (simp add: metitarski_simps algebra_simps) (* 8 ms *)
            then have "\<not> rr * (1 + rr) < ln (1 + rr) \<and> \<not> ln (1 + rr) < rr"
              using ff2 by fastforce (* 280 ms *)
            then have "\<not> rr * - 1 + ln (1 + rr) < 0 \<and> \<not> rr * rr < rr * - 1 + ln (1 + rr)"
              by (simp add: metitarski_simps algebra_simps) (* 8 ms *)
            then have "\<not> rr * rr < \<bar>rr * - 1 + ln (1 + rr)\<bar>"
              using ff1 by simp (* 48 ms *) }
          moreover
          { assume "\<not> rr * (rr * - 1) \<le> 0 \<and> \<not> rr \<le> - 1"
            then have "\<not> 0 \<le> rr"
              by sos (* 16 ms *) }
          ultimately have "\<not> 0 \<le> rr \<or> \<not> rr * rr < \<bar>rr * - 1 + ln (1 + rr)\<bar>"
            by metis (* 24 ms *) }
        ultimately have "\<not> 0 \<le> rr \<or> \<not> - 1 < rr \<or> \<not> rr * rr < \<bar>rr * - 1 + ln (1 + rr)\<bar>"
          by metis (* 12 ms *) }
      ultimately have "\<not> 0 \<le> rr \<or> \<not> - 1 < rr \<or> \<not> rr * rr < \<bar>rr * - 1 + ln (1 + rr)\<bar>"
        by metis (* 16 ms *)
      moreover
      { assume "\<not> rr * rr < \<bar>rr * - 1 + ln (1 + rr)\<bar>"
        then have "\<not> rr\<^sup>2 < \<bar>ln (1 + rr) - rr\<bar>"
          by (simp add: metitarski_simps algebra_simps) (* 8 ms *)
        then have "\<not> rr\<^sup>2 < \<bar>ln (1 + rr) - rr\<bar> \<or> \<not> 0 \<le> rr"
          by metis (* 8 ms *) }
      ultimately have "- 1 < rr \<and> 0 \<le> rr \<longrightarrow> \<not> rr\<^sup>2 < \<bar>ln (1 + rr) - rr\<bar> \<or> \<not> 0 \<le> rr"
        by metis (* 4 ms *) }
    ultimately have "- 1 < rr \<and> 0 \<le> rr \<longrightarrow> \<not> rr\<^sup>2 < \<bar>ln (1 + rr) - rr\<bar> \<or> \<not> 0 \<le> rr"
      by metis (* 4 ms *)
    moreover
    { assume "\<not> - 1 < rr"
      then have "\<not> 0 \<le> rr"
        by sos (* 4 ms *) }
    ultimately have "0 \<le> rr \<longrightarrow> \<not> rr\<^sup>2 < \<bar>ln (1 + rr) - rr\<bar> \<or> \<not> 0 \<le> rr"
      by metis (* 8 ms *)
    moreover
    { assume "\<not> 0 \<le> rr"
      then have "\<not> rr\<^sup>2 < \<bar>ln (1 + rr) - rr\<bar> \<or> \<not> 0 \<le> rr"
        by metis (* 0.0 ms *) }
    ultimately have "\<not> rr\<^sup>2 < \<bar>ln (1 + rr) - rr\<bar> \<or> \<not> 0 \<le> rr"
      by metis (* 4 ms *) }
  then have "\<forall>r. \<not> (r::real)\<^sup>2 < \<bar>ln (1 + r) - r\<bar> \<or> \<not> 0 \<le> r"
    by blast (* 0.0 ms *)
  then show ?thesis
    by auto (* 1.0 s *)
qed

end
  