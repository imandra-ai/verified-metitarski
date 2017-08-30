theory "abs-problem-1"
  imports "../GenerateATP"
begin
  
lemma "abs-problem-1": "\<forall>(X::real).(0\<le>X \<longrightarrow> abs(ln(1+X)-X) \<le> X^2)"
(*  apply(tactic {*fn st => (writeln (isar_proof st @{context}); Seq.single st) *})*)
proof -
  { fix rr :: real
    have "rr * rr < rr * - 1 + ln (1 + rr) \<or> \<bar>rr * - 1 + ln (1 + rr)\<bar> \<noteq> rr * - 1 + ln (1 + rr) \<or> \<bar>rr * - 1 + ln (1 + rr)\<bar> \<le> rr * rr"
      by auto (* 16 ms *)
    then have ff1: "rr * - 1 + ln (1 + rr) < 0 \<or> rr * rr < rr * - 1 + ln (1 + rr) \<or> \<bar>rr * - 1 + ln (1 + rr)\<bar> \<le> rr * rr"
      using abs_nonnegative by blast (* 0.0 ms *)
    have "\<not> lgen False (X_000043 - 1) X_000044 \<or> X_000043 \<le> 0 \<or> ln X_000043 \<le> X_000044"
      using lgen_le_neg ln_upper_bound_cf1 by blast (* 4 ms *)
    then have ff2: "X_000044 < - 1 + X_000043 \<or> X_000043 \<le> 0 \<or> ln X_000043 \<le> X_000044"
      using metitarski_simps algebra_simps by auto (* 52 ms *)
    have "rr * rr < - (rr * - 1 + ln (1 + rr)) \<or> \<bar>rr * - 1 + ln (1 + rr)\<bar> \<noteq> - (rr * - 1 + ln (1 + rr)) \<or> \<bar>rr * - 1 + ln (1 + rr)\<bar> \<le> rr * rr"
      by auto (* 20 ms *)
    then have ff3: "rr * rr < - (rr * - 1 + ln (1 + rr)) \<or> 0 \<le> rr * - 1 + ln (1 + rr) \<or> \<bar>rr * - 1 + ln (1 + rr)\<bar> \<le> rr * rr"
      using abs_negative by blast (* 4 ms *)
    have "\<And>X_000050 X_000051. \<not> lgen False X_000051 ((X_000050 - 1) / X_000050) \<or> X_000050 \<le> 0 \<or> X_000051 \<le> ln X_000050"
      using lgen_le_neg ln_lower_bound_cf1 by blast (* 4 ms *)
    then have ff4: "\<And>X_000050 X_000051. (- 1 + X_000050) / X_000050 < X_000051 \<or> X_000050 \<le> 0 \<or> X_000051 \<le> ln X_000050"
      using algebra_simps
      apply -
      apply(atomize)  
      sledgehammer[max_facts = 25]  
      apply(rule allE)

        
      sledgehammer(* 168 ms *)
    have "\<not> rr \<le> - 1 \<or> \<not> - 1 < rr"
      by fastforce (* 0.0 ms *)
    moreover
    { assume "\<not> rr \<le> - 1"
      then have "\<not> rr * (rr * (rr * - 1)) \<le> 0 \<and> \<not> rr \<le> - 1 \<or> \<not> 0 < rr * (rr * (rr * - 1)) \<and> \<not> rr \<le> - 1"
        by fastforce (* 0.0 ms *)
      moreover
      { assume "\<not> 0 < rr * (rr * (rr * - 1)) \<and> \<not> rr \<le> - 1"
        then have "\<not> rr < rr * (1 + rr * - 1) * (1 + rr) \<and> \<not> 1 + rr \<le> 0"
          by (simp add: metitarski_simps algebra_simps) (* 44 ms *)
        then have "\<not> rr / (1 + rr) < rr * (1 + rr * - 1)"
          using leq_right_divide_mul_pos by fastforce (* 300 ms *)
        then have "ln (1 + rr) < rr \<longrightarrow> \<not> rr / (1 + rr) < rr * (1 + rr * - 1) \<and> \<not> rr \<le> ln (1 + rr)"
          by auto (* 4 ms *)
        moreover
        { assume "\<not> rr / (1 + rr) < rr * (1 + rr * - 1) \<and> \<not> rr \<le> ln (1 + rr)"
          then have "- 1 < rr \<longrightarrow> \<not> rr / (1 + rr) < rr * (1 + rr * - 1) \<and> \<not> rr \<le> - 1 \<and> \<not> rr \<le> ln (1 + rr)"
            by auto (* 16 ms *)
          moreover
          { assume "\<not> rr / (1 + rr) < rr * (1 + rr * - 1) \<and> \<not> rr \<le> - 1 \<and> \<not> rr \<le> ln (1 + rr)"
            then have "\<not> (- 1 + (1 + rr)) / (1 + rr) < rr * (1 + rr * - 1) \<and> \<not> 1 + rr \<le> 0 \<and> \<not> rr \<le> ln (1 + rr)"
              by (simp add: metitarski_simps algebra_simps) (* 8 ms *)
            then have "\<not> ln (1 + rr) < rr * (1 + rr * - 1) \<and> \<not> rr \<le> ln (1 + rr)"
              using ff4 by force (* > 5.0 s, timed out *)
            then have "\<not> rr * rr < - (rr * - 1 + ln (1 + rr)) \<and> \<not> 0 \<le> rr * - 1 + ln (1 + rr)"
              by (simp add: metitarski_simps algebra_simps) (* 4 ms *)
            then have "\<not> rr * rr < \<bar>rr * - 1 + ln (1 + rr)\<bar>"
              using ff3 by force (* 36 ms *) }
          ultimately have "\<not> - 1 < rr \<or> \<not> rr * rr < \<bar>rr * - 1 + ln (1 + rr)\<bar>"
            by metis (* 12 ms *) }
        ultimately have "\<not> ln (1 + rr) < rr \<or> \<not> - 1 < rr \<or> \<not> rr * rr < \<bar>rr * - 1 + ln (1 + rr)\<bar>"
          by metis (* 44 ms *) }
      moreover
      { assume "\<not> rr * (rr * (rr * - 1)) \<le> 0 \<and> \<not> rr \<le> - 1"
        then have "\<not> 0 \<le> rr \<or> \<not> 0 < rr * rr"
          by sos (* 76 ms *)
        moreover
        { assume "\<not> 0 < rr * rr"
          then have "\<not> 0 < rr * rr \<and> \<not> - 1 < rr \<or> \<not> 0 < rr * rr \<and> \<not> rr \<le> - 1"
            by auto (* 0.0 ms *)
          moreover
          { assume "\<not> 0 < rr * rr \<and> \<not> rr \<le> - 1"
            then have "\<not> rr < rr * (1 + rr) \<and> \<not> 1 + rr \<le> 0"
              by (simp add: metitarski_simps algebra_simps) (* 0.0 ms *)
            then have "\<not> rr / (1 + rr) < rr"
              using leq_right_divide_mul_pos by fastforce (* 68 ms *)
            then have "- 1 < rr \<longrightarrow> \<not> rr / (1 + rr) < rr \<and> \<not> rr \<le> - 1"
              by simp (* 0.0 ms *)
            moreover
            { assume "\<not> rr / (1 + rr) < rr \<and> \<not> rr \<le> - 1"
              then have "\<not> (- 1 + (1 + rr)) / (1 + rr) < rr \<and> \<not> 1 + rr \<le> 0"
                by (simp add: metitarski_simps algebra_simps) (* 4 ms *)
              then have "\<not> ln (1 + rr) < rr"
                using ff4 by metis (* failed *) }
            ultimately have "\<not> ln (1 + rr) < rr \<or> \<not> - 1 < rr"
              by metis (* 12 ms *) }
          moreover
          { assume "\<not> 0 < rr * rr \<and> \<not> - 1 < rr"
            then have "\<not> 0 \<le> rr"
              by sos (* 24 ms *) }
          ultimately have "\<not> 0 \<le> rr \<or> \<not> ln (1 + rr) < rr \<or> \<not> - 1 < rr"
            by metis (* 16 ms *) }
        ultimately have "\<not> 0 \<le> rr \<or> \<not> ln (1 + rr) < rr \<or> \<not> - 1 < rr"
          by metis (* 8 ms *) }
      ultimately have "\<not> 0 \<le> rr \<or> \<not> ln (1 + rr) < rr \<or> \<not> - 1 < rr \<or> \<not> rr * rr < \<bar>rr * - 1 + ln (1 + rr)\<bar>"
        by metis (* 16 ms *)
      moreover
      { assume "\<not> ln (1 + rr) < rr"
        then have "- 1 < rr \<longrightarrow> \<not> ln (1 + rr) < rr \<and> \<not> rr \<le> - 1"
          by auto (* 4 ms *)
        moreover
        { assume "\<not> ln (1 + rr) < rr \<and> \<not> rr \<le> - 1"
          then have "\<not> rr * (rr * - 1) \<le> 0 \<and> \<not> rr \<le> - 1 \<or> \<not> 0 < rr * (rr * - 1) \<and> \<not> ln (1 + rr) < rr \<and> \<not> rr \<le> - 1"
            by auto (* 4 ms *)
          moreover
          { assume "\<not> 0 < rr * (rr * - 1) \<and> \<not> ln (1 + rr) < rr \<and> \<not> rr \<le> - 1"
            then have "\<not> rr * (1 + rr) < - 1 + (1 + rr) \<and> \<not> ln (1 + rr) < rr \<and> \<not> 1 + rr \<le> 0"
              by (simp add: metitarski_simps algebra_simps) (* 8 ms *)
            then have "\<not> rr * (1 + rr) < ln (1 + rr) \<and> \<not> ln (1 + rr) < rr"
              using ff2 by metis (* failed *)
            then have "\<not> rr * - 1 + ln (1 + rr) < 0 \<and> \<not> rr * rr < rr * - 1 + ln (1 + rr)"
              by (simp add: metitarski_simps algebra_simps) (* 4 ms *)
            then have "\<not> rr * rr < \<bar>rr * - 1 + ln (1 + rr)\<bar>"
              using ff1 by auto (* 36 ms *) }
          moreover
          { assume "\<not> rr * (rr * - 1) \<le> 0 \<and> \<not> rr \<le> - 1"
            then have "\<not> 0 \<le> rr"
              by sos (* 24 ms *) }
          ultimately have "\<not> 0 \<le> rr \<or> \<not> rr * rr < \<bar>rr * - 1 + ln (1 + rr)\<bar>"
            by metis (* 28 ms *) }
        ultimately have "\<not> 0 \<le> rr \<or> \<not> - 1 < rr \<or> \<not> rr * rr < \<bar>rr * - 1 + ln (1 + rr)\<bar>"
          by metis (* 8 ms *) }
      ultimately have "\<not> 0 \<le> rr \<or> \<not> - 1 < rr \<or> \<not> rr * rr < \<bar>rr * - 1 + ln (1 + rr)\<bar>"
        by metis (* 12 ms *)
      moreover
      { assume "\<not> rr * rr < \<bar>rr * - 1 + ln (1 + rr)\<bar>"
        then have "\<not> rr\<^sup>2 < \<bar>ln (1 + rr) - rr\<bar>"
          by (simp add: metitarski_simps algebra_simps) (* 8 ms *)
        then have "\<not> rr\<^sup>2 < \<bar>ln (1 + rr) - rr\<bar> \<or> \<not> 0 \<le> rr"
          by metis (* 4 ms *) }
      ultimately have "- 1 < rr \<and> 0 \<le> rr \<longrightarrow> \<not> rr\<^sup>2 < \<bar>ln (1 + rr) - rr\<bar> \<or> \<not> 0 \<le> rr"
        by metis (* 4 ms *) }
    ultimately have "- 1 < rr \<and> 0 \<le> rr \<longrightarrow> \<not> rr\<^sup>2 < \<bar>ln (1 + rr) - rr\<bar> \<or> \<not> 0 \<le> rr"
      by metis (* 8 ms *)
    moreover
    { assume "\<not> - 1 < rr"
      then have "\<not> 0 \<le> rr"
        by sos (* 16 ms *) }
    ultimately have "0 \<le> rr \<longrightarrow> \<not> rr\<^sup>2 < \<bar>ln (1 + rr) - rr\<bar> \<or> \<not> 0 \<le> rr"
      by metis (* 8 ms *)
    moreover
    { assume "\<not> 0 \<le> rr"
      then have "\<not> rr\<^sup>2 < \<bar>ln (1 + rr) - rr\<bar> \<or> \<not> 0 \<le> rr"
        by metis (* 0.0 ms *) }
    ultimately have "\<not> rr\<^sup>2 < \<bar>ln (1 + rr) - rr\<bar> \<or> \<not> 0 \<le> rr"
      by metis (* 4 ms *) }
  then have "\<forall>r. \<not> (r::real)\<^sup>2 < \<bar>ln (1 + r) - r\<bar> \<or> \<not> 0 \<le> r"
    by meson (* 0.0 ms *)
  then show ?thesis
    by auto (* 1.0 s *)
qed  
  
end
  