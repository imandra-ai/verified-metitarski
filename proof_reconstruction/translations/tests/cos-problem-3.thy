theory "cos-problem-3"
  imports "../GenerateATP"
    "~/Documents/internship/verified-metitarski/isabelle-proofs/CosBounds"
begin
  
lemma "\<forall>(X::real).((Not((1 <= abs(X))) --> (abs(cos(X)) <= 1)))
" 
  apply(tactic {*fn st => (writeln (isar_proof st [] @{context}); Seq.single st) *})
proof -
  { fix rr :: real
    have ff1: "\<And>r ra. \<not> lgen False ra (cos r) \<or> ra \<le> cos r"
      using lgen_le_neg by auto (* 0.0 ms *)
    have "\<And>r ra. \<not> lgen False ra (1 - r\<^sup>2 / 2) \<or> lgen False ra (cos r)"
      using cos_lower_bound_0 by blast (* 4 ms *)
    then have "\<And>r ra. \<not> lgen False ra (1 - r\<^sup>2 / 2) \<or> ra \<le> cos r"
      using ff1 by blast (* 4 ms *)
    then have "\<And>r ra. (1::real) + ra * (ra * (- 1 / 2)) < r \<or> r \<le> cos ra"
      by mt_arith_rule (* failed *)
    then have ff2: "1 + rr * (rr * (- 1 / 2)) < 0 \<or> 0 \<le> cos rr"
      by blast (* 4 ms *)
    have ff3: "cos rr < 0 \<or> \<bar>cos rr\<bar> = cos rr"
      using abs_nonnegative by blast (* 0.0 ms *)
    have "1 < cos rr \<or> \<bar>cos rr\<bar> \<noteq> cos rr \<or> \<bar>cos rr\<bar> \<le> 1"
      by auto (* 4 ms *)
    then have ff4: "cos rr < 0 \<or> 1 < cos rr \<or> \<bar>cos rr\<bar> \<le> 1"
      using ff3 by fastforce (* 0.0 ms *)
    have ff5: "\<And>r ra. \<not> lgen False (cos ra) r \<or> cos ra \<le> r"
      using lgen_le_neg by auto (* 0.0 ms *)
    have "\<And>r ra. \<not> lgen False (1 - ra\<^sup>2 / 2 + ra ^ 4 / 24) r \<or> lgen False (cos ra) r"
      using cos_upper_bound_0 by blast (* 4 ms *)
    then have "\<And>r ra. \<not> lgen False (1 - ra\<^sup>2 / 2 + ra ^ 4 / 24) r \<or> cos ra \<le> r"
      using ff5 by blast (* 4 ms *)
    then have "\<And>r ra. (ra::real) < 1 + r * (r * (- 1 / 2 + r * (r * (1 / 24)))) \<or> cos r \<le> ra"
      by mt_arith_rule (* failed *)
    then have ff6: "1 < 1 + rr * (rr * (- 1 / 2 + rr * (rr * (1 / 24)))) \<or> cos rr \<le> 1"
      by blast (* 4 ms *)
    have ff7: "0 \<le> rr \<or> \<bar>rr\<bar> = - rr"
      using abs_negative by blast (* 0.0 ms *)
    have "- rr < 1 \<or> \<bar>rr\<bar> \<noteq> - rr \<or> 1 \<le> \<bar>rr\<bar>"
      by auto (* 16 ms *)
    then have ff8: "- rr < 1 \<or> 0 \<le> rr \<or> 1 \<le> \<bar>rr\<bar>"
      using ff7 by fastforce (* 0.0 ms *)
    have ff9: "rr < 0 \<or> \<bar>rr\<bar> = rr"
      using abs_nonnegative by blast (* 4 ms *)
    have "rr < 1 \<or> \<bar>rr\<bar> \<noteq> rr \<or> 1 \<le> \<bar>rr\<bar>"
      by auto (* 20 ms *)
    then have ff10: "rr < 0 \<or> rr < 1 \<or> 1 \<le> \<bar>rr\<bar>"
      using ff9 by fastforce (* 0.0 ms *)
    have "\<not> rr * (rr * (1 / 2)) \<le> 1 \<or> \<not> 1 < rr * (rr * (1 / 2))"
      by auto (* 20 ms *)
    moreover
    { assume "\<not> 1 < rr * (rr * (1 / 2))"
      then have "\<not> 1 + rr * (rr * (- 1 / 2)) < 0"
        by mt_arith_rule (* failed *)
      then have "\<not> cos rr < 0"
        using ff2 by fastforce (* 4 ms *)
      then have "rr * (rr * (- 1 / 2 + rr * (rr * (1 / 24)))) \<le> 0 \<longrightarrow> \<not> cos rr < 0 \<and> \<not> 0 < rr * (rr * (- 1 / 2 + rr * (rr * (1 / 24))))"
        by auto (* 4 ms *)
      moreover
      { assume "\<not> cos rr < 0 \<and> \<not> 0 < rr * (rr * (- 1 / 2 + rr * (rr * (1 / 24))))"
        then have "\<not> cos rr < 0 \<and> \<not> 1 < 1 + rr * (rr * (- 1 / 2 + rr * (rr * (1 / 24))))"
          by mt_arith_rule (* failed *)
        then have "\<not> cos rr < 0 \<and> \<not> 1 < cos rr"
          using ff6 by fastforce (* 24 ms *)
        then have "\<not> 1 < \<bar>cos rr\<bar>"
          using ff4 by simp (* 0.0 ms *)
        then have "\<not> \<bar>rr\<bar> < 1 \<or> \<not> 1 < \<bar>cos rr\<bar>"
          by metis (* 4 ms *) }
      moreover
      { assume "\<not> rr * (rr * (- 1 / 2 + rr * (rr * (1 / 24)))) \<le> 0"
        then have "\<not> - 1 < rr \<or> \<not> rr < 1"
          by sos (* 104 ms *) }
      ultimately have "rr < 1 \<and> - 1 < rr \<longrightarrow> \<not> \<bar>rr\<bar> < 1 \<or> \<not> 1 < \<bar>cos rr\<bar>"
        by metis (* 8 ms *) }
    moreover
    { assume "\<not> rr * (rr * (1 / 2)) \<le> 1"
      then have "\<not> - 1 < rr \<or> \<not> rr < 1"
        by sos (* 44 ms *) }
    ultimately have "rr < 1 \<and> - 1 < rr \<longrightarrow> \<not> \<bar>rr\<bar> < 1 \<or> \<not> 1 < \<bar>cos rr\<bar>"
      by metis (* 4 ms *)
    moreover
    { assume "\<not> - 1 < rr"
      then have "\<not> rr < 0 \<and> \<not> - 1 < rr \<or> \<not> - 1 < rr \<and> \<not> 0 \<le> rr"
        by force (* 4 ms *)
      moreover
      { assume "\<not> - 1 < rr \<and> \<not> 0 \<le> rr"
        then have "\<not> - rr < 1 \<and> \<not> 0 \<le> rr"
          by mt_arith_rule (* failed *)
        then have "\<not> \<bar>rr\<bar> < 1"
          using ff8 by auto (* 8 ms *) }
      moreover
      { assume "\<not> rr < 0 \<and> \<not> - 1 < rr"
        then have "\<not> rr < 1"
          by sos (* 8 ms *) }
      ultimately have "\<not> \<bar>rr\<bar> < 1 \<or> \<not> rr < 1"
        by metis (* 8 ms *) }
    ultimately have "rr < 1 \<and> \<bar>rr\<bar> < 1 \<longrightarrow> \<not> \<bar>rr\<bar> < 1 \<or> \<not> 1 < \<bar>cos rr\<bar>"
      by metis (* 4 ms *)
    moreover
    { assume aaa1: "\<not> rr < 1"
      have "rr < 1 \<or> 0 \<le> rr"
        by auto (* 4 ms *)
      then have "\<not> rr < 0 \<and> \<not> rr < 1"
        using aaa1 by fastforce (* 0.0 ms *)
      then have "\<not> \<bar>rr\<bar> < 1"
        using ff10 by auto (* 8 ms *) }
    ultimately have "\<bar>rr\<bar> < 1 \<longrightarrow> \<not> \<bar>rr\<bar> < 1 \<or> \<not> 1 < \<bar>cos rr\<bar>"
      by metis (* 4 ms *)
    moreover
    { assume "\<not> \<bar>rr\<bar> < 1"
      then have "\<not> \<bar>rr\<bar> < 1 \<or> \<not> 1 < \<bar>cos rr\<bar>"
        by metis (* 4 ms *) }
    ultimately have "\<not> \<bar>rr\<bar> < 1 \<or> \<not> 1 < \<bar>cos rr\<bar>"
      by metis (* 4 ms *) }
  then have "\<forall>r. \<not> \<bar>r::real\<bar> < 1 \<or> \<not> 1 < \<bar>cos r\<bar>"
    by blast (* 0.0 ms *)
  then show ?thesis
    by auto (* 8 ms *)
qed
  
(*proof -
  { fix rr :: real
    have ff1: "\<And>r ra. \<not> lgen False ra (cos r) \<or> ra \<le> cos r"
      using lgen_le_neg by auto (* 4 ms *)
    have "\<And>r ra. \<not> lgen False ra (1 - r\<^sup>2 / 2) \<or> lgen False ra (cos r)"
      using cos_lower_bound_0 by auto (* failed *) 
    then have "\<And>r ra. \<not> lgen False ra (1 - r\<^sup>2 / 2) \<or> ra \<le> cos r"
      using ff1 by blast (* 8 ms *)
    then have "\<And>r ra. (1::real) + ra * (ra * (- 1 / 2)) < r \<or> r \<le> cos ra"
      by (auto simp add: metitarski_simps algebra_simps) (* failed *) (*this seems to work*)
    then have ff2: "1 + rr * (rr * (- 1 / 2)) < 0 \<or> 0 \<le> cos rr"
      by blast (* failed *)
    have ff3: "cos rr < 0 \<or> \<bar>cos rr\<bar> = cos rr"
      using abs_nonnegative by auto (* 40 ms *)
    have "1 < cos rr \<or> \<bar>cos rr\<bar> \<noteq> cos rr \<or> \<bar>cos rr\<bar> \<le> 1"
      by auto (* 8 ms *)
    then have ff4: "cos rr < 0 \<or> 1 < cos rr \<or> \<bar>cos rr\<bar> \<le> 1"
      using ff3 by blast (* 0.0 ms *)
    have ff5: "\<And>r ra. \<not> lgen False (cos ra) r \<or> cos ra \<le> r"
      using lgen_le_neg by auto (* 4 ms *)
    have "\<And>r ra. \<not> lgen False (1 - ra\<^sup>2 / 2 + ra ^ 4 / 24) r \<or> lgen False (cos ra) r"
      using cos_upper_bound_0 by auto (* failed *)
    then have "\<And>r ra. \<not> lgen False (1 - ra\<^sup>2 / 2 + ra ^ 4 / 24) r \<or> cos ra \<le> r"
      using ff5 by blast (* 12 ms *)
    then have "\<And>r ra. (ra::real) < 1 + r * (r * (- 1 / 2 + r * (r * (1 / 24)))) \<or> cos r \<le> ra"
      by (simp add: metitarski_simps algebra_simps) (* failed *)
    then have ff6: "1 < 1 + rr * (rr * (- 1 / 2 + rr * (rr * (1 / 24)))) \<or> cos rr \<le> 1"
      by auto (* 8 ms *)
    have ff7: "0 \<le> rr \<or> \<bar>rr\<bar> = - rr"
      using abs_negative by auto (* 0.0 ms *)
    have "- rr < 1 \<or> \<bar>rr\<bar> \<noteq> - rr \<or> 1 \<le> \<bar>rr\<bar>"
      by auto (* 16 ms *)
    then have ff8: "- rr < 1 \<or> 0 \<le> rr \<or> 1 \<le> \<bar>rr\<bar>"
      using ff7 by fastforce (* 0.0 ms *)
    have ff9: "rr < 0 \<or> \<bar>rr\<bar> = rr"
      using abs_nonnegative by auto (* 16 ms *)
    have "rr < 1 \<or> \<bar>rr\<bar> \<noteq> rr \<or> 1 \<le> \<bar>rr\<bar>"
      by auto (* 8 ms *)
    then have ff10: "rr < 0 \<or> rr < 1 \<or> 1 \<le> \<bar>rr\<bar>"
      using ff9 by fastforce (* 0.0 ms *)
    have "\<not> rr * (rr * (1 / 2)) \<le> 1 \<or> \<not> 1 < rr * (rr * (1 / 2))"
      by auto (* 8 ms *)
    moreover
    { assume "\<not> 1 < rr * (rr * (1 / 2))"
      then have "\<not> 1 + rr * (rr * (- 1 / 2)) < 0"
        by (simp add: metitarski_simps algebra_simps) (* 8 ms *)
      then have "\<not> cos rr < 0"
        using ff2 by auto (* 4 ms *)
      then have "rr * (rr * (- 1 / 2 + rr * (rr * (1 / 24)))) \<le> 0 \<longrightarrow> \<not> cos rr < 0 \<and> \<not> 0 < rr * (rr * (- 1 / 2 + rr * (rr * (1 / 24))))"
        by simp (* 8 ms *)
      moreover
      { assume "\<not> cos rr < 0 \<and> \<not> 0 < rr * (rr * (- 1 / 2 + rr * (rr * (1 / 24))))"
        then have "\<not> cos rr < 0 \<and> \<not> 1 < 1 + rr * (rr * (- 1 / 2 + rr * (rr * (1 / 24))))"
          by (simp add: metitarski_simps algebra_simps) (* 12 ms *)
        then have "\<not> cos rr < 0 \<and> \<not> 1 < cos rr"
          using ff6 by fastforce (* 8 ms *)
        then have "\<not> 1 < \<bar>cos rr\<bar>"
          using ff4 by auto (* 4 ms *)
        then have "\<not> \<bar>rr\<bar> < 1 \<or> \<not> 1 < \<bar>cos rr\<bar>"
          by metis (* 44 ms *) }
      moreover
      { assume "\<not> rr * (rr * (- 1 / 2 + rr * (rr * (1 / 24)))) \<le> 0"
        then have "\<not> - 1 < rr \<or> \<not> rr < 1"
          by sos (* 164 ms *) }
      ultimately have "rr < 1 \<and> - 1 < rr \<longrightarrow> \<not> \<bar>rr\<bar> < 1 \<or> \<not> 1 < \<bar>cos rr\<bar>"
        by metis (* 32 ms *) }
    moreover
    { assume "\<not> rr * (rr * (1 / 2)) \<le> 1"
      then have "\<not> - 1 < rr \<or> \<not> rr < 1"
        by sos (* 44 ms *) }
    ultimately have "rr < 1 \<and> - 1 < rr \<longrightarrow> \<not> \<bar>rr\<bar> < 1 \<or> \<not> 1 < \<bar>cos rr\<bar>"
      by metis (* 24 ms *)
    moreover
    { assume "\<not> - 1 < rr"
      then have "\<not> rr < 0 \<and> \<not> - 1 < rr \<or> \<not> - 1 < rr \<and> \<not> 0 \<le> rr"
        by fastforce (* 4 ms *)
      moreover
      { assume "\<not> - 1 < rr \<and> \<not> 0 \<le> rr"
        then have "\<not> - rr < 1 \<and> \<not> 0 \<le> rr"
          by (simp add: metitarski_simps algebra_simps) (* 4 ms *)
        then have "\<not> \<bar>rr\<bar> < 1"
          using ff8 by simp (* 8 ms *) }
      moreover
      { assume "\<not> rr < 0 \<and> \<not> - 1 < rr"
        then have "\<not> rr < 1"
          by sos (* 24 ms *) }
      ultimately have "\<not> \<bar>rr\<bar> < 1 \<or> \<not> rr < 1"
        by metis (* 4 ms *) }
    ultimately have "rr < 1 \<and> \<bar>rr\<bar> < 1 \<longrightarrow> \<not> \<bar>rr\<bar> < 1 \<or> \<not> 1 < \<bar>cos rr\<bar>"
      by metis (* 8 ms *)
    moreover
    { assume aaa1: "\<not> rr < 1"
      have "rr < 1 \<or> 0 \<le> rr"
        by auto (* 4 ms *)
      then have "\<not> rr < 0 \<and> \<not> rr < 1"
        using aaa1 by force (* 0.0 ms *)
      then have "\<not> \<bar>rr\<bar> < 1"
        using ff10 by simp (* 16 ms *) }
    ultimately have "\<bar>rr\<bar> < 1 \<longrightarrow> \<not> \<bar>rr\<bar> < 1 \<or> \<not> 1 < \<bar>cos rr\<bar>"
      by metis (* 4 ms *)
    moreover
    { assume "\<not> \<bar>rr\<bar> < 1"
      then have "\<not> \<bar>rr\<bar> < 1 \<or> \<not> 1 < \<bar>cos rr\<bar>"
        by metis (* 4 ms *) }
    ultimately have "\<not> \<bar>rr\<bar> < 1 \<or> \<not> 1 < \<bar>cos rr\<bar>"
      by metis (* 4 ms *) }
  then have "\<forall>r. \<not> \<bar>r::real\<bar> < 1 \<or> \<not> 1 < \<bar>cos r\<bar>"
    by blast (* 0.0 ms *)
  then show "\<forall>r. \<bar>r::real\<bar> < 1 \<longrightarrow> \<bar>cos r\<bar> \<le> 1"
    by auto (* 12 ms *)
qed
*)  
end  