theory "cos-problem-3"
  imports "../GenerateATP"
begin
  
lemma "\<forall>(X::real).((Not((1 <= abs(X))) --> (abs(cos(X)) <= 1)))
" 
  apply(tactic {*fn st => (writeln (isar_proof st @{context}); Seq.single st) *})
proof -
  { fix rr :: real
    have "\<And>r ra. \<not> lgen False ra (1 - r\<^sup>2 / 2) \<or> ra \<le> cos r"
      sorry (*by (metis cos_lower_bound_0 lgen_le_neg)*) (* failed *)
    then have ff1: "\<And>r ra. (1::real) + ra * (ra * (- 1 / 2)) < r \<or> r \<le> cos ra"
      by (auto simp add: metitarski_simps algebra_simps ) (* failed *) (*this seems to work*)
    have "1 < cos rr \<or> \<bar>cos rr\<bar> \<noteq> cos rr \<or> \<bar>cos rr\<bar> \<le> 1"
      by auto (* 8 ms *)
    then have ff2: "cos rr < 0 \<or> 1 < cos rr \<or> \<bar>cos rr\<bar> \<le> 1"
      using abs_nonnegative by blast (* 8 ms *)
    have "\<And>r ra. \<not> lgen False (1 - ra\<^sup>2 / 2 + ra ^ 4 / 24) r \<or> cos ra \<le> r"
      sorry (*by (metis cos_upper_bound_0 lgen_le_neg)*) (* failed *)
    then have ff3: "\<And>r ra. (ra::real) < 1 + r * (r * (- 1 / 2 + r * (r * (1 / 24)))) \<or> cos r \<le> ra"
      by (auto simp add: metitarski_simps field_simps) (* failed *)
    have "- rr < 1 \<or> \<bar>rr\<bar> \<noteq> - rr \<or> 1 \<le> \<bar>rr\<bar>"
      by auto (* 16 ms *)
    then have ff4: "- rr < 1 \<or> 0 \<le> rr \<or> 1 \<le> \<bar>rr\<bar>"
      using abs_negative by blast (* 0.0 ms *)
    have "rr < 1 \<or> \<bar>rr\<bar> \<noteq> rr \<or> 1 \<le> \<bar>rr\<bar>"
      by auto (* 8 ms *)
    then have ff5: "rr < 0 \<or> rr < 1 \<or> 1 \<le> \<bar>rr\<bar>"
      using abs_nonnegative by blast (* 4 ms *)
    have "\<not> rr * (rr * (1 / 2)) \<le> 1 \<or> \<not> 1 < rr * (rr * (1 / 2))"
      by auto (* 8 ms *)
    moreover
    { assume "\<not> 1 < rr * (rr * (1 / 2))"
      then have "\<not> 1 + rr * (rr * (- 1 / 2)) < 0"
        by (simp add: metitarski_simps algebra_simps) (* 8 ms *)
      then have "\<not> cos rr < 0"
        using ff1 by fastforce (* 404 ms *)
      then have "rr * (rr * (- 1 / 2 + rr * (rr * (1 / 24)))) \<le> 0 \<longrightarrow> \<not> cos rr < 0 \<and> \<not> 0 < rr * (rr * (- 1 / 2 + rr * (rr * (1 / 24))))"
        by simp (* 8 ms *)
      moreover
      { assume "\<not> cos rr < 0 \<and> \<not> 0 < rr * (rr * (- 1 / 2 + rr * (rr * (1 / 24))))"
        then have "\<not> cos rr < 0 \<and> \<not> 1 < 1 + rr * (rr * (- 1 / 2 + rr * (rr * (1 / 24))))"
          by (simp add: metitarski_simps algebra_simps) (* 40 ms *)
        then have "\<not> cos rr < 0 \<and> \<not> 1 < cos rr"
          using ff3 by fastforce (* 1.5 s *)
        then have "\<not> 1 < \<bar>cos rr\<bar>"
          using ff2 by simp (* 4 ms *)
        then have "\<not> \<bar>rr\<bar> < 1 \<or> \<not> 1 < \<bar>cos rr\<bar>"
          by metis (* 0.0 ms *) }
      moreover
      { assume "\<not> rr * (rr * (- 1 / 2 + rr * (rr * (1 / 24)))) \<le> 0"
        then have "\<not> - 1 < rr \<or> \<not> rr < 1"
          by sos (* 196 ms *) }
      ultimately have "rr < 1 \<and> - 1 < rr \<longrightarrow> \<not> \<bar>rr\<bar> < 1 \<or> \<not> 1 < \<bar>cos rr\<bar>"
        by metis (* 12 ms *) }
    moreover
    { assume "\<not> rr * (rr * (1 / 2)) \<le> 1"
      then have "\<not> - 1 < rr \<or> \<not> rr < 1"
        by sos (* 48 ms *) }
    ultimately have "rr < 1 \<and> - 1 < rr \<longrightarrow> \<not> \<bar>rr\<bar> < 1 \<or> \<not> 1 < \<bar>cos rr\<bar>"
      by metis (* 8 ms *)
    moreover
    { assume "\<not> - 1 < rr"
      then have "\<not> rr < 0 \<and> \<not> - 1 < rr \<or> \<not> - 1 < rr \<and> \<not> 0 \<le> rr"
        by auto (* 4 ms *)
      moreover
      { assume "\<not> - 1 < rr \<and> \<not> 0 \<le> rr"
        then have "\<not> - rr < 1 \<and> \<not> 0 \<le> rr"
          by (simp add: metitarski_simps algebra_simps) (* 0.0 ms *)
        then have "\<not> \<bar>rr\<bar> < 1"
          using ff4 by auto (* 8 ms *) }
      moreover
      { assume "\<not> rr < 0 \<and> \<not> - 1 < rr"
        then have "\<not> rr < 1"
          by sos (* 8 ms *) }
      ultimately have "\<not> \<bar>rr\<bar> < 1 \<or> \<not> rr < 1"
        by metis (* 4 ms *) }
    ultimately have "rr < 1 \<and> \<bar>rr\<bar> < 1 \<longrightarrow> \<not> \<bar>rr\<bar> < 1 \<or> \<not> 1 < \<bar>cos rr\<bar>"
      by metis (* 8 ms *)
    moreover
    { assume aaa1: "\<not> rr < 1"
      have "rr < 1 \<or> 0 \<le> rr"
        by auto (* 4 ms *)
      then have "\<not> rr < 0 \<and> \<not> rr < 1"
        using aaa1 by fastforce (* 4 ms *)
      then have "\<not> \<bar>rr\<bar> < 1"
        using ff5 by auto (* 4 ms *) }
    ultimately have "\<bar>rr\<bar> < 1 \<longrightarrow> \<not> \<bar>rr\<bar> < 1 \<or> \<not> 1 < \<bar>cos rr\<bar>"
      by metis (* 8 ms *)
    moreover
    { assume "\<not> \<bar>rr\<bar> < 1"
      then have "\<not> \<bar>rr\<bar> < 1 \<or> \<not> 1 < \<bar>cos rr\<bar>"
        by metis (* 4 ms *) }
    ultimately have "\<not> \<bar>rr\<bar> < 1 \<or> \<not> 1 < \<bar>cos rr\<bar>"
      by metis (* 8 ms *) }
  then have "\<forall>r. \<not> \<bar>r::real\<bar> < 1 \<or> \<not> 1 < \<bar>cos r\<bar>"
    by blast (* 4 ms *)
  then show ?thesis
    by auto (* 20 ms *)
qed
  
end  