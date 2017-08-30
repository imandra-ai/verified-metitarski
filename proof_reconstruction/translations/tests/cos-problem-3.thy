theory "cos-problem-3"
  imports "../GenerateATP"
begin
  
lemma "\<forall>(X::real).((Not((1 <= abs(X))) --> (abs(cos(X)) <= 1)))
" 
  apply(tactic {*fn st => (writeln (isar_proof st @{context}); Seq.single st) *})
proof -
  { fix rr :: real
    have "\<not> lgen False X_000012 (1 - X_000011\<^sup>2 / 2) \<or> X_000012 \<le> cos X_000011"
      by (metis cos_lower_bound_0 lgen_le_neg) (* failed *)
    then have ff1: "1 + X_000011 * (X_000011 * (- 1 / 2)) < X_000012 \<or> X_000012 \<le> cos X_000011"
      by (auto simp add: algebra_simps divide_simps metitarski_simps) (* failed *)
    have "1 < cos rr \<or> \<bar>cos rr\<bar> \<noteq> cos rr \<or> \<bar>cos rr\<bar> \<le> 1"
      by auto (* 28 ms *)
    then have ff2: "cos rr < 0 \<or> 1 < cos rr \<or> \<bar>cos rr\<bar> \<le> 1"
      using abs_nonnegative by blast (* 8 ms *)
    have "\<not> lgen False (1 - X_000020\<^sup>2 / 2 + X_000020 ^ 4 / 24) X_000021 \<or> cos X_000020 \<le> X_000021"
      by (metis cos_upper_bound_0 lgen_le_neg) (* failed *)
    then have ff3: "X_000021 < 1 + X_000020 * (X_000020 * (- 1 / 2 + X_000020 * (X_000020 * (1 / 24)))) \<or> cos X_000020 \<le> X_000021"
      by (force simp add: algebra_simps divide_simps metitarski_simps) (* failed *)
    have "- rr < 1 \<or> \<bar>rr\<bar> \<noteq> - rr \<or> 1 \<le> \<bar>rr\<bar>"
      by auto (* 8 ms *)
    then have ff4: "- rr < 1 \<or> 0 \<le> rr \<or> 1 \<le> \<bar>rr\<bar>"
      using abs_negative by blast (* 0.0 ms *)
    have "rr < 1 \<or> \<bar>rr\<bar> \<noteq> rr \<or> 1 \<le> \<bar>rr\<bar>"
      by auto (* 24 ms *)
    then have ff5: "rr < 0 \<or> rr < 1 \<or> 1 \<le> \<bar>rr\<bar>"
      using abs_nonnegative by blast (* 8 ms *)
    have "\<not> rr * (rr * (1 / 2)) \<le> 1 \<or> \<not> 1 < rr * (rr * (1 / 2))"
      by auto (* 8 ms *)
    moreover
    { assume "\<not> 1 < rr * (rr * (1 / 2))"
      then have "\<not> 1 + rr * (rr * (- 1 / 2)) < 0"
        by (simp add: metitarski_simps algebra_simps) (* 8 ms *)
      then have "\<not> cos rr < 0"
        using ff1 by metis (* failed *)
      then have "rr * (rr * (- 1 / 2 + rr * (rr * (1 / 24)))) \<le> 0 \<longrightarrow> \<not> cos rr < 0 \<and> \<not> 0 < rr * (rr * (- 1 / 2 + rr * (rr * (1 / 24))))"
        by auto (* 16 ms *)
      moreover
      { assume "\<not> cos rr < 0 \<and> \<not> 0 < rr * (rr * (- 1 / 2 + rr * (rr * (1 / 24))))"
        then have "\<not> cos rr < 0 \<and> \<not> 1 < 1 + rr * (rr * (- 1 / 2 + rr * (rr * (1 / 24))))"
          by (simp add: metitarski_simps algebra_simps) (* 52 ms *)
        then have "\<not> cos rr < 0 \<and> \<not> 1 < cos rr"
          using ff3 by metis (* failed *)
        then have "\<not> 1 < \<bar>cos rr\<bar>"
          using ff2 by auto (* 4 ms *)
        then have "\<not> \<bar>rr\<bar> < 1 \<or> \<not> 1 < \<bar>cos rr\<bar>"
          by metis (* 20 ms *) }
      moreover
      { assume "\<not> rr * (rr * (- 1 / 2 + rr * (rr * (1 / 24)))) \<le> 0"
        then have "\<not> - 1 < rr \<or> \<not> rr < 1"
          by sos (* 264 ms *) }
      ultimately have "rr < 1 \<and> - 1 < rr \<longrightarrow> \<not> \<bar>rr\<bar> < 1 \<or> \<not> 1 < \<bar>cos rr\<bar>"
        by metis (* 28 ms *) }
    moreover
    { assume "\<not> rr * (rr * (1 / 2)) \<le> 1"
      then have "\<not> - 1 < rr \<or> \<not> rr < 1"
        by sos (* 64 ms *) }
    ultimately have "rr < 1 \<and> - 1 < rr \<longrightarrow> \<not> \<bar>rr\<bar> < 1 \<or> \<not> 1 < \<bar>cos rr\<bar>"
      by metis (* 16 ms *)
    moreover
    { assume "\<not> - 1 < rr"
      then have "\<not> rr < 0 \<and> \<not> - 1 < rr \<or> \<not> - 1 < rr \<and> \<not> 0 \<le> rr"
        by force (* 4 ms *)
      moreover
      { assume "\<not> - 1 < rr \<and> \<not> 0 \<le> rr"
        then have "\<not> - rr < 1 \<and> \<not> 0 \<le> rr"
          by (simp add: metitarski_simps algebra_simps) (* 4 ms *)
        then have "\<not> \<bar>rr\<bar> < 1"
          using ff4 by simp (* 16 ms *) }
      moreover
      { assume "\<not> rr < 0 \<and> \<not> - 1 < rr"
        then have "\<not> rr < 1"
          by sos (* 28 ms *) }
      ultimately have "\<not> \<bar>rr\<bar> < 1 \<or> \<not> rr < 1"
        by metis (* 16 ms *) }
    ultimately have "rr < 1 \<and> \<bar>rr\<bar> < 1 \<longrightarrow> \<not> \<bar>rr\<bar> < 1 \<or> \<not> 1 < \<bar>cos rr\<bar>"
      by metis (* 16 ms *)
    moreover
    { assume aaa1: "\<not> rr < 1"
      have "rr < 1 \<or> 0 \<le> rr"
        by auto (* 8 ms *)
      then have "\<not> rr < 0 \<and> \<not> rr < 1"
        using aaa1 by simp (* 4 ms *)
      then have "\<not> \<bar>rr\<bar> < 1"
        using ff5 by auto (* 16 ms *) }
    ultimately have "\<bar>rr\<bar> < 1 \<longrightarrow> \<not> \<bar>rr\<bar> < 1 \<or> \<not> 1 < \<bar>cos rr\<bar>"
      by metis (* 16 ms *)
    moreover
    { assume "\<not> \<bar>rr\<bar> < 1"
      then have "\<not> \<bar>rr\<bar> < 1 \<or> \<not> 1 < \<bar>cos rr\<bar>"
        by metis (* 4 ms *) }
    ultimately have "\<not> \<bar>rr\<bar> < 1 \<or> \<not> 1 < \<bar>cos rr\<bar>"
      by metis (* 28 ms *) }
  then have "\<forall>r. \<not> \<bar>r::real\<bar> < 1 \<or> \<not> 1 < \<bar>cos r\<bar>"
    by blast (* 0.0 ms *)
  then show "\<forall>r. \<bar>r::real\<bar> < 1 \<longrightarrow> \<bar>cos r\<bar> \<le> 1"
    by auto (* 28 ms *)
qed  
  
end  