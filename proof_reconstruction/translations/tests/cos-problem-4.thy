theory "cos-problem-4"
  imports "../GenerateATP"
begin
  
lemma "\<forall>(X::real).((((0 <= X) \<and> (X <= pi)) --> (cos(X) <= 1)))"
  apply(tactic {*fn st => (writeln (isar_proof st @{context}); Seq.single st) *})
proof -
  { fix rr :: real
    have ff1: "\<And>r ra. \<not> lgen False (cos ra) r \<or> cos ra \<le> r"
      using lgen_le_neg by auto (* 4 ms *)
    have "\<And>r ra. \<not> lgen False (1 - ra\<^sup>2 / 2 + ra ^ 4 / 24) r \<or> lgen False (cos ra) r"
      using cos_upper_bound_0 by auto (* failed *)
    then have "\<And>r ra. \<not> lgen False (1 - ra\<^sup>2 / 2 + ra ^ 4 / 24) r \<or> cos ra \<le> r"
      using ff1 by blast (* 16 ms *)
    then have "\<And>r ra. (ra::real) < 1 + r * (r * (- 1 / 2 + r * (r * (1 / 24)))) \<or> cos r \<le> ra"
      sorry (* failed *)
    then have ff2: "1 < 1 + rr * (rr * (- 1 / 2 + rr * (rr * (1 / 24)))) \<or> cos rr \<le> 1"
      by blast (* 0.0 ms *)
    have "\<not> rr * (rr * (- 1 / 2 + rr * (rr * (1 / 24)))) \<le> 0 \<or> \<not> 0 < rr * (rr * (- 1 / 2 + rr * (rr * (1 / 24))))"
      by force (* 20 ms *)
    moreover
    { assume "\<not> 0 < rr * (rr * (- 1 / 2 + rr * (rr * (1 / 24))))"
      then have "\<not> 1 < 1 + rr * (rr * (- 1 / 2 + rr * (rr * (1 / 24))))"
        sorry (* failed *)
      then have "\<not> 1 < cos rr"
        using ff2 by force (* 88 ms *)
      then have "\<not> 1 < cos rr \<or> \<not> 0 \<le> rr \<or> \<not> rr \<le> pi"
        by metis (* 4 ms *) }
    moreover
    { assume "\<not> rr * (rr * (- 1 / 2 + rr * (rr * (1 / 24)))) \<le> 0"
      then have "\<not> rr \<le> pi \<or> \<not> 0 \<le> rr"
        using pi_lower_bound pi_upper_bound by sos (* failed *)
      moreover
      { assume "\<not> 0 \<le> rr"
        then have "\<not> 1 < cos rr \<or> \<not> 0 \<le> rr \<or> \<not> rr \<le> pi"
          by metis (* 0.0 ms *) }
      moreover
      { assume "\<not> rr \<le> pi"
        then have "\<not> 1 < cos rr \<or> \<not> 0 \<le> rr \<or> \<not> rr \<le> pi"
          by metis (* 0.0 ms *) }
      ultimately have "\<not> 1 < cos rr \<or> \<not> 0 \<le> rr \<or> \<not> rr \<le> pi"
        by metis (* 8 ms *) }
    ultimately have "\<not> 1 < cos rr \<or> \<not> 0 \<le> rr \<or> \<not> rr \<le> pi"
      by metis (* 24 ms *) }
  then have "\<forall>r. \<not> 1 < cos r \<or> \<not> r \<le> pi \<or> \<not> 0 \<le> r"
    by blast (* 4 ms *)
  then show ?thesis
    by auto (* 4 ms *)
qed
  
(*proof -
  { fix rr :: real
    have ff1: "\<And>r ra. \<not> lgen False (cos ra) r \<or> cos ra \<le> r"
      using lgen_le_neg by auto (* 0.0 ms *)
    have "\<And>r ra. \<not> lgen False (1 - ra\<^sup>2 / 2 + ra ^ 4 / 24) r \<or> lgen False (cos ra) r"
      using cos_upper_bound_0 by auto (* failed *)
    then have "\<And>r ra. \<not> lgen False (1 - ra\<^sup>2 / 2 + ra ^ 4 / 24) r \<or> cos ra \<le> r"
      using ff1 by blast (* 4 ms *)
    then have "\<And>r ra. (ra::real) < 1 + r * (r * (- 1 / 2 + r * (r * (1 / 24)))) \<or> cos r \<le> ra"
      by (simp add: metitarski_simps algebra_simps) (* failed *)
    then have ff2: "1 < 1 + rr * (rr * (- 1 / 2 + rr * (rr * (1 / 24)))) \<or> cos rr \<le> 1"
      by blast (* 0.0 ms *)
    have "\<not> rr * (rr * (- 1 / 2 + rr * (rr * (1 / 24)))) \<le> 0 \<or> \<not> 0 < rr * (rr * (- 1 / 2 + rr * (rr * (1 / 24))))"
      by auto (* 4 ms *)
    moreover
    { assume "\<not> 0 < rr * (rr * (- 1 / 2 + rr * (rr * (1 / 24))))"
      then have "\<not> 1 < 1 + rr * (rr * (- 1 / 2 + rr * (rr * (1 / 24))))"
        by (simp add: metitarski_simps algebra_simps) (* 56 ms *)
      then have "\<not> 1 < cos rr"
        using ff2 by fastforce (* 40 ms *)
      then have "\<not> 1 < cos rr \<or> \<not> 0 \<le> rr \<or> \<not> rr \<le> pi"
        by metis (* 4 ms *) }
    moreover
    { assume "\<not> rr * (rr * (- 1 / 2 + rr * (rr * (1 / 24)))) \<le> 0"
      then have "\<not> rr \<le> pi \<or> \<not> 0 \<le> rr"
        using pi_lower_bound pi_upper_bound by sos (* failed *)
      moreover
      { assume "\<not> 0 \<le> rr"
        then have "\<not> 1 < cos rr \<or> \<not> 0 \<le> rr \<or> \<not> rr \<le> pi"
          by metis (* 4 ms *) }
      moreover
      { assume "\<not> rr \<le> pi"
        then have "\<not> 1 < cos rr \<or> \<not> 0 \<le> rr \<or> \<not> rr \<le> pi"
          by metis (* 0.0 ms *) }
      ultimately have "\<not> 1 < cos rr \<or> \<not> 0 \<le> rr \<or> \<not> rr \<le> pi"
        by metis (* 0.0 ms *) }
    ultimately have "\<not> 1 < cos rr \<or> \<not> 0 \<le> rr \<or> \<not> rr \<le> pi"
      by metis (* 8 ms *) }
  then have "\<forall>r. \<not> 1 < cos r \<or> \<not> r \<le> pi \<or> \<not> 0 \<le> r"
    by meson (* 0.0 ms *)
  then show ?thesis
    by auto (* 4 ms *)
qed  
*)
  
end
  