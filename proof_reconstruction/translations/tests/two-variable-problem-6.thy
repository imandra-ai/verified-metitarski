theory "two-variable-problem-6"
  imports "../GenerateATP"
    "~/Documents/internship/verified-metitarski/isabelle-proofs/ExpBounds"
begin
  
(*MT hangs on two-variable-problem-3 with my default options.*)  
lemma "\<forall>(X::real).(\<forall>(Y::real).((Not((Y <= X)) --> Not(((1 / (1 + exp(X))) <= (1 / (1 + exp(Y))))))))"
  apply(tactic {*fn st => (writeln (isar_proof st [] @{context}); Seq.single st) *})
proof -
  { fix rr :: real and rra :: real
    have ff1: "\<And>r ra. ra < exp r \<or> \<not> lgen True ra (exp r)"
      using lgen_less_neg by blast (* 0.0 ms *)
    have "\<And>r ra. 0 < ra \<or> lgen True ra (exp r)"
      using exp_positive by blast (* 0.0 ms *)
    then have ff2: "\<And>r ra. (0::real) < ra \<or> ra < exp r"
      using ff1 by simp (* 0.0 ms *)
    then have ff3: "(0::real) < - 1 \<or> - 1 < exp rr"
      by blast (* 0.0 ms *)
    have ff4: "(0::real) < - 1 \<or> - 1 < exp rra"
      using ff2 by blast (* 0.0 ms *)
    have ff5: "exp rr < exp rra \<or> rra \<le> rr"
      using exp_monotone2 by blast (* 0.0 ms *)
    have ff6: "1 / (1 + exp rra) < 1 / (1 + exp rr) \<or> 1 / (1 + exp rr) * (1 + exp rra) \<le> 1 \<or> 1 + exp rra \<le> 0"
      using leq_left_mul_divide_pos by blast (* 8 ms *)
    have ff7: "1 < (1 + exp rra) / (1 + exp rr) \<or> 1 + exp rr \<le> 0 \<or> 1 + exp rra \<le> 1 * (1 + exp rr)"
      using leq_right_mul_divide_pos by blast (* 0.0 ms *)
    have "\<not> (0::real) < - 1"
      by mt_arith_rule (* failed *)
    then have "\<not> exp rr \<le> - 1"
      using ff3 by auto (* 4 ms *)
    then have "\<not> (0::real) < - 1 \<and> \<not> exp rr \<le> - 1"
      by mt_arith_rule (* failed *)
    then have "\<not> exp rr \<le> - 1 \<and> \<not> exp rra \<le> - 1"
      using ff4 by auto (* 8 ms *)
    then have "rr < rra \<longrightarrow> \<not> exp rr \<le> - 1 \<and> \<not> exp rra \<le> - 1 \<and> \<not> rra \<le> rr"
      by auto (* 12 ms *)
    moreover
    { assume "\<not> exp rr \<le> - 1 \<and> \<not> exp rra \<le> - 1 \<and> \<not> rra \<le> rr"
      then have "\<not> exp rr \<le> - 1 \<and> \<not> exp rra \<le> - 1 \<and> \<not> exp rra \<le> exp rr"
        using ff5 by fastforce (* 0.0 ms *)
      then have "\<not> 1 + exp rr \<le> 0 \<and> \<not> 1 + exp rra \<le> 1 * (1 + exp rr) \<and> \<not> exp rra \<le> - 1"
        by mt_arith_rule (* failed *)
      then have "\<not> (1 + exp rra) / (1 + exp rr) \<le> 1 \<and> \<not> exp rra \<le> - 1"
        using ff7 by auto (* 8 ms *)
      then have "\<not> 1 / (1 + exp rr) * (1 + exp rra) \<le> 1 \<and> \<not> 1 + exp rra \<le> 0"
        by mt_arith_rule (* failed *)
      then have "\<not> 1 / (1 + exp rr) \<le> 1 / (1 + exp rra)"
        using ff6 by simp (* 24 ms *)
      then have "\<not> rr < rra \<or> \<not> 1 / (1 + exp rr) \<le> 1 / (1 + exp rra)"
        by metis (* 4 ms *) }
    moreover
    { assume "\<not> rr < rra"
      then have "\<not> rr < rra \<or> \<not> 1 / (1 + exp rr) \<le> 1 / (1 + exp rra)"
        by metis (* 4 ms *) }
    ultimately have "\<not> rr < rra \<or> \<not> 1 / (1 + exp rr) \<le> 1 / (1 + exp rra)"
      by metis (* 16 ms *) }
  then have "\<forall>r ra. \<not> (r::real) < ra \<or> \<not> 1 / (1 + exp r) \<le> 1 / (1 + exp ra)"
    by blast (* 0.0 ms *)
  then show ?thesis
    by auto (* 0.0 ms *)
qed
  
end
  