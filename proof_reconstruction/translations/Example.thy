theory Example
  imports Main Real Transcendental "~/Documents/internship/verified-metitarski/isabelle-proofs/AxiomsGeneral"
begin
 
declare[[ML_print_depth=50]]  
  
ML
\<open>@{term "\<And>(X_000043::real) X_000044. X_000044 < - 1 + X_000043"}\<close>

ML
\<open>@{term "\<forall>(X_000043::real) X_000044. X_000044 < - 1 + X_000043"}\<close>  
 

lemma refute_28_lemm: "(- 1 + X_000050) / X_000050 < X_000051 \<or> X_000050 \<le> 0 \<or> X_000051 \<le> ln X_000050"
  sorry    
  
lemma "abs-problem-1": "\<forall>(X::real).(0\<le>X \<longrightarrow> abs(ln(1+X)-X) \<le> X^2)"
proof -
  {fix rr :: real
   have refute_28: "(- 1 + X_000050) / X_000050 < X_000051 \<or> X_000050 \<le> 0 \<or> X_000051 \<le> ln X_000050"
     sorry
   have refute_30_neg: "\<not> (- 1 + (1 + rr)) / (1 + rr) < rr * (1 + rr * - 1) \<and> \<not> 1 + rr \<le> 0 \<and> \<not> rr \<le> ln (1 + rr)"    
     sorry
   then have refute_24_neg: "\<not> ln (1 + rr) < rr * (1 + rr * - 1) \<and> \<not> rr \<le> ln (1 + rr)"
     using refute_28_lemm by fastforce
 }
   then show ?thesis
     sorry
 qed
   
lemma "\<forall>(X::real).(0\<le>X \<longrightarrow> abs(ln(1+X)-X) \<le> X^2)"
proof -
  {
    fix rr :: real
    assume "\<not> 0 < rr * (rr * (rr * - 1)) \<and> \<not> rr \<le> - 1"
    then have "\<not> rr < rr * (1 + rr * - 1) * (1 + rr) \<and> \<not> 1 + rr \<le> 0"
(*    sledgehammer [max_facts = 25, isar_proof] (add: algebra_simps)*)
     by(simp add: algebra_simps)
(*      sledgehammer[max_facts = 25]
      by (smt mult.commute mult.left_commute semiring_normalization_rules(2))*)
(*      by (smt mult.commute mult.left_commute semiring_normalization_rules(2)) ()*)
(*      by (smt mult.assoc mult.commute mult_minus_right semiring_normalization_rules(2)) *)
  }
  then show ?thesis
     sorry
 qed
  
(* Making a custom MT simpset*)   
named_theorems metitarski_simps "arithmetic simplification rules used by Metitarski"
 
declare power2_eq_square[metitarski_simps]    
  
lemma "\<forall>(X::real).(0\<le>X \<longrightarrow> abs(ln(1+X)-X) \<le> X^2)"
proof -
  {
    fix rr :: real
    assume "\<not> rr * rr < \<bar>rr * - 1 + ln (1 + rr)\<bar>"
    then have "\<not> rr\<^sup>2 < \<bar>ln (1 + rr) - rr\<bar>"
      by (force simp add: metitarski_simps)
  }
  then show ?thesis
     sorry
qed  

lemma "1 / 2 * (1 + 5 * (X_000060::real)) * (X_000060 - 1) = - 1 / 2 + X_000060 * (- 2 + X_000060 * (5 / 2))"  
  apply(simp add: algebra_simps divide_simps)
  done
    
  
lemma "True"
proof -
  {
    fix rr :: real
    have "\<And>r ra. \<not> lgen False (1 / 2 * (ra + 5) * (ra - 1) / (2 * ra + 1)) r \<or> ra \<le> 0 \<or> ln ra \<le> r"  
      sorry
    then have "\<And>r ra. (ra::real) < (- 5 / 2 + r * (2 + r * (1 / 2))) / (1 + r * 2) \<or> r \<le> 0 \<or> ln r \<le> ra"
      sledgehammer[isar_proof = true](add: disjE)
  }
  then show ?thesis
     sorry
qed    
  
end