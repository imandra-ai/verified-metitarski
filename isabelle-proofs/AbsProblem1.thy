theory AbsProblem1
  imports AxiomsGeneral AxiomsAbs "~~/../Documents/afp/Special_Function_Bounds/Log_CF_Bounds" 
          "~~/src/HOL/Library/Sum_of_Squares"
begin
  
lemma abs_problem_1: 
  "0 \<le> (x::real) \<longrightarrow> abs(ln(1 + x) - x) \<le> x ^ 2"
  
proof(rule ccontr)
  assume negate_0_0: "\<not> (0 \<le> x \<longrightarrow> abs(ln(1 + x) - x) \<le> x ^ 2)"
    
  (*conjunct*)  
  have normalize_0_2: "x ^ 2 < abs(ln(1 + x) - x)"
    using negate_0_0 by auto
      
  (*conjunct*)
  have normalize_0_3: "0 \<le> x"    
    using negate_0_0 by auto
      
  (*subst*)
  have refute_0_0: "x < x * (1 + x * -1) * (1 + x) \<or>
                    x * (1 + x * -1) \<le> x / (1 + x) \<or>
                    1 + x \<le> 0"
    using leq_right_divide_mul_pos_axiom by smt
  
  (*canonicalize*)
  have refute_0_1: "x ^ 2 < abs(ln(1 + x) - x)"
    using normalize_0_2 by auto
      
  (*arithmetic*)
  have refute_0_2: "(x * x) < abs(x * -1 + ln(1 + x))"
    using refute_0_1 by (simp add: power2_eq_square)
      
  (*subst*)    
  have refute_0_3: "(x * -1 + ln(1 + x) < 0 \<or>
                    abs(x * -1 + ln(1 + x)) = x * -1 + ln(1 + x))"
    using abs_nonnegative_axiom by auto    
    
  (*tautology*)
  have refute_0_4: "x * x < x * -1 + ln(1 + x) \<or>
                   abs(x * -1 + ln(1 + x)) \<noteq> x * -1 + ln(1 + x) \<or>
                   abs(x * -1 + ln(1 + x)) \<le> x * x"
    by auto
      
  (*resolve*)
  have refute_0_5: "x * -1 + ln(1 + x) < 0 \<or>
                    x * x < x * -1 + ln(1 + x) \<or>
                    abs(x * -1 + ln(1 + x)) \<le> x * x"
    using refute_0_3 refute_0_4 by auto
      
   (*resolve*)
   have refute_0_6: "x * -1 + ln(1 + x) < 0 \<or>
                     x * x < x * -1 + ln(1 + x)"
     using refute_0_5 refute_0_2 by auto
       
   (*arithmetic*)
   have refute_0_7: "x * (1 + x) < ln(1 + x) \<or> ln(1 + x) < x"    
     using refute_0_6
     by (smt abs_ln_one_plus_x_minus_x_bound_nonneg less_1_mult ln_less_self negate_0_0)
  
   (*subst*)
   have refute_0_8: "\<not> (lgen False (ln(z::real)) (y::real)) \<or> ln(z) \<le> y"    
     using lgen_le_neg_axiom by auto
       
   (*subst*)
   have refute_0_9: "\<not> (lgen False (z - 1) y) \<or> 
                     y \<le> 0 \<or> 
                     (lgen False (ln(z)) y)"
     using ln_upper_1
     by (smt abs_ln_one_plus_x_minus_x_bound_nonneg divide_self_if leq_right_divide_mul_pos_axiom ln_gt_zero negate_0_0 power2_eq_square)
     
  then show False
qed      
  
end
  