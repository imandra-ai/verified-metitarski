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
   have refute_0_9: "\<not> (lgen False ((z::real) - 1) (y::real)) \<or> 
                     z \<le> 0 \<or> 
                     (lgen False (ln(z)) y)"
     using ln_upper_1
     by (smt lgen_le_neg_axiom lgen_le_pos_axiom)
    

  (*resolve*)
   have refute_0_10: "\<not> (lgen False ((z::real) - 1) y) \<or>
                      z \<le> 0 \<or>
                      ln(z) \<le> (y::real)"
     using refute_0_9 refute_0_8 by auto     
       
   (*arithmetic*)    
   have refute_0_11: "y < -1 + z \<or> z \<le> 0 \<or> ln(z) \<le> y"
     using refute_0_10 by auto
   
   (*subst*)    
   have refute_0_12: "x * (1 + x) < -1 + (1 + x) \<or>
                      1 + x \<le> 0 \<or>
                      ln(1 + x) \<le> x * (1 + x)"
     using refute_0_11 by (smt ln_le_minus_one)
 
   (*resolve*)
   have refute_0_13: "x * (1 + x) < -1 + (1 +x) \<or>
                      ln(1 + x) < x \<or>
                      1 + x \<le> 0"
     using refute_0_12 refute_0_7 by auto
       
   (*arithmetic*)
   have refute_0_14: "0 < x * (x * -1) \<or> ln(1 + x) < x \<or> x \<le> -1"
     using refute_0_13
     by (smt ln_add_one_self_le_self normalize_0_3 real_minus_mult_self_le refute_0_6)

   (*canonicalize*)
   have refute_0_15: "0 \<le> x"
     using normalize_0_3 by auto
       
   (*decision*)
   have refute_0_16: " x * (x * -1) \<le> 0 \<or> x \<le> -1"  
     using refute_0_15 by sos
       
   (*resolve*)
   have refute_0_17: "ln(1 + x) < x \<or> x \<le> -1"
     using refute_0_16 refute_0_14 by auto
       
   (*resolve*)
   have refute_0_18: "-1 < x"
     using refute_0_15 by sos
   
   (*resolve*)
   have refute_0_19: "ln(1 + x) < x"
     using refute_0_17 refute_0_18 by auto
       
   (*subst*)
   have refute_0_20: "0 \<le> x * -1 + ln(1 + x) \<or>
                      abs(x * -1 + ln(1 + x)) = -(x * -1 + ln(1 + x))"    
     using abs_negative_axiom by auto
       
   (*tautology*)
   have refute_0_21: "x * x < -(x * -1 + ln(1 + x)) \<or>
                     abs(x * -1 + ln(1 + x)) \<noteq> -(x * -1 + ln(1 + x)) \<or>
                     abs(x * -1 + ln(1 + x)) \<le> x * x"
     by auto
      
   (*resolve*)
   have refute_0_22: "x * x < -(x * -1 + ln(1 + x)) \<or>
                      0 \<le> x * -1 + ln(1 + x) \<or>
                      abs(x * -1 + ln(1 + x)) \<le> x * x"
     using refute_0_20 refute_0_21 by auto
       
   (*resolve*)
   have refute_0_23: "x * x < -(x * -1 + ln(1 + x)) \<or>
                      0 \<le> x * -1 + ln(1 + x)"
     using refute_0_22 refute_0_2 by auto
       
   (*arithmetic*)
   have refute_0_24: "ln(1 + x) < x * (1 + x * -1) \<or>
                      x \<le> ln(1 + x)"
     using refute_0_23
     by (smt distrib_left mult_cancel_left2)
       
   (*subst*)
   have refute_0_25: "\<not> (lgen False q (ln(p))) \<or> q \<le> ln(p)"
     using lgen_le_neg_axiom by auto
       
   (*subst*)
   have refute_0_26: "\<not> (lgen False q ((p - 1)/p)) \<or> 
                      p \<le> 0 \<or>
                      (lgen False q (ln(p)))"
     using ln_lower_1 sledgehammer
     by (smt divide_minus_left lgen_le_neg_axiom lgen_le_pos_axiom ln_diff_le ln_one)  
     
   then show False
qed      
  
end
  