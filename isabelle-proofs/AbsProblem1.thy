theory AbsProblem1
  imports AxiomsGeneral AxiomsAbs LnBounds 
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
    using leq_right_divide_mul_pos_axiom by (simp add: not_le)
  
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
     using ln_add_one_self_le_self negate_0_0 by fastforce
  
   (*subst*)
   have refute_0_8: "\<not> (lgen False (ln(z::real)) (y::real)) \<or> ln(z) \<le> y"    
     using lgen_le_neg_axiom by auto
       
   (*subst*)
   have refute_0_9: "\<not> (lgen False ((z::real) - 1) (y::real)) \<or> 
                     z \<le> 0 \<or> 
                     (lgen False (ln(z)) y)"
     using ln_upper1
     using  not_le by blast    

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
     using refute_0_11 
     by (metis distrib_left le_add_same_cancel1 le_less_trans ln_add_one_self_le_self mult.right_neutral mult_minus_right mult_zero_left negate_0_0 not_less real_minus_mult_self_le)
    
 
   (*resolve*)
   have refute_0_13: "x * (1 + x) < -1 + (1 +x) \<or>
                      ln(1 + x) < x \<or>
                      1 + x \<le> 0"
     using refute_0_12 refute_0_7 by auto
       
   (*arithmetic*)
   have refute_0_14: "0 < x * (x * -1) \<or> ln(1 + x) < x \<or> x \<le> -1"
     using refute_0_13
     using less_eq_real_def negate_0_0 by auto

   (*canonicalize*)
   have refute_0_15: "0 \<le> x"
     using normalize_0_3 by auto
       
   (*decision*)
   have refute_0_16: " x * (x * -1) \<le> 0 \<or> x \<le> -1"  
     using refute_0_15 
   by (sos "((((A<0 * A<1) * R<1) + ((A<0 * R<1) * (R<1 * [x]^2))))")
       
   (*resolve*)
   have refute_0_17: "ln(1 + x) < x \<or> x \<le> -1"
     using refute_0_16 refute_0_14 by auto
       
   (*resolve*)
   have refute_0_18: "-1 < x"
     using refute_0_15
     by (sos "((R<1 + (((A<=1 * R<1) * (R<1 * [1]^2)) + ((A<=0 * R<1) * (R<1 * [1]^2)))))")
   
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
         proof -
           have "x * x < \<bar>- x + ln (x + 1)\<bar>"
             by (metis add.commute add_uminus_conv_diff power2_eq_square refute_0_1)
           then have "ln (x + 1) < x + x * - x"
             by (simp add: abs_if add.commute refute_0_19)
           then show ?thesis
             by (metis add.commute distrib_left mult.right_neutral mult_minus_right)
         qed    
       
   (*subst*)
   have refute_0_25: "\<not> (lgen False q (ln(p))) \<or> q \<le> ln(p)"
     using lgen_le_neg_axiom by auto
   
       
   (*subst*)
   have refute_0_26: "\<not> (lgen False (q::real) (((p::real) - 1)/p)) \<or> 
                      p \<le> 0 \<or>
                      (lgen False q (ln(p)))"
     using ln_lower1
     using not_le by blast
       
   (*resolve*)
   have refute_0_27: "\<not> (lgen False q ((p - 1) / p)) \<or> 
                      p \<le> 0 \<or>
                      q \<le> ln(p)"
     using refute_0_26 refute_0_25 by auto
       
   (*arithmetic*)
   have refute_0_28: "(-1 + p) / p < q \<or> 
                      p \<le> 0 \<or>
                      q \<le> ln(p)"
     using refute_0_27 by (simp add: not_le)
       
   (*subst*)
   have refute_0_29: "(-1 + (1 + x)) / (1 + x) < x * (1 + x * -1) \<or>
                      x * (1 + x * -1) \<le> ln(1 + x) \<or>
                      1 + x \<le> 0"
     using refute_0_28
     by (metis add.commute add_uminus_conv_diff le_less_trans ln_lower_1 ln_lower_1_eq not_le)
     
   (*resolve*)
   have refute_0_30: "(-1 + (1 + x)) / (1 + x) < x * (1 + x * -1) \<or>
                      1 + x \<le> 0 \<or>
                      x \<le> ln(1 + x)"
     using refute_0_29 refute_0_24 by auto
       
   (*arithmetic*)
   have refute_0_31: "x / (1 + x) < x * (1 + x * -1) \<or>
                      x \<le> -1 \<or>
                      x \<le> ln(1 + x)"
     using refute_0_30 by auto
       
   (*resolve*)
   have refute_0_32: "x / (1 + x) < x * (1 + x * -1) \<or>
                      x \<le> ln(1 + x)"
     using refute_0_31 refute_0_18 by auto
       
   (*resolve*)
   have refute_0_33: "x / (1 + x) < x * (1 + x * -1)"
     using refute_0_32 refute_0_19 by auto
       
   (*resolve*)
   have refute_0_34: "x < x * (1 + x * -1) * (1 + x) \<or> 
                      1 + x \<le> 0"
     using refute_0_0 refute_0_33 by auto
       
   (*arithmetic*)
   have refute_0_35: "0 < x * (x * (x * -1)) \<or> 
                      x \<le> -1"
     using refute_0_34
       proof -
         have f1: "ln (x + 1) < x"
           by (simp add: add.commute refute_0_19)
         have f2: "x * x < \<bar>- x + ln (x + 1)\<bar>"
           by (metis add.commute mult_minus1_right refute_0_2)
         have "0 \<le> ln (x + 1)"
        using refute_0_15 by force
      then have "x * x < x"
        using f2 f1 by linarith
      then show ?thesis
        using abs_ln_one_plus_x_minus_x_bound_nonneg less_eq_real_def negate_0_0 by auto
    qed

   (*subst*)
    have refute_0_36: "x < x * (1 + x) \<or> 
                      1 + x \<le> 0 \<or>
                      x \<le> x / (1 + x)"
      using leq_right_divide_mul_pos_axiom
      using not_le by blast
        
   (*subst*)
    have refute_0_37: "(-1 + (1 + x)) / (1 + x) < x \<or> 
                       1 + x \<le> 0 \<or>
                       x \<le> ln(1 + x)"
      using refute_0_28
        proof -
          have "1 / (1 + x) < 1 \<longrightarrow> x / (1 + x) < x \<or> (\<exists>r. \<not> x * r < x \<and> r < 1)"
            by (metis (no_types) mult.right_neutral times_divide_eq_right)
          then have "x / (1 + x) < x \<or> (- 1 + (1 + x)) / (1 + x) < x \<or> 1 + x \<le> 0 \<or> x \<le> ln (1 + x)"
            using refute_0_15 by force
          then show ?thesis
        by simp
    qed
      
   (*resolve*)
   have refute_0_38: "(-1 + (1 + x)) / (1 + x) < x \<or> 
                       1 + x \<le> 0"   
      using refute_0_37 refute_0_19 by auto
        
   (*arithmetic*)
   have refute_0_39: "x / (1 + x) < x \<or> 
                      x \<le> -1"
     using refute_0_38 by auto
       
   (*resolve*)
   have refute_0_40: "x / (1 + x) < x"
     using refute_0_39 refute_0_18 by auto
       
   (*resolve*)
   have refute_0_41: "x < x * (1 + x) \<or> 
                      1 + x \<le> 0"
     using refute_0_36 refute_0_40 by auto
       
   (*arithmetic*) 
   have refute_0_42: "0 < x * x \<or> x \<le> -1"
     using refute_0_41
     using less_eq_real_def by auto
   
   (*decision*)   
   have refute_0_43: "0 < x * x \<or> -1 < x"
     using refute_0_15
     by (sos "((R<1 + (((A<=1 * R<1) * (R<1 * [1]^2)) + ((A<=0 * R<1) * (R<1 * [1]^2)))))")
      
   (*resolve*)
   have refute_0_44: "0 < x * x"
     using refute_0_42 refute_0_43 by auto
       
   (*decision*)
   have refute_0_45: "x * (x * (x * -1)) \<le> 0 \<or> 
                      x \<le> -1"
     using refute_0_44 refute_0_15
     by (sos "((((A<0 * (A<1 * A<2)) * R<1) + ((A<=0 * (A<1 * R<1)) * (R<1 * [x^2]^2))))")
     
   (*resolve*)
   have refute_0_46: "x \<le> -1"
     using refute_0_45 refute_0_35 by auto
   
   (*resolve*)    
   then show False
     using refute_0_45 refute_0_18 by auto
qed      
  
end
  