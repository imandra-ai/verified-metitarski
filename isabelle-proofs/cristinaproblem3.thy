theory cristinaproblem3
  imports AxiomsGeneral AxiomsAbs "~~/src/HOL/Library/Sum_of_Squares"
begin
  
lemma "(x::real)+y \<le> abs (x+y)"
proof(rule ccontr)
  assume hypothesis: "\<not> (x::real)+y \<le> abs (x+y)"
  
  (*tautology*)  
  have refute_0_2: "-(x + y) < x + y \<or>
                    abs(x + y) \<noteq> -(x + y) \<or>
                    x + y \<le> abs(x + y)"
    by auto

  (*resolve*)    
  have refute_0_3: "-(x + y) < x + y \<or> 
                    0 \<le> x + y \<or> 
                    x + y \<le> abs(x + y)"
    using refute_0_2 abs_negative_axiom by auto    
 
  (*resolve*)    
  have refute_0_4: "-(x + y) < x + y \<or> 0 \<le> x + y"
    using refute_0_3 hypothesis by auto    
 
  (*arithmetic*)
  have refute_0_5: "x * -1 < y \<or> x * -1 \<le> y"
    using refute_0_4 by auto
      
  (*tautology*)    
  have refute_0_7: "x + y < x + y \<or>
                   abs(x + y) \<noteq> x + y \<or>
                   x + y \<le> abs(x + y)" 
    by auto
 
  (*resolve*)    
  have refute_0_8: "x + y < 0 \<or>
                    x + y < x + y \<or>
                    x + y \<le> abs(x + y)"
    using refute_0_7 abs_nonnegative_axiom by auto    
    
  (*resolve*)   
  have refute_0_9: "x + y < 0 \<or>
                    x + y < x + y"
    using refute_0_8 hypothesis by auto 
      
  (*arithmetic*)
  have refute_0_10: "y < x * -1"
    using refute_0_9 by auto
      
  (*decision*)
  have refute_0_11: "x * -1 \<le> y \<or> y \<le> x * -1"
    using refute_0_10 by sos
      
  (*resolve*)
  have refute_0_12: "x * -1 \<le> y"
    using refute_0_11 refute_0_5 by auto    
      
  then show False
    using refute_0_12 refute_0_10 by auto
qed      
  
end
  