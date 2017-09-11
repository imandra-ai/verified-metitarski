theory LnBounds
  imports Main Real 
    (*Path to the special function bounds afp entry. 
      The method from the afp website for making this a relative path didn't work!*)
    AxiomsGeneral "~~/../Documents/afp/Special_Function_Bounds/Log_CF_Bounds"
    "../../PSL/PSL"
    "~~/src/HOL/Library/Sum_of_Squares"
begin
  
  lemma ln_lower_bound_cf1: "\<not> 0 < x
                   \<or> \<not> (lgen R  y ((x-1)/x))
                   \<or> (lgen R y (ln(x)))"
    using ln_lower_1
    by (metis lgen.elims(2) lgen.elims(3) ln_lower_1_eq not_le order.trans)
      
  lemma ln_upper_bound_cf1: "\<not> 0 < x
                    \<or> \<not> (lgen r  (x - 1) y)
                    \<or> (lgen r (ln(x)) y)"
    using ln_upper_1
    by (metis (full_types) lgen.elims(2) lgen.elims(3) not_le order.trans)

      find_theorems ln_upper_3
      
  lemma ln_upper_bound_cf3: "\<not> 0 < X
    \<or> \<not> (lgen R  ((1/2)*(X+5)*(X-1)/(2*X+1)) Y)
    \<or> (lgen R (ln(X)) Y)"
    apply(clarsimp)
    apply(drule ln_upper_3)
    apply(clarsimp simp add: ln_upper_3_def)
    apply(erule lgen.elims)
    apply(auto)
    done      
      
  lemma ln_lower_bound_cf3: "\<not> 0 < X
    \<or> \<not> (lgen R Y ((1/2)*(1+5*X)*(X-1)/(X*(2+X))))
    \<or> (lgen R Y (ln(X)))"
    using ln_lower_3
    by (metis lgen.elims(2) lgen.elims(3) ln_lower_3_eq not_le order.trans)
end
  