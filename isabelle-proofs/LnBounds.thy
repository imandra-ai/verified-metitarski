theory LnBounds
  imports Main Real 
    (*Path to the special function bounds afp entry. 
      The method from the afp website for making this a relative path didn't work!*)
    AxiomsGeneral "~~/../Documents/afp/Special_Function_Bounds/Log_CF_Bounds"
begin
  
  lemma ln_lower1: "\<not> 0 < x
                   \<or> \<not> (lgen R  y ((x-1)/x))
                   \<or> (lgen R y (ln(x)))"
    using ln_lower_1
    by (metis lgen.elims(2) lgen.elims(3) ln_lower_1_eq not_le order.trans)
      
  lemma ln_upper1: "\<not> 0 < x
                    \<or> \<not> (lgen r  (x - 1) y)
                    \<or> (lgen r (ln(x)) y)"
    using ln_upper_1
    by (metis (full_types) lgen.elims(2) lgen.elims(3) not_le order.trans)   
end
  