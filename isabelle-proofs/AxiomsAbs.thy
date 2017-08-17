theory AxiomsAbs
  imports Main Real
begin
  
lemma abs_nonnegative_axiom:
  "\<not>(0 \<le> (x::real)) \<or> (abs x) = x"
  by auto
    
lemma abs_negative_axiom:
  "0 \<le> (x::real) \<or> (abs x) = -x "
  by auto
  
end
  