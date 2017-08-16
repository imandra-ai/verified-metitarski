theory AxiomsAbs
  imports Main Real
begin
  
lemma abs_nonnegative:
  "\<not>(0 \<le> (x::real)) \<or> (abs x) = x"
  by auto
    
lemma abs_negative:
  "0 \<le> (x::real) \<or> (abs x) = -x "
  by auto
  
end
  