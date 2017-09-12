theory CosBounds
  imports Main Real
    AxiomsGeneral
    "~~/../Documents/afp/Special_Function_Bounds/Sin_Cos_Bounds"
begin
  
lemma cos_upper_bound_0:
  "\<not> (lgen R  (1 - (X^2)/2 + (X^4)/24) Y)
    \<or> (lgen R  (cos(X)) Y)"
  sorry
    
(*  apply(clarsimp)
  apply(erule lgen.elims)
   apply(clarsimp)
   apply(insert cospoly_upper [where ?n=1 and ?x=X])
   apply(simp add: cospoly_def sum_def)
   apply(rule order.trans)
    apply(assumption)
    apply(assumption)
    
   apply() 
   (* apply(metis cospoly_upper cospoly_def order_trans not_le)*)
   (* sledgehammer[max_facts = 25](add: cospoly_upper)*)
*)
    
lemma cos_lower_bound_0:
  "\<not> (lgen R  Y  (1 - (X^2)/2))
    \<or> (lgen R  Y  (cos(X)))"
  sorry    
    
end
  