theory CosBounds
  imports Main Real
    AxiomsGeneral
    "~~/../Documents/afp/Special_Function_Bounds/Sin_Cos_Bounds"
    Set_Interval   
begin

  
lemma cos_upper_bound_0:
  "\<not> (lgen R  (1 - (X^2)/2 + (X^4)/24) Y)
    \<or> (lgen R  (cos(X)) Y)"
  apply(clarsimp)
  apply(erule lgen.elims)
   apply(clarsimp)
   apply(insert cospoly_upper [where ?n=1 and ?x=X])
   apply(rule order.trans)
    apply(assumption)
   apply(simp add: cospoly_def)
proof-
  fix X::real
  have "(\<Sum>k<5. cos_coeff k * X ^ k) = 1 - X\<^sup>2 / 2 + X ^ 4 / 24"
    apply(simp add: sum_def cos_coeff_def divide_simps algebra_simps split: if_split)
    apply(subst comm_monoid_set.eq_fold)
     defer
     apply(simp add: Finite_Set.fold_def)
      sorry

    
lemma cos_lower_bound_0:
  "\<not> (lgen R  Y  (1 - (X^2)/2))
    \<or> (lgen R  Y  (cos(X)))"
  sorry    
    
end
  