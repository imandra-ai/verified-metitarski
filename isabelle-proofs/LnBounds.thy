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
      
strategy eq_simp = Dynamic(Auto)      
      
  lemma ln_lower_bound_cf3: "\<not> 0 < X
    \<or> \<not> (lgen R Y ((1/2)*(1+5*X)*(X-1)/(X*(2+X))))
    \<or> (lgen R Y (ln(X)))"
    apply(clarsimp)
    apply(drule ln_lower_3)
    apply(clarsimp simp add: ln_lower_3_def ln_upper_3_def)
    apply(erule lgen.elims)
     apply(clarsimp simp add: field_simps)
     apply(rule order.trans)
      apply(assumption)
     apply(rule ord_eq_le_trans [where ?b = "- ((5 / X + (1 / X - 1) / X - 5) / (2 + 4 / X))"])
      apply(thin_tac "\<not> R")
      apply(thin_tac "- ((5 / X + (1 / X - 1) / X - 5) / (2 + 4 / X)) \<le> ln X")
      apply(thin_tac "Y \<le> (X * (X * 5) - (1 + X * 4)) / (X * 4 + X * (X * 2))")
      apply(simp only: divide_eq_eq eq_minus_divide_eq split: if_splits)
      apply(safe)
       apply(simp add: divide_simps algebra_simps split: if_splits)
        apply(simp only: add_divide_eq_if_simps divide_eq_eq split: if_splits)
      apply algebra
     apply(simp only: add_divide_eq_if_simps)
     apply(split if_splits)
      back
        apply algebra
       apply
      
      apply(rule impE [where ?P = "X \<noteq> 0" and ?Q = "(X * 4 + X * (X * 2) \<noteq> 0 \<longrightarrow>
      (2 * X + 4 \<noteq> 0 \<longrightarrow> (X * (X * 5) - (1 + X * 4)) * ((2 * X + 4) * X) = (5 * (X * X) - (4 * X + 1)) * (X * 4 + X * (X * 2))) \<and>
      (2 * X + 4 = 0 \<longrightarrow> X * (X * 5) = 1 + X * 4)) \<and>
     (X * 4 + X * (X * 2) = 0 \<longrightarrow> 2 * X + 4 \<noteq> 0 \<longrightarrow> 4 * X + 1 = 5 * (X * X))"])

      apply(auto simp add: algebra_simps)+

      apply(force simp add: field_simps)
    apply(auto)  

    done
end
  