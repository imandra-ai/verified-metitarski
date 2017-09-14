theory ExpBounds
  imports Main Real Transcendental
    AxiomsGeneral
    "~~/../Documents/afp/Special_Function_Bounds/Log_CF_Bounds"
begin
  
lemma "exp_monotone2": "\<not> (X::real) \<le> Y \<or> exp X \<le> exp Y"
  by auto
    
find_theorems "lgen"    
    
lemma "exp_positive": "\<not> Y <= 0
    | (lgen R Y (exp X))"
proof -
  consider (a) R | (b) "\<not>R"
    by auto
  then show ?thesis      
    proof cases
      case a thm \<open>R\<close>
      then show ?thesis    
        apply(clarsimp)
          by (meson dual_order.order_iff_strict exp_ge_zero exp_not_eq_zero le_less_trans)
    next
      case b thm \<open>\<not> R\<close>
      then show ?thesis 
        apply(clarsimp)
          using exp_ge_zero order_trans by blast
    qed
qed    
  
end
  