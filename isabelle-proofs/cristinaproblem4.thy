theory cristinaproblem4
  imports Main Real
begin    

lemma cristinaproblem4:
  "2 \<le> (x::real) \<longrightarrow> 0 \<le> (x-2)*x"
proof(rule ccontr)
  assume "\<not>( 2 \<le> (x::real) \<longrightarrow> 0 \<le> (x-2)*x )"
  then show False
    
    have "\<exists>y. 2\<le>y \<and> 0>(y-2)*y "
  
    
end