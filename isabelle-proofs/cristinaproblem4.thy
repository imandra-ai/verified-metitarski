theory cristinaproblem4
  imports Main Real "~~/src/HOL/Library/Sum_of_Squares" AxiomsGeneral
begin    

lemma cristinaproblem4:
  "2 \<le> (x::real) \<longrightarrow> 0 \<le> (x-2)*x"
proof(rule ccontr)
  assume "\<not>( 2 \<le> (x::real) \<longrightarrow> 0 \<le> (x-2)*x )"
  then show False
    by sos
qed
end