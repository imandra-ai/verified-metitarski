theory cristinaproblem4
  imports "~~/src/HOL/Library/Sum_of_Squares" AxiomsGeneral
begin    

lemma cristinaproblem4:
  "2 \<le> (x::real) \<longrightarrow> 0 \<le> (x-2)*x"
proof(rule ccontr)
  assume "\<not>( 2 \<le> (x::real) \<longrightarrow> 0 \<le> (x-2)*x )"
  then show False
    by (sos "(((A<0 * R<1) + ((R<1 * (R<4 * [~1/2*x + 1]^2)) + ((A<=0 * R<1) * (R<2 * [1]^2)))))")
qed
end