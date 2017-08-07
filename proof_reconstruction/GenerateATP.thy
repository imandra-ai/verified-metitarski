theory GenerateATP
  imports Main Real Complex_Main
begin
  
declare[[ML_print_depth=50]]   
  
lemma foo: "\<forall>X Y::real .\<exists> Z. \<not> Z = (sqrt (2::real)) \<and> less_eq 0 (times (minus X 1::real) (minus X 1))"  
  sorry
  
ML\<open>
val theorem = Thm.concl_of @{thm foo};
\<close>  

ML_file "~/Documents/internship/verified-metitarski/proof_reconstruction/atp_problem_of_thm.ML"  
  
ML\<open>
ATP_Problem_of_thm.atp_problem_of_thm @{context} @{thm foo}                                                                    
\<close>
    
end
  