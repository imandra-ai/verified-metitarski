theory GenerateATP
  imports Main Real Complex_Main
begin
  
declare[[ML_print_depth=50]]   
  
(*For the cube root use "root 3"*)  
lemma foo: "\<forall>X Y::real .\<forall> Z::real. Z \<noteq> (tan 5.3) \<longrightarrow> greater pi (times ( minus (abs X) 1::real) (minus X 1))"  
(*apply(atomize)*)
  sorry
 
ML\<open>
val theorem = Thm.concl_of @{thm foo};
\<close>  

ML_file "~/Documents/internship/verified-metitarski/proof_reconstruction/atp_problem_of_thm.ML"  
ML_file "~/Documents/internship/verified-metitarski/proof_reconstruction/atp_problem_to_tptp.ML"

  
ML\<open>
val atp_problem = ATP_Problem_of_thm.atp_problem_of_thm @{context} @{thm foo};                                                                    
\<close>
  
ML\<open>
ATP_Problem_to_tptp.atp_problem_to_tptp atp_problem;
\<close> 
    
end
  