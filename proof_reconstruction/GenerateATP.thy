theory GenerateATP
  imports Main Real Complex_Main
begin
  
declare[[ML_print_depth=50]]   
  
(*For the cube root use "root 3"*)  
lemma foo: "\<forall>X::real.(0 \<le> X \<longrightarrow> abs(ln(1+X) - X) <= X^2) "  
(*apply(atomize)*)
  sorry
 
ML\<open>
val theorem = Thm.concl_of @{thm foo};
\<close>  

ML_file "~/Documents/internship/verified-metitarski/proof_reconstruction/atp_problem_of_thm.ML"  
ML_file "~/Documents/internship/verified-metitarski/proof_reconstruction/atp_problem_to_tptp.ML"
ML_file "~/Documents/internship/verified-metitarski/proof_reconstruction/mt_call.ML"
  
ML\<open>
val atp_problem = ATP_Problem_of_thm.atp_problem_of_thm @{context} @{thm foo};                                                                    
\<close>
  
ML\<open>
val tptp_problem = ATP_Problem_to_tptp.atp_problem_to_tptp atp_problem;
\<close>

ML\<open>
val tptp_proof = Call_Metitarski.call_mt tptp_problem
\<close>  

    
end
  