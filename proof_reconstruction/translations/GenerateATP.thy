theory GenerateATP
  imports Main Real Complex_Main "~/Documents/internship/verified-metitarski/isabelle-proofs/AxiomsGeneral"
begin
  
declare[[ML_print_depth=50]]   
  
(*For the cube root use "root 3"*)
(*For log base 2 use "log 2"*)  
(*^ only allows natural numbers powers. Use powr for any real exponent?*)  
lemma foo: "\<forall>(Y::real).0 <= abs (Y^ 3) "  
(*apply(atomize)*)
  sorry  
    
ML\<open>
val theorem = Thm.concl_of @{thm foo};
\<close>  
  
ML_file "~/Documents/internship/verified-metitarski/proof_reconstruction/translations/thm_to_atp_problem.ML"  
ML_file "~/Documents/internship/verified-metitarski/proof_reconstruction/translations/atp_problem_to_tptp.ML"
ML_file "~/Documents/internship/verified-metitarski/proof_reconstruction/translations/mt_call.ML"
ML_file "~/Documents/internship/verified-metitarski/proof_reconstruction/translations/tptp_proof_to_atp_proof.ML"
ML_file "~/Documents/internship/verified-metitarski/proof_reconstruction/translations/termify_atp_proof.ML"  
  
  
(*Create ATP_Problem from a theorem*)  
ML\<open>
val atp_problem = Thm_to_ATP_Problem.thm_to_atp_problem @{context} @{thm foo};                                                                    
\<close>
  
(*Create tptp string with the problem*)  
ML\<open>
val tptp_problem = ATP_Problem_to_tptp.atp_problem_to_tptp atp_problem;
\<close>

(*Give it to Metitarski*)  
ML\<open>
(*Path to Metitarski on this computer*)
val mt_path = "/home/cristina/Documents/internship/metitarski/metit"

val tptp_proof = Call_Metitarski.call_mt mt_path tptp_problem
\<close>  

(*Read the tptp proof into an ATP_Proof*)  
ML\<open>
val atp_proof = TPTP_Proof_to_atp_proof.tptp_proof_to_atp_proof atp_problem tptp_proof
(*Need to deal with the case MT gives up*)
\<close>
  
ML\<open>
val termified_atp_proof : (term, string) ATP_Proof.atp_step list 
    = Termify_atp_proof.termify_atp_proof atp_proof;
\<close>  
  
end
  