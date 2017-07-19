theory Isar
  imports Main
begin

ML_file "~/Documents/internship/verified-metitarski/proof_reconstruction/tstp_input.ML" 
    
ML_file "~/Documents/internship/verified-metitarski/proof_reconstruction/tstp_parsing.ML"

ML\<open>
ATP_Satallax.atp_proof_of_tstplike_proof "1" [("2", [ATP_Problem.Class_Decl("3", "4", [])])] 
    (TSTP_Input.read "Documents/internship/verified-metitarski/problems/cristina-problem-6.tstpout") 
\<close>

ML\<open>TSTP_Input.read "Documents/internship/verified-metitarski/proof_reconstruction/input.txt"\<close>
  
ML\<open>Sledgehammer_Prover_ATP.run_atp   Sledgehammer_Prover.Try   ""\<close> 
ML\<open>open Symtab\<close>  
ML\<open>open Term
   val f = add_vars;
\<close>  
    
  
end
  