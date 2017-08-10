theory GenerateATP
  imports Main Real Complex_Main
begin
  
declare[[ML_print_depth=50]]   
  
(*For the cube root use "root 3"*)  
lemma foo: "\<forall>X::real.(0 \<le> X \<longrightarrow> 0 <= X^2) "  
(*apply(atomize)*)
  sorry
 
ML\<open>
val theorem = Thm.concl_of @{thm foo};
\<close>  

ML_file "~/Documents/internship/verified-metitarski/proof_reconstruction/atp_problem_of_thm.ML"  
ML_file "~/Documents/internship/verified-metitarski/proof_reconstruction/atp_problem_to_tptp.ML"
ML_file "~/Documents/internship/verified-metitarski/proof_reconstruction/mt_call.ML"
  
  
(*Create ATP_Problem from a theorem*)  
ML\<open>
val atp_problem = ATP_Problem_of_thm.atp_problem_of_thm @{context} @{thm foo};                                                                    
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
(*Remove axioms*)
val trimmed_tptp_proof : string = 
  Substring.position "fof" (CharVectorSlice.full tptp_proof)
    |> #2
    |> CharVectorSlice.vector;

val atp_proof = ATP_Satallax.atp_proof_of_tstplike_proof "1" atp_problem trimmed_tptp_proof

(*Remove the clause derived by strip*)
fun remove_strip accum [] = rev accum
   |remove_strip accum ((step as (_, _, _, rule, _))::proof) =   
        if rule = "strip" then remove_strip accum proof
        else remove_strip (step::accum) proof

val atp_proof = remove_strip [] atp_proof
\<close>
  
  
end
  