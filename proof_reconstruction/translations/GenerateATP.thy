theory GenerateATP
  imports Main Real Complex_Main "~/Documents/internship/verified-metitarski/isabelle-proofs/AxiomsGeneral"
begin
  
declare[[ML_print_depth=50]]   
  
(*For the cube root use "root 3"*)
(*For log base 2 use "log 2"*)  
(*^ only allows natural numbers powers. Use powr infix for any real exponent?*)  
  
  
(*lemma foo: "\<forall>(Y::real).0 <= Y^2 "*)
  
(*Redirected proof involves a case split. Not supporting that at the moment.*)  
(*lemma foo: "\<forall>(Y::real).0 <= abs(Y^3)"*)
lemma foo: "\<forall>(X::real).(0\<le>X \<longrightarrow> abs(ln(1+X)-X) \<le> X^2)"  
(*lemma foo: "\<forall>(X::real) (Y::real).X+Y \<le> abs (X+Y)"*)
  
(*apply(atomize)*)
  sorry  
    
    
ML\<open>
val theorem = Thm.concl_of @{thm foo};
\<close>  

  
ML\<open>

fun pretty_thm ctxt thm =
  Syntax.pretty_term ctxt (Thm.prop_of thm);

(*val thm_string = Pretty.string_of  (pretty_thm @{context} @{thm foo})*)
(*val thm_string = Thm.string_of_thm @{context} @{thm foo}*)

fun write (file : string) (text : string) =
  let
    val out_str = TextIO.openOut file
    val _ = TextIO.output (out_str, text)
    val _ = TextIO.closeOut out_str
  in
    ()
  end;

(*write "/home/cristina/theorem.thy" thm_string*)

\<close>    
  
(*No absolute paths needed because this theory is in the same folder as the ML files.*)  
ML_file "config.ML"  

ML_file "thm_to_atp_problem.ML"  
ML_file "atp_problem_to_tptp.ML"
ML_file "mt_call.ML"
ML_file "tptp_proof_to_atp_proof.ML"
ML_file "termify_atp_proof.ML"

(*ML_file "termified_atp_proof_to_isar.ML"*) 
ML_file "termified_atp_proof_to_indirect_proof.ML"  
  
  
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
(*mt_path comes from config.ML*)
val tptp_proof = Call_Metitarski.call_mt mt_path problem_path tptp_problem
\<close>  

(*Read the tptp proof into an ATP_Proof*)  
ML\<open>
val atp_proof = TPTP_Proof_to_atp_proof.tptp_proof_to_atp_proof atp_problem tptp_proof
(*Need to deal with the case MT gives up*)
\<close>

(*Termify the formulas in the atp_proof*)  
ML\<open>
val termified_atp_proof : (term, string) ATP_Proof.atp_step list 
    = Termify_atp_proof.termify_atp_proof atp_proof;
\<close>  
 
(*Convert the indirect proof to isar*)  
ML\<open>
val (lemma, indirect_isar_proof) = 
  Termified_atp_proof_to_indirect_proof.termified_atp_proof_to_indirect_proof @{context} termified_atp_proof
\<close>  
  
ML\<open>
(*val proof = Termified_atp_proof_to_isar.termified_atp_proof_to_isar termified_atp_proof*)

(* Eventually we should automatically select what axioms to include *)
val preamble = "theory Proof \n imports Main Real\n" ^ 
  "\"" ^ abs_ax_path ^ "\"\n" ^ 
  "\"" ^ general_ax_path ^ "\"\n" ^
  "\"" ^ ln_bounds_path ^ "\"\n" ^
  "begin \n"
val end_string = "\nend";

write isar_proof_path (preamble ^ lemma ^ indirect_isar_proof ^ end_string)

\<close>  
  
end
  