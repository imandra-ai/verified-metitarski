theory GenerateATP
  imports Main Real Transcendental "~/Documents/internship/verified-metitarski/isabelle-proofs/AxiomsGeneral"
begin
  
declare[[ML_print_depth=50]]   
  
(*For the cube root use "root 3"*)
(*For log base 2 use "log 2"*)  
(*^ only allows natural numbers powers. Use powr infix for any real exponent?*)  
  
  
  
(*lemma foo: "\<forall>(Y::real).0 <= Y^2 "*)
  
(*Redirected proof involves a case split. Not supporting that at the moment.*)  
(*lemma foo: "\<forall>(Y::real).0 <= abs(Y^3)"*)
(*lemma foo: "\<forall>(X::real).(0\<le>X \<longrightarrow> abs(ln(1+X)-X) \<le> X^2)"*)
lemma foo: "\<forall>(X::real) (Y::real).X+Y \<le> abs (X+Y)"  
  ML_val {* 
  val st = #goal @{Isar.goal};
  (*Thm.prop_of (#goal @{Isar.goal})*) *}
    apply(tactic {*fn st => (writeln (@{make_string} st); Seq.single st) *})
  ML_prf{**}
sorry    
    
  
ML\<open>
  val conjecture : term = List.hd (Syntax.check_props @{context}
    [Syntax.parse_prop @{context} "\<forall>(X::real) (Y::real).X+Y \<le> abs (X+Y)"])

  val conjecture = Const ("Pure.imp", @{typ "prop \<Rightarrow> prop \<Rightarrow> prop"}) $
                   conjecture $ 
                   (Const ("Pure.prop", @{typ "prop \<Rightarrow> prop"}) $ conjecture)

  (*val conjecture : cterm = Thm.cterm_of @{context} conjecture;

  @{thm conjecture}*)
\<close>  
  
ML\<open>
val theorem = Thm.concl_of @{thm foo};
fun delimiter #"." = true
  | delimiter _ = false
val thm_name = List.last (String.tokens delimiter (Thm.derivation_name @{thm foo}))
\<close>  

(*Getting an Isabelle term from a conjecture string*)  
ML\<open>
List.hd (Syntax.check_props @{context}
  [Syntax.parse_prop @{context} "\<forall>(X::real).(((0 <= X) \<longrightarrow> (abs((ln((1 + X)) - X)) <= power X 2)))"])
\<close>  
  
  
ML\<open>
fun write (file : string) (text : string) =
  let
    val out_str = TextIO.openOut file
    val _ = TextIO.output (out_str, text)
    val _ = TextIO.closeOut out_str
  in
    ()
  end;
\<close>    
  
(*No absolute paths needed because this theory is in the same folder as the ML files.*)  
ML_file "config.ML"  
ML_file "atp_util.ML" 
ML_file "sledgehammer_isar.ML"

  
ML_file "thm_to_atp_problem.ML"  
ML_file "atp_problem_to_tptp.ML"
ML_file "mt_call.ML"
ML_file "tptp_proof_to_atp_proof.ML"
ML_file "termify_atp_proof.ML"

(*ML_file "termified_atp_proof_to_isar.ML" *)
ML_file "termified_atp_proof_to_indirect_proof.ML"  


  
(*Create ATP_Problem from a term*)  
ML\<open>
val atp_problem = Thm_to_ATP_Problem.thm_to_atp_problem @{context} theorem thm_name;                                                                    
\<close>
  
(*Create tptp string with the problem*)  
ML\<open>
val tptp_problem = ATP_Problem_to_tptp.atp_problem_to_tptp atp_problem;
\<close>

(*Give it to Metitarski*)  
ML\<open>
(*mt_path comes from config.ML*)
val tptp_proof = Call_Metitarski.call_mt MT_Config.mt_path MT_Config.problem_path tptp_problem
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
 
(*Using isar_proof_text instead*)  
ML\<open>
val ctxt : Proof.context = @{context}
val debug : bool = true
val isar_proofs : bool option = SOME true
val smt_proofs : bool option = SOME false
val num_chained : int = 1 (*What is this?*)

  val verbose : bool = true
  val alt_metis_args : string option * string option = (NONE, NONE)
  val preplay_timeout : Time.time = Time.fromSeconds 5
  val compress : real option = NONE
  val try0 : bool = true
  val minimize : bool = false
  val atp_proof0 : (term, string) ATP_Proof.atp_step list = termified_atp_proof
  val goal : term (*thm*) = conjecture (*@{thm foo}*)
val isar_params : unit ->Sledgehammer_Isar.isar_params = 
  fn () => (verbose, alt_metis_args, preplay_timeout, compress, try0, minimize, atp_proof0, goal)

  val used_facts : (string * Sledgehammer_Isar.stature) list = []
  val preplay : Sledgehammer_Proof_Methods.proof_method = Sledgehammer_Proof_Methods.Auto_Method  (*?*)
  val one_line_play : Sledgehammer_Proof_Methods.play_outcome = Sledgehammer_Proof_Methods.Played Time.zeroTime  (*?*)
  val banner : string = ""
  val subgoal : int = 1
  val subgoal_count : int = 1
val one_line_params : Sledgehammer_Isar.one_line_params =
  ((used_facts, (preplay, one_line_play)), banner, subgoal, subgoal_count);

ML_Pretty.format_polyml 86 (ML_Pretty.to_polyml (ML_Pretty.str (Sledgehammer_Isar.isar_proof_text ctxt debug num_chained isar_proofs smt_proofs 
  isar_params one_line_params)))
\<close>  
 
ML\<open>
open ML_Pretty
\<close>  
  
ML\<open>
(*val proof = Termified_atp_proof_to_isar.termified_atp_proof_to_isar termified_atp_proof;
writeln proof;
*)

(* Eventually we should automatically select what axioms to include *)
val preamble = "theory Proof \n imports Main Real Transcendental\n" ^ 
  "\"" ^ MT_Config.abs_ax_path ^ "\"\n" ^ 
  "\"" ^ MT_Config.general_ax_path ^ "\"\n" ^
  "\"" ^ MT_Config.ln_bounds_path ^ "\"\n" ^
  "begin \n"
val end_string = "\nend";

val proof_path = MT_Config.isar_proof_path ^ "Proof.thy";

write proof_path (preamble ^ lemma ^ indirect_isar_proof ^ end_string)

\<close>  
 
  
end
  