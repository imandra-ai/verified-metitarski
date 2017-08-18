signature PROVER =
sig

val prove : Proof.context -> string -> string -> unit

end

structure Prover : PROVER =
struct

fun prove (ctxt : Proof.context) (conj_name : string) (conjecture : string) : unit =
  let
    (*Transform a conjecture from a string to an Isabelle term*)
    val isa_conjecture : term =
      List.hd (Syntax.check_props ctxt [Syntax.parse_prop ctxt conjecture])

    (*Create ATP_Problem from a term*)
    val atp_problem = Thm_to_ATP_Problem.thm_to_atp_problem ctxt isa_conjecture conj_name

    (*Create tptp string with the problem*)
    val tptp_problem = ATP_Problem_to_tptp.atp_problem_to_tptp atp_problem

    (*Give it to Metitarski*)
    val tptp_proof = Call_Metitarski.call_mt MT_Config.mt_path MT_Config.problem_path tptp_problem

    (*Read the tptp proof into an ATP_Proof*) 
    val atp_proof = TPTP_Proof_to_atp_proof.tptp_proof_to_atp_proof atp_problem tptp_proof

    (*Termify the formulas in the atp_proof*) 
    val termified_atp_proof : (term, string) ATP_Proof.atp_step list 
      = Termify_atp_proof.termify_atp_proof atp_proof;

    (*Convert the indirect proof to isar*)  
    val (lemma, indirect_isar_proof) = 
      Termified_atp_proof_to_indirect_proof.termified_atp_proof_to_indirect_proof 
        ctxt termified_atp_proof

    (*For writing the Isar proof to a file.*)
    fun write (file : string) (text : string) =
      let
        val out_str = TextIO.openOut file
        val _ = TextIO.output (out_str, text)
        val _ = TextIO.closeOut out_str
      in
        ()
      end;

    val preamble = "theory " ^ "\"" ^ conj_name ^ "\""  ^ "\n imports Main Real Transcendental\n" ^ "begin \n"
    val end_string = "\nend";

    val proof_path = MT_Config.isar_proof_path ^ conj_name ^ ".thy"
  in
    write proof_path (preamble ^ lemma ^ indirect_isar_proof ^ end_string)
  end

end;