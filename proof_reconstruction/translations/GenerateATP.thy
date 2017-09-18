theory GenerateATP
  imports 
    Main 
    Real 
    Transcendental 
    "~/Documents/internship/verified-metitarski/isabelle-proofs/AxiomsAbs" 
    "~/Documents/internship/verified-metitarski/isabelle-proofs/AxiomsGeneral"
    "~/Documents/internship/verified-metitarski/isabelle-proofs/LnBounds"
    "~/Documents/internship/verified-metitarski/isabelle-proofs/Arithmetic"
    "~/Documents/internship/verified-metitarski/proof_reconstruction/translations/Example"
    "~~/src/HOL/Library/Sum_of_Squares"
begin
  
declare[[ML_print_depth=50]]
    
(*No absolute paths needed because this theory is in the same folder as the ML files.*)  
ML_file "config.ML"  
  
(*My copy of the Sledgehammer files. The order these are loaded is important!"*)
ML_file "Sledgehammer/sledgehammer_util.ML"
ML_file "Sledgehammer/sledgehammer_fact.ML"   
ML_file "Sledgehammer/sledgehammer_proof_methods.ML"
ML_file "Sledgehammer/sledgehammer_isar_proof.ML"
ML_file "Sledgehammer/sledgehammer_isar_preplay.ML"
ML_file "Sledgehammer/sledgehammer_isar_compress.ML"  
ML_file "Sledgehammer/sledgehammer_isar_minimize.ML"  
ML_file "Sledgehammer/sledgehammer_isar.ML"
ML_file "Sledgehammer/sledgehammer_prover.ML"
ML_file "Sledgehammer/sledgehammer_prover_atp.ML"
ML_file "Sledgehammer/sledgehammer_prover_smt.ML"
ML_file "Sledgehammer/sledgehammer_prover_minimize.ML"  
ML_file "Sledgehammer/sledgehammer_mash.ML" 
ML_file "Sledgehammer/sledgehammer.ML"
(*ML_file "Sledgehammer/sledgehammer_commands.ML"  *)
  
ML_file "thm_to_atp_problem.ML"  
ML_file "atp_problem_to_tptp.ML"
ML_file "mt_call.ML"
ML_file "tptp_proof_to_atp_proof.ML"
ML_file "termify_atp_proof.ML"  

  
ML\<open>
fun isar_proof (st : thm) (mt_args : string list) (ctxt : Proof.context)  =
  let

    (*Getting the name of a theorem*)
    fun delimiter #"." = true
      | delimiter _ = false
    val thm_name = (List.last (String.tokens delimiter (Thm.derivation_name st))
                    handle Empty => "Conjecture")

    (*Strip the Pure.prop from in front of the conclusion*)
    val conjecture =
      (case Thm.concl_of st of
        Const("Pure.prop", _) $ t => 
          (case t of
            Const("Pure.term", _) $ t1 => t1
          | _ => t
          ) 
      | _ => raise Fail "Malformed conjecture"
      )

    (*Create ATP_Problem from a term*)  
    val atp_problem = Thm_to_ATP_Problem.thm_to_atp_problem ctxt 
      conjecture thm_name;       
    (*Create tptp string with the problem*)  
    val tptp_problem = ATP_Problem_to_tptp.atp_problem_to_tptp atp_problem;
    val _ = @{print} tptp_problem    

    (*Give it to Metitarski*)  
    (*mt_path comes from config.ML*)
    val tptp_proof = Call_Metitarski.call_mt MT_Config.mt_path MT_Config.problem_path tptp_problem mt_args
    val _ = @{print} tptp_proof

    (*Read the tptp proof into an ATP_Proof*)  
    val atp_proof = TPTP_Proof_to_atp_proof.tptp_proof_to_atp_proof atp_problem tptp_proof
    (*Need to deal with the case MT gives up*)
    val _ = @{print} atp_proof   

    (*Termify the formulas in the atp_proof*)  
    val termified_atp_proof : (term, string) ATP_Proof.atp_step list 
        = Termify_atp_proof.termify_atp_proof atp_proof;
    val _ = @{print} "TERMIFIED ATP PROOF:"
    val _ = @{print} termified_atp_proof      

    (*Using isar_proof_text instead*)  
    val ctxt : Proof.context = ctxt
    val debug : bool = true
    val isar_proofs : bool option = SOME true
    val smt_proofs : bool option = SOME false
    val num_chained : int = 1 (*What is this?*)
    
      val verbose : bool = true
      val alt_metis_args : string option * string option = (NONE, NONE)
      val preplay_timeout : Time.time = Time.fromSeconds 5
      val compress : real option = SOME 0.0 (*Turn off proof compression for testing.
                                              to turn on, use NONE, or a positive number.*)
      val try0 : bool = false (*if true, tries the automated methods before translating the MT proof*)
      val minimize : bool = false
      val atp_proof0 : (term, string) ATP_Proof.atp_step list = termified_atp_proof
      val goal : thm = st (*the theorem that was passed as an argument to the function*)
    val isar_params : unit ->Sledgehammer_Isar.isar_params = 
      fn () => (verbose, alt_metis_args, preplay_timeout, compress, try0, minimize, atp_proof0, goal)
    
      val used_facts : (string * Sledgehammer_Isar.stature) list = [] (*Only affects the one-line proof we're not using*)
      val preplay : Sledgehammer_Proof_Methods.proof_method = Sledgehammer_Proof_Methods.Auto_Method  (*?*)
      val one_line_play : Sledgehammer_Proof_Methods.play_outcome = Sledgehammer_Proof_Methods.Played Time.zeroTime  (*?*)
      val banner : string = "metitarski"  (*This is now also needed in selecting proof methods. 
                                            It must contain the work metitarski*)
      val subgoal : int = 1
      val subgoal_count : int = 1
    val one_line_params : Sledgehammer_Isar.one_line_params =
      ((used_facts, (preplay, one_line_play)), banner, subgoal, subgoal_count);
  in 
    (*atp_proof*)
    (*conjecture*)
    (*atp_problem*)
    (*tptp_proof*)
    ML_Pretty.format_polyml 86 (ML_Pretty.to_polyml (ML_Pretty.str (Sledgehammer_Isar.isar_proof_text ctxt debug num_chained isar_proofs smt_proofs 
      isar_params one_line_params)))
  end
\<close>
  
(*For the cube root use "root 3"*)
(*For log base 2 use "log 2"*)  
(*^ only allows natural numbers powers. Use powr infix for any real exponent?*)   

(* Making a custom MT simpset*)  
named_theorems metitarski_simps "arithmetic simplification rules used by Metitarski"
 
declare power2_eq_square[metitarski_simps]     
  
lemma foo1: "\<forall>(Y::real).0 <= Y^2 "
  apply(tactic {*fn st => (writeln (isar_proof st [] @{context}); Seq.single st) *})
proof -
  { fix rr :: real
    have "\<not> 0 < rr * (rr * - 1)"
      by sos (* 12 ms *)
    then have "\<not> rr\<^sup>2 < 0"
      by mt_arith_rule (* failed *) }
  then have "\<forall>r. \<not> (r::real)\<^sup>2 < 0"
    by satx (* 0.0 ms *)
  then show ?thesis
    by auto (* 0.0 ms *)
qed

lemma foo2: "\<forall>(Y::real).0 <= abs(Y^3)"
(*  ML_val{*writeln (isar_proof (#goal @{Isar.goal}) @{context})*}*)
  apply(tactic {*fn st => (writeln (isar_proof st [] @{context}); Seq.single st) *})
proof -
  { fix rr :: real
    have ff1: "0 \<le> rr * (rr * rr) \<or> \<bar>rr * (rr * rr)\<bar> = - (rr * (rr * rr))"
      using abs_negative by blast (* 0.0 ms *)
    have "- (rr * (rr * rr)) < 0 \<or> \<bar>rr * (rr * rr)\<bar> \<noteq> - (rr * (rr * rr)) \<or> 0 \<le> \<bar>rr * (rr * rr)\<bar>"
      by auto (* 4 ms *)
    then have ff2: "- (rr * (rr * rr)) < 0 \<or> 0 \<le> rr * (rr * rr) \<or> 0 \<le> \<bar>rr * (rr * rr)\<bar>"
      using ff1 by fastforce (* 0.0 ms *)
    have ff3: "rr * (rr * rr) < 0 \<or> \<bar>rr * (rr * rr)\<bar> = rr * (rr * rr)"
      using abs_nonnegative by auto (* 12 ms *)
    have "rr * (rr * rr) < 0 \<or> \<bar>rr * (rr * rr)\<bar> \<noteq> rr * (rr * rr) \<or> 0 \<le> \<bar>rr * (rr * rr)\<bar>"
      by auto (* 4 ms *)
    then have ff4: "rr * (rr * rr) < 0 \<or> 0 \<le> \<bar>rr * (rr * rr)\<bar>"
      using ff3 by fastforce (* 0.0 ms *)
    have "\<not> rr * (rr * rr) \<le> 0 \<or> \<not> 0 < rr * (rr * rr)"
      by auto (* 4 ms *)
    moreover
    { assume "\<not> 0 < rr * (rr * rr)"
      then have "\<not> - (rr * (rr * rr)) < 0"
        by mt_arith_rule (* failed *)
      then have "rr * (rr * rr) < 0 \<longrightarrow> \<not> - (rr * (rr * rr)) < 0 \<and> \<not> 0 \<le> rr * (rr * rr)"
        by force (* 4 ms *)
      moreover
      { assume "\<not> - (rr * (rr * rr)) < 0 \<and> \<not> 0 \<le> rr * (rr * rr)"
        then have "\<not> \<bar>rr * (rr * rr)\<bar> < 0"
          using ff2 by simp (* 12 ms *) }
      ultimately have "\<not> rr * (rr * rr) < 0 \<or> \<not> \<bar>rr * (rr * rr)\<bar> < 0"
        by metis (* 8 ms *) }
    moreover
    { assume "\<not> rr * (rr * rr) \<le> 0"
      then have "\<not> 0 < rr * (rr * (rr * - 1))"
        by sos (* 20 ms *)
      then have "\<not> rr * (rr * rr) < 0"
        by mt_arith_rule (* failed *) }
    ultimately have "\<not> rr * (rr * rr) < 0 \<or> \<not> \<bar>rr * (rr * rr)\<bar> < 0"
      by metis (* 64 ms *)
    moreover
    { assume "\<not> rr * (rr * rr) < 0"
      then have "\<not> \<bar>rr * (rr * rr)\<bar> < 0"
        using ff4 by simp (* 4 ms *) }
    ultimately have "\<not> \<bar>rr * (rr * rr)\<bar> < 0"
      by metis (* 8 ms *)
    then have "\<not> \<bar>rr ^ 3\<bar> < 0"
      by mt_arith_rule (* failed *) }
  then have "\<forall>r. \<not> \<bar>(r::real) ^ 3\<bar> < 0"
    by meson (* 0.0 ms *)
  then show ?thesis
    by auto (* 8 ms *)
qed
 
lemma foo3: "\<forall>(X::real) (Y::real).X+Y \<le> abs (X+Y)"     
  apply(tactic {*fn st => (writeln (isar_proof st [] @{context}); Seq.single st) *})
proof -
  { fix rr :: real and rra :: real
    have ff1: "0 \<le> rr + rra \<or> \<bar>rr + rra\<bar> = - (rr + rra)"
      using abs_negative by blast (* 4 ms *)
    have "- (rr + rra) < rr + rra \<or> \<bar>rr + rra\<bar> \<noteq> - (rr + rra) \<or> rr + rra \<le> \<bar>rr + rra\<bar>"
      by auto (* 20 ms *)
    then have ff2: "- (rr + rra) < rr + rra \<or> 0 \<le> rr + rra \<or> rr + rra \<le> \<bar>rr + rra\<bar>"
      using ff1 by fastforce (* 0.0 ms *)
    have ff3: "rr + rra < 0 \<or> \<bar>rr + rra\<bar> = rr + rra"
      using abs_nonnegative by auto (* 16 ms *)
    have "rr + rra < rr + rra \<or> \<bar>rr + rra\<bar> \<noteq> rr + rra \<or> rr + rra \<le> \<bar>rr + rra\<bar>"
      by auto (* 16 ms *)
    then have ff4: "rr + rra < 0 \<or> rr + rra < rr + rra \<or> rr + rra \<le> \<bar>rr + rra\<bar>"
      using ff3 by fastforce (* 0.0 ms *)
    have "\<not> rr * - 1 \<le> rra \<or> \<not> rra < rr * - 1"
      by simp (* 0.0 ms *)
    moreover
    { assume "\<not> rr * - 1 \<le> rra"
      then have "\<not> rr * - 1 \<le> rra \<and> \<not> rra \<le> rr * - 1 \<or> \<not> rr * - 1 < rra \<and> \<not> rr * - 1 \<le> rra"
        by auto (* 12 ms *)
      moreover
      { assume "\<not> rr * - 1 < rra \<and> \<not> rr * - 1 \<le> rra"
        then have "\<not> - (rr + rra) < rr + rra \<and> \<not> 0 \<le> rr + rra"
          by mt_arith_rule (* failed *)
        then have "\<not> \<bar>rr + rra\<bar> < rr + rra"
          using ff2 by fastforce (* 44 ms *) }
      moreover
      { assume "\<not> rr * - 1 \<le> rra \<and> \<not> rra \<le> rr * - 1"
        then have "\<not> rra < rr * - 1"
          by sos (* 92 ms *) }
      ultimately have "\<not> \<bar>rr + rra\<bar> < rr + rra \<or> \<not> rra < rr * - 1"
        by metis (* 20 ms *) }
    ultimately have "\<not> \<bar>rr + rra\<bar> < rr + rra \<or> \<not> rra < rr * - 1"
      by metis (* 8 ms *)
    moreover
    { assume "\<not> rra < rr * - 1"
      then have "\<not> rr + rra < 0 \<and> \<not> rr + rra < rr + rra"
        by mt_arith_rule (* failed *)
      then have "\<not> \<bar>rr + rra\<bar> < rr + rra"
        using ff4 by auto (* 8 ms *) }
    ultimately have "\<not> \<bar>rr + rra\<bar> < rr + rra"
      by metis (* 12 ms *) }
  then have "\<forall>r ra. \<not> \<bar>(r::real) + ra\<bar> < r + ra"
    by blast (* 0.0 ms *)
  then show ?thesis
    by auto (* 4 ms *)
      qed

(*
lemma before_ff4: "\<not> lgen False (X_000043 - 1) X_000044 \<or> X_000043 \<le> 0 \<or> ln X_000043 \<le> X_000044"
  using lgen_le_neg ln_upper_bound_cf1 by blast
    
lemma ff4: "(- 1 + (X_000050::real)) / X_000050 < X_000051 \<or> X_000050 \<le> 0 \<or> X_000051 \<le> ln X_000050"
  apply(insert before_ff4)
  apply(rule spec [where ?x = X_000050])
  apply(rule spec [where ?x = X_000051])
  apply(atomize)
  apply(blast)  
*)  
  

  
(*  ML_prf{**}*)    
  
(*  
ML\<open>
  val conjecture : term = List.hd (Syntax.check_props @{context}
    [Syntax.parse_prop @{context} "\<forall>(X::real) (Y::real).X+Y \<le> abs (X+Y)"])

  val conjecture = Const ("Pure.imp", @{typ "prop \<Rightarrow> prop \<Rightarrow> prop"}) $
                   conjecture $ 
                   (Const ("Pure.prop", @{typ "prop \<Rightarrow> prop"}) $ conjecture)
\<close>  

(*Getting an Isabelle term from a conjecture string*)  
ML\<open>
List.hd (Syntax.check_props @{context}
  [Syntax.parse_prop @{context} "\<forall>(X::real).(((0 <= X) \<longrightarrow> (abs((ln((1 + X)) - X)) <= power X 2)))"])
\<close>   
  
ML\<open>
(*Writing to a file*)
fun write (file : string) (text : string) =
  let
    val out_str = TextIO.openOut file
    val _ = TextIO.output (out_str, text)
    val _ = TextIO.closeOut out_str
  in
    ()
  end;
\<close>    
  
(*ML_file "termified_atp_proof_to_isar.ML" *)
ML_file "termified_atp_proof_to_indirect_proof.ML"    
  
ML\<open>
(*Convert the indirect proof to isar*)  
val (lemma, indirect_isar_proof) = 
  Termified_atp_proof_to_indirect_proof.termified_atp_proof_to_indirect_proof @{context} termified_atp_proof

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
*) 
  
end
  