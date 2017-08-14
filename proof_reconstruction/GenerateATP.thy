theory GenerateATP
  imports Main Real Complex_Main
begin
  
declare[[ML_print_depth=50]]   
  
(*For the cube root use "root 3"*)  
lemma foo: "\<forall>X::real.(0 \<le> X \<longrightarrow> 0 <= X^2) "  
(*apply(atomize)*)
  sorry

lemma foo_metalevel: "0\<le>(X::real) \<Longrightarrow> 0\<le> X^2"
  sorry
ML\<open>
Thm.prems_of @{thm foo_metalevel}
\<close>    
  
ML\<open>
val theorem = Thm.concl_of @{thm foo};
\<close>  

ML_file "~/Documents/internship/verified-metitarski/proof_reconstruction/thm_to_atp_problem.ML"  
ML_file "~/Documents/internship/verified-metitarski/proof_reconstruction/atp_problem_to_tptp.ML"
ML_file "~/Documents/internship/verified-metitarski/proof_reconstruction/mt_call.ML"
ML_file "~/Documents/internship/verified-metitarski/proof_reconstruction/tptp_proof_to_atp_proof.ML"  
  
  
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
\<close>

ML\<open>
open Symtab
\<close>  
  
ML\<open>
val tptp_prefix_name_to_isabelle = 
  Symtab.empty
    |> Symtab.update_new ()
     

fun atp_term_to_term (atp_term : (string, string ATP_Problem.atp_type) ATP_Problem.atp_term) 
  : term =
  (case atp_term of
    ATP_Problem.ATerm ((name, _), args) =>
      let
        val isa_name = Symtab.lookup tptp_prefix_name_to_isabelle name
      in
        
      end
  )

(*Need to wrap formula in HOL.Trueprop*)
fun atp_formula_to_term (atp_formula 
  : (string, string ATP_Problem.atp_type, 
     (string, string ATP_Problem.atp_type) ATP_Problem.atp_term, string) ATP_Problem.atp_formula)
  : term =
  (case atp_formula of
    ATP_Problem.AQuant (quantifier, [(var, _)], phi) =>
      let
        val quant_string =
          (case quantifier of
            ATP_Problem.AForall => "HOL.All"
          | ATP_Problem.AExists => "HOL.Ex"
          | _ => error "Not a valid atp_formula"
          )
      in
        (Const (quant_string, @{typ  "(real \<Rightarrow> bool) \<Rightarrow> bool"}) $
         Abs (var, @{typ "real"}, (atp_formula_to_term phi)))
      end

  | ATP_Problem.AConn (conn, [phi1, phi2]) =>
      let
        val conn_string =
          (case conn of
            ATP_Problem.AImplies => "HOL.implies"
          | ATP_Problem.AAnd => "HOL.conj"
          | ATP_Problem.AOr => "HOL.disj"
          | _ => error "Unupported atp connective"
          )
      in
        (Const (conn_string, @{typ "bool \<Rightarrow> bool \<Rightarrow> bool"})) $ 
        (atp_formula_to_term phi1) $
        (atp_formula_to_term phi2)
      end

  | ATP_Problem.AConn (ATP_Problem.ANot, [phi]) =>
      (Const ("HOL.Not", @{typ "bool \<Rightarrow> bool"})) $
      (atp_formula_to_term phi)

  | ATP_Problem.AAtom atp_term => error "" (*atp_term_to_term atp_term*)

  | _ => error "Unsupported atp_formula."
  )
\<close>  
  
end
  