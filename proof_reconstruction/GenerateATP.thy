theory GenerateATP
  imports Main Real Complex_Main
begin
  
declare[[ML_print_depth=50]]   
  
(*For the cube root use "root 3"*)
(*^ only allows natural numbers powers. Does MT allow any powe?*)  
lemma foo: "\<forall>X::real.(0 = X/2 \<longrightarrow> 0 <= X) "  
(*apply(atomize)*)
  sorry

lemma foo': "False"
  sorry  
  
lemma foo_metalevel: "0\<le>(X::real) \<Longrightarrow> 0\<le> X^2"
  sorry

ML\<open>
Thm.concl_of @{thm foo'}
\<close>    
  
ML\<open>
val theorem = Thm.concl_of @{thm foo};
\<close>  

ML\<open>
Thm.prems_of @{thm foo_metalevel}
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
    |> Symtab.update_new ("add", (ATP_Problem_to_tptp.plus, @{typ "real\<Rightarrow>real\<Rightarrow>real"}))
    |> Symtab.update_new ("subtract", (ATP_Problem_to_tptp.minus, @{typ "real\<Rightarrow>real\<Rightarrow>real"}))
    |> Symtab.update_new ("neg", (ATP_Problem_to_tptp.uminus, @{typ "real\<Rightarrow>real"}))
    |> Symtab.update_new ("multiply", (ATP_Problem_to_tptp.times, @{typ "real\<Rightarrow>real\<Rightarrow>real"}))
    |> Symtab.update_new ("divide", (ATP_Problem_to_tptp.divide, @{typ "real\<Rightarrow>real\<Rightarrow>real"}))
    |> Symtab.update_new ("power", (ATP_Problem_to_tptp.power, @{typ "real\<Rightarrow>nat\<Rightarrow>real"}))

    |> Symtab.update_new ("less", (ATP_Problem_to_tptp.less, @{typ "real\<Rightarrow>real\<Rightarrow>bool"}))
    |> Symtab.update_new ("less_equal", (ATP_Problem_to_tptp.less_eq, @{typ "real\<Rightarrow>real\<Rightarrow>bool"}))

    
 

    (*Not supported in atp_problem_to_tptp*)
    |> Symtab.update_new ("$false", ("HOL.False", @{typ "bool"}))
  
(*TODO: Support all the other operators*)
(*TODO: Translate numbers. Power requires a nat argmumet!*)
(*TODO: Transform bound variables to Bound*)
(*TODO: Fix types of Free variables*)
fun atp_term_to_term (atp_term : (string, string ATP_Problem.atp_type) ATP_Problem.atp_term) 
  : term =
  (case atp_term of
    ATP_Problem.ATerm ((name, _), args) =>
      (case Symtab.lookup tptp_prefix_name_to_isabelle name of
        (*For now interpret all variables as free. Fix with an extra function!*)
        NONE => if args=[] then Free (name, @{typ 'a})
                else error ("Unsupported tptp operator: " ^ name)
      | SOME (isa_name, ty) => 
          let 
            val termified_args = List.map atp_term_to_term args

            fun isa_app ((arg:term), (func:term)) = func $ arg
          in
            List.foldl isa_app (Const (isa_name, ty)) termified_args 
          end
      )

  (*Not supporting atp_term AAbs*)
  | _ => error "Invalid atp_term"
  )

fun atp_formula_to_term (atp_formula 
  : (string, string (*This is the type that ATPSatallax returns, not: string ATP_Problem.atp_type*), 
     (string, string ATP_Problem.atp_type) ATP_Problem.atp_term, string) ATP_Problem.atp_formula)
  : term =
  (case atp_formula of
    ATP_Problem.AQuant (quantifier, [(var, _)], phi) =>
      let
        val quant_string =
          (case quantifier of
            ATP_Problem.AForall => "HOL.All"
          | ATP_Problem.AExists => "HOL.Ex"
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

  | ATP_Problem.AAtom atp_term => atp_term_to_term atp_term

  (*Not supporting equivalence (AIff) and type qunatifiers*)
  | _ => error "Unsupported atp_formula."
  )

(*Need to wrap formula in HOL.Trueprop*)
fun wrap_term (t : term) : term =
  Const ("HOL.Trueprop", @{typ "bool \<Rightarrow> prop"}) $ t

fun termify_atp_proof (atp_proof : string ATP_Proof.atp_proof) 
  : (term, string) ATP_Proof.atp_step list=
  let 
    fun termify_atp_proof_line (name, role, phi, rule, from) =
      (name, role, wrap_term (atp_formula_to_term phi), rule, from)
  in
    List.map termify_atp_proof_line atp_proof
  end;

termify_atp_proof atp_proof;
\<close>  
  
end
  