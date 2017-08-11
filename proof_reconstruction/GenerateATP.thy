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

(*Remove the clause derived by strip=subgoal_0*)
fun remove_strip accum [] = rev accum
   |remove_strip accum ((step as (_, _, _, rule, _))::proof) =   
        if rule = "strip" then remove_strip accum proof
        else remove_strip (step::accum) proof

(*Clauses derived from subgoal_0 now derived from original goal*)
fun replace_from accum _ [] = rev accum
   |replace_from accum name'' ((name, role, t, rule, from)::proof) = 
        let val from' = map (fn (name',ls) => if name' = "subgoal_0" then (name'', ls) else (name',ls)) from
        in replace_from ((name, role, t, rule, from')::accum) name'' proof
        end

val conjecture_name = (#1 (#1 (hd atp_proof)))
                handle Empty => raise Fail "The parsed atp_proof is empty." 

val atp_proof = 
    atp_proof
        |>remove_strip []
        |>replace_from [] conjecture_name
\<close>

ML\<open>
fun atp_formula_to_term (atp_formula 
  : (string, string ATP_Problem.atp_type, 
     (string, string ATP_Problem.atp_type) ATP_Problem.atp_term, string) ATP_Problem.atp_formula) =
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
  