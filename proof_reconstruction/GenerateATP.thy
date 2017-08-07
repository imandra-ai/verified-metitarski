theory GenerateATP
  imports Main Real Complex_Main
begin
  
declare[[ML_print_depth=50]]   
  
lemma foo: "\<forall>X Y::real .\<exists> Z. \<not> Z = (ln (2::real)) \<longrightarrow> greater 0 (times ( minus (abs X) 1::real) (minus X 1))"  
(*apply(atomize)*)
  sorry
 
ML\<open>
val theorem = Thm.concl_of @{thm foo};
\<close>  

ML_file "~/Documents/internship/verified-metitarski/proof_reconstruction/atp_problem_of_thm.ML"  
  
ML\<open>
ATP_Problem_of_thm.atp_problem_of_thm @{context} @{thm foo}                                                                    
\<close>

ML\<open>

(*Function symbols that need to be translated to tptp*)
val plus = "Groups.plus_class.plus"
val minus = "Groups.minus_class.minus"
val times = "Groups.times_class.times"
val divide = "Rings.divide_class.divide"
val power = "Power.power_class.power"

(*Greater than is an abbreviation of less than in Isabelle*)
val less = "Orderings.ord_class.less"
val less_eq = "Orderings.ord_class.less_eq"

val abs = "Groups.abs_class.abs"

val sqrt = "NthRoot.sqrt"
val ln = "Transcendental.ln_class.ln"

fun atp_term_to_tptp atp_term = error "";

fun atp_formula_to_tptp atp_formula = 
  (case atp_formula of
    ATP_Problem.AQuant (ATP_Problem.AForall, [(var, _)], phi) =>
      "![" ^ var ^ "] : (" ^ (atp_formula_to_tptp phi) ^ ")"
  | ATP_Problem.AQuant (ATP_Problem.AExists, [(var, _)], phi) =>
      "?[" ^ var ^ "] : (" ^ (atp_formula_to_tptp phi) ^ ")"

  (*Negation has exactly one argument*)
  | ATP_Problem.AConn (ATP_Problem.ANot, [phi]) =>
      "~" ^ (atp_formula_to_tptp phi)
  | ATP_Problem.AConn (ATP_Problem.AAnd, [phi1, phi2]) =>
      (atp_formula_to_tptp phi1) ^ "&" ^ (atp_formula_to_tptp phi2)
  | ATP_Problem.AConn (ATP_Problem.AOr, [phi1, phi2]) =>
      (atp_formula_to_tptp phi1) ^ "|" ^ (atp_formula_to_tptp phi2)
  | ATP_Problem.AConn (ATP_Problem.AImplies, [phi1, phi2]) =>
      (atp_formula_to_tptp phi1) ^ "=>" ^ (atp_formula_to_tptp phi2)

  | ATP_Problem.AAtom term => atp_term_to_tptp term

  | _ => error "Malformed atp formula"
  )
\<close> 
    
end
  