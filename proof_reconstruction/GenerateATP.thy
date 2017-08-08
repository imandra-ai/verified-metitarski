theory GenerateATP
  imports Main Real Complex_Main
begin
  
declare[[ML_print_depth=50]]   
  
lemma foo: "\<forall>X Y::real .\<exists> Z. \<not> Z = (ln (5.3::real)) \<longrightarrow> greater 0 (times ( minus (abs X) 1::real) (minus X 1))"  
(*apply(atomize)*)
  sorry
 
ML\<open>
val theorem = Thm.concl_of @{thm foo};
\<close>  

ML_file "~/Documents/internship/verified-metitarski/proof_reconstruction/atp_problem_of_thm.ML"  
  
ML\<open>
val atp_problem = ATP_Problem_of_thm.atp_problem_of_thm @{context} @{thm foo};                                                                    
\<close>
  
ML\<open>

(*Function symbols that need to be translated to tptp. Need to add more*)
val plus = "Groups.plus_class.plus"
val minus = "Groups.minus_class.minus"
val times = "Groups.times_class.times"
val divide = "Rings.divide_class.divide"
val power = "Power.power_class.power"

(*Greater than is an abbreviation of less than in Isabelle*)
val less = "Orderings.ord_class.less"
val less_eq = "Orderings.ord_class.less_eq"
val eq = "HOL.eq"

val abs = "Groups.abs_class.abs"
val sqrt = "NthRoot.sqrt"
val ln = "Transcendental.ln_class.ln"

val zero = "Groups.zero_class.zero"
val one = "Groups.one_class.one"

datatype name_type = Infix | Prefix | NoArgs

val name_table = Symtab.empty
  |> Symtab.update_new (plus, (Infix, "+"))
  |> Symtab.update_new (minus, (Infix, "-"))
  |> Symtab.update_new (times, (Infix, "*"))
  |> Symtab.update_new (divide, (Infix, "/"))
  |> Symtab.update_new (power, (Infix, "^"))

  |> Symtab.update_new (less, (Infix, "<"))
  |> Symtab.update_new (less_eq, (Infix, "<="))
  |> Symtab.update_new (eq, (Infix, "="))

  |> Symtab.update_new (abs, (Prefix, "abs"))
  |> Symtab.update_new (sqrt, (Prefix, "sqrt"))
  |> Symtab.update_new (ln, (Prefix, "ln"))

  |> Symtab.update_new (zero, (NoArgs, "0"))
  |> Symtab.update_new (one, (NoArgs, "1"))


fun atp_number_to_int atp_term =
  (case atp_term of
    ATP_Problem.ATerm (("Num.num.One", _), []) => 1
  | ATP_Problem.ATerm (("Num.num.Bit0", _), [arg]) =>
      let
        val m = atp_number_to_int arg
      in
        m + m
      end
  | ATP_Problem.ATerm (("Num.num.Bit1", _), [arg]) =>
      let
        val m = atp_number_to_int arg
      in
        1 + m + m
      end
  | _ => error "Malformed atp number"
  );

fun atp_term_to_tptp atp_term = 
  (case atp_term of
    (*Translating natural numbers. Rational numbers are translated as fractions*)
    ATP_Problem.ATerm (("Num.numeral_class.numeral", _), [arg]) =>
      string_of_int (atp_number_to_int arg)

  | ATP_Problem.ATerm ((name, _), []) => 
      (case Symtab.lookup name_table name of
        NONE => name
      | SOME (NoArgs, tptp_name) => tptp_name
      | _ => error "Atp_term doesn't have any argumets but name_type is not NoArgs"
      )
  | ATP_Problem.ATerm ((name, _), arg1::args) =>
      (case Symtab.lookup name_table name of
        NONE => error "Tptp name of " ^ name ^ " operator unknown"
      | SOME (Infix, tptp_name) =>
          (case args of
            (*Enclose all infix operators in parantheses to ensure correct precedence*)
            [arg2] => "(" ^ (atp_term_to_tptp arg1) ^ " " ^ tptp_name ^ " " ^ (atp_term_to_tptp arg2) ^ ")"
          | _ => error "Infix operator " ^ name ^ " has incorrect number of argments"
          )
      | SOME (Prefix, tptp_name) =>
          let
            fun to_tptp_arg arg = "," ^ (atp_term_to_tptp arg) ^ " "
          in
            tptp_name ^ "(" ^ (atp_term_to_tptp arg1) ^ (String.concat (List.map to_tptp_arg args))  ^ ")"
          end
      | _ => error "Operator " ^ name ^ " has arguments but the name_type is NoArgs."
      )
  | _ => error "Malformed atp_term"
  );

(*atp_number_to_int (ATP_Problem.ATerm (("Num.num.Bit1", [ATP_Problem.AFun (ATP_Problem.AType (("Num.num", []), []), ATP_Problem.AType (("Num.num", []), []))]),
                    [ATP_Problem.ATerm (("Num.num.Bit0", [ATP_Problem.AFun (ATP_Problem.AType (("Num.num", []), []), ATP_Problem.AType (("Num.num", []), []))]),
                            [ATP_Problem.ATerm (("Num.num.One", [ATP_Problem.AType (("Num.num", []), [])]), [])])])]));
*)

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
      (atp_formula_to_tptp phi1) ^ " & " ^ (atp_formula_to_tptp phi2)
  | ATP_Problem.AConn (ATP_Problem.AOr, [phi1, phi2]) =>
      (atp_formula_to_tptp phi1) ^ " | " ^ (atp_formula_to_tptp phi2)
  | ATP_Problem.AConn (ATP_Problem.AImplies, [phi1, phi2]) =>
      (atp_formula_to_tptp phi1) ^ " => " ^ (atp_formula_to_tptp phi2)

  | ATP_Problem.AAtom term => atp_term_to_tptp term

  | _ => error "Malformed atp formula"
  );

fun atp_problem_to_tptp (atp_problem : (string * string ATP_Problem.atp_problem_line list) list) =
  let
    val atp_formula = 
      case
        atp_problem
          |> List.hd
          |> #2
          |> List.hd
      of
        ATP_Problem.Formula (_, _, formula, _, _) => formula
      | _ => error "Malfomred atp_problem"
  in
    (*Assume all conjectures are FOF for now*)
    "fof(" ^ 
    (atp_problem |> List.hd |> #1) ^
    ",conjecture, " ^ 
    (atp_formula_to_tptp atp_formula) ^
    ")."
  end;
  

atp_problem_to_tptp atp_problem;

\<close> 
    
end
  