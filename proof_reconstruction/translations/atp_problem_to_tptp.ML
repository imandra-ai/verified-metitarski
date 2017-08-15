signature ATP_PROBLEM_TO_TPTP =
sig
  val atp_problem_to_tptp : string ATP_Problem.atp_problem -> string

  val plus : string
  val minus : string
  val uminus : string
  val times : string
  val divide : string
  val power : string
  val powr : string
  
  val less : string
  val less_eq : string
  val eq : string
  
  val abs : string
  val sqrt : string
  val ln : string
  val arcsin : string
  val arccos : string
  val arctan : string
  val exp : string
  val cos : string
  val sin : string
  val tan : string
  
  val max : string
  val min : string
  
  val zero : string
  val one : string
  val pi : string

  val nthrt : string
  val log : string
end;

structure ATP_Problem_to_tptp : ATP_PROBLEM_TO_TPTP =
struct

(*Function symbols that need to be translated to tptp. Need to add more*)
val plus = "Groups.plus_class.plus"
val minus = "Groups.minus_class.minus"
val uminus = "Groups.uminus_class.uminus"
val times = "Groups.times_class.times"
val divide = "Rings.divide_class.divide"
val power = "Power.power_class.power"
(*Different operator for real powers!*)
val powr = "Transcendental.powr"

(*Greater than is an abbreviation of less than in Isabelle.
  Not_eq (!=) is an abbreviation of Not and Eq. 
  Will need to translate them from tptp to Isabelle.
  Also, lgen*)
val less = "Orderings.ord_class.less"
val less_eq = "Orderings.ord_class.less_eq"
val eq = "HOL.eq"

val abs = "Groups.abs_class.abs"
val sqrt = "NthRoot.sqrt"
val ln = "Transcendental.ln_class.ln"
val arcsin = "Transcendental.arcsin"
val arccos = "Transcendental.arccos"
val arctan = "Transcendental.arctan"
val exp = "Transcendental.exp"
val cos = "Transcendental.cos"
val sin = "Transcendental.sin"
val tan = "Transcendental.tan"

val max = "Orderings.ord_class.max"
val min = "Orderings.ord_class.min"

val zero = "Groups.zero_class.zero"
val one = "Groups.one_class.one"
val pi = "Transcendental.pi"

val nthrt = "NthRoot.root"
val log = "Transcendental.log"
(*Also support cbrt and nthroot and log but they are hardcoded in atp_term_to_tptp*)

datatype name_type = Infix | Prefix | Unary | NoArgs

val isabelle_to_infix_tptp_name = Symtab.empty
  |> Symtab.update_new (plus, (Infix, "+"))
  |> Symtab.update_new (minus, (Infix, "-"))
  |> Symtab.update_new (uminus, (Unary, "-"))
  |> Symtab.update_new (times, (Infix, "*"))
  |> Symtab.update_new (divide, (Infix, "/"))
  |> Symtab.update_new (power, (Infix, "^"))
  |> Symtab.update_new (powr, (Prefix, "pow"))

  |> Symtab.update_new (less, (Infix, "<"))
  |> Symtab.update_new (less_eq, (Infix, "<="))
  |> Symtab.update_new (eq, (Infix, "="))

  |> Symtab.update_new (abs, (Prefix, "abs"))
  |> Symtab.update_new (sqrt, (Prefix, "sqrt"))
  |> Symtab.update_new (ln, (Prefix, "ln"))
  |> Symtab.update_new (arcsin, (Prefix, "arcsin"))
  |> Symtab.update_new (arccos, (Prefix, "arccos"))
  |> Symtab.update_new (arctan, (Prefix, "arctan"))
  |> Symtab.update_new (exp, (Prefix, "exp"))
  |> Symtab.update_new (cos, (Prefix, "cos"))
  |> Symtab.update_new (sin, (Prefix, "sin"))
  |> Symtab.update_new (tan, (Prefix, "tan"))

  |> Symtab.update_new (max, (Prefix, "max"))
  |> Symtab.update_new (min, (Prefix, "min"))

  |> Symtab.update_new (zero, (NoArgs, "0"))
  |> Symtab.update_new (one, (NoArgs, "1"))
  |> Symtab.update_new (pi, (NoArgs, "pi"))
  (*Also support cbrt and nthroot and log but they are hardcoded in atp_term_to_tptp*)


fun atp_number_to_int (atp_term : (string, string ATP_Problem.atp_type) ATP_Problem.atp_term) : int =
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
  | ATP_Problem.ATerm ((name, _), _) => error ("Not an atp number " ^ name)
  | _ => error "Not an atp_term ATerm"
  )

fun atp_numeral_to_int (atp_term : (string, string ATP_Problem.atp_type) ATP_Problem.atp_term)
    : string =
    (case atp_term of
      ATP_Problem.ATerm (("Num.numeral_class.numeral", _), [arg]) =>
        string_of_int (atp_number_to_int arg)   
    | _ => error "Not an atp numeral"
    )

fun atp_term_to_tptp (atp_term : (string, string ATP_Problem.atp_type) ATP_Problem.atp_term) : string = 
  (case atp_term of

    (*Translating the nth root.*)
    ATP_Problem.ATerm (("NthRoot.root", _), [arg1, arg2]) =>
      (*Fix: name of tptp root functions shouldn't be hardcoded here*)
      (case atp_numeral_to_int arg1 of
        "3" => "cbrt(" ^ (atp_term_to_tptp arg2) ^ ")"
      | n => "nthrt(" ^ n ^ ", " ^ (atp_term_to_tptp arg2) ^ ")"
      )

    (*Translating the log base 2 function. Fix: shouldn't be hardcoded here*)
  | ATP_Problem.ATerm (("Transcendental.log", _), [arg1, arg2]) =>
      (case atp_numeral_to_int arg1 of
        "2" => "log(" ^ (atp_term_to_tptp arg2) ^ ")"
      | _ => error "This is not a base two logarithm."
      )

    (*Translating natural numbers. Rational numbers are translated as fractions*)
  | ATP_Problem.ATerm (("Num.numeral_class.numeral", _), [_]) =>
      atp_numeral_to_int atp_term     

  | ATP_Problem.ATerm ((name, _), []) => 
      (case Symtab.lookup isabelle_to_infix_tptp_name name of
        NONE => name
      | SOME (NoArgs, tptp_name) => tptp_name
      | _ => error "Atp_term doesn't have any argumets but name_type is not NoArgs"
      )
  | ATP_Problem.ATerm ((name, _), arg1::args) =>
      (case Symtab.lookup isabelle_to_infix_tptp_name name of
        NONE => error ("Unknown tptp name for " ^ name ^ " operator")
      | SOME (Infix, tptp_name) =>
          (case args of
            (*Enclose all infix operators in parantheses to ensure correct precedence. 
              Metitarski doesn't like parantheses around multiplications and less/greater in CNF*)
            [arg2] => "(" ^ (atp_term_to_tptp arg1) ^ " " ^ tptp_name ^ " " ^ (atp_term_to_tptp arg2) ^ ")"
          | _ => error ("Infix operator " ^ name ^ " has incorrect number of argments")
          )
      | SOME (Prefix, tptp_name) =>
          let
            fun to_tptp_arg arg = "," ^ (atp_term_to_tptp arg) ^ " "
          in
            tptp_name ^ "(" ^ (atp_term_to_tptp arg1) ^ (String.concat (List.map to_tptp_arg args))  ^ ")"
          end
      | SOME (Unary, tptp_name) =>
          (case args of
            [] => "(" ^ tptp_name ^ (atp_term_to_tptp arg1) ^ ")"
          | _ => error ("Unary operator " ^ tptp_name ^ " has incorrect number of arguments.")
          )
      | _ => error ("Operator " ^ name ^ " has arguments but the name_type is NoArgs.")
      )
  | _ => error "Malformed atp_term"
  )

fun atp_formula_to_tptp (atp_formula 
  : (string, string ATP_Problem.atp_type, 
     (string, string ATP_Problem.atp_type) ATP_Problem.atp_term, string) ATP_Problem.atp_formula)
  : string = 
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
  )

fun atp_problem_to_tptp (atp_problem : (string * string ATP_Problem.atp_problem_line list) list) 
    : string =
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
  end

end;