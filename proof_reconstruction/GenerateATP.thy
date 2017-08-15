theory GenerateATP
  imports Main Real Complex_Main
begin
  
declare[[ML_print_depth=50]]   
  
(*For the cube root use "root 3"*)
(*^ only allows natural numbers powers. Does MT allow any exponent?*)  
lemma foo: "\<forall>(X::real) (Y::real).\<forall> (Z::real).(\<not>(4.3 = min Z X) \<longrightarrow> 0 <= abs (Y ^ 3)) "  
(*apply(atomize)*)
  sorry
  
lemma foo_metalevel: "0\<le>(X::real) \<Longrightarrow> 0\<le> X^2"
  sorry 
  
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
(*Need to deal with the case MT gives up*)
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
    |> Symtab.update_new ("pow", (ATP_Problem_to_tptp.powr, @{typ "real\<Rightarrow>real\<Rightarrow>real"}))

    (*Greater, greater than: MT always replaces these with less*)
    (*not_eq translated to not and eq by ATP_Satallax.atp_proof_of_tstplike_proof*)
    |> Symtab.update_new ("less", (ATP_Problem_to_tptp.less, @{typ "real\<Rightarrow>real\<Rightarrow>bool"}))
    |> Symtab.update_new ("less_equal", (ATP_Problem_to_tptp.less_eq, @{typ "real\<Rightarrow>real\<Rightarrow>bool"}))
    |> Symtab.update_new ("equal", (ATP_Problem_to_tptp.eq, @{typ "real\<Rightarrow>real\<Rightarrow>bool"}))
    
    |> Symtab.update_new ("abs", (ATP_Problem_to_tptp.abs, @{typ "real\<Rightarrow>real"}))
    |> Symtab.update_new ("sqrt", (ATP_Problem_to_tptp.sqrt, @{typ "real\<Rightarrow>real"}))
    |> Symtab.update_new ("ln", (ATP_Problem_to_tptp.ln, @{typ "real\<Rightarrow>real"}))
    |> Symtab.update_new ("arcsin", (ATP_Problem_to_tptp.arcsin, @{typ "real\<Rightarrow>real"}))
    |> Symtab.update_new ("arccos", (ATP_Problem_to_tptp.arccos, @{typ "real\<Rightarrow>real"}))
    |> Symtab.update_new ("arctan", (ATP_Problem_to_tptp.arctan, @{typ "real\<Rightarrow>real"}))
 
    |> Symtab.update_new ("exp", (ATP_Problem_to_tptp.exp, @{typ "real\<Rightarrow>real"}))
    |> Symtab.update_new ("cos", (ATP_Problem_to_tptp.cos, @{typ "real\<Rightarrow>real"}))
    |> Symtab.update_new ("sin", (ATP_Problem_to_tptp.sin, @{typ "real\<Rightarrow>real"}))
    |> Symtab.update_new ("tan", (ATP_Problem_to_tptp.tan, @{typ "real\<Rightarrow>real"}))

    |> Symtab.update_new ("max", (ATP_Problem_to_tptp.max, @{typ "real\<Rightarrow>real\<Rightarrow>real"}))
    |> Symtab.update_new ("min", (ATP_Problem_to_tptp.min, @{typ "real\<Rightarrow>real\<Rightarrow>real"}))

    |> Symtab.update_new ("0", (ATP_Problem_to_tptp.zero, @{typ "real"}))
    |> Symtab.update_new ("1", (ATP_Problem_to_tptp.one, @{typ "real"}))
    |> Symtab.update_new ("pi", (ATP_Problem_to_tptp.pi, @{typ "real"}))
 
    (*Not supported in atp_problem_to_tptp*)
    |> Symtab.update_new ("$false", ("HOL.False", @{typ "bool"}))

fun fix_bound_vars_atp_term (var_list : string list)
                            (atp_term 
  : (string, string ATP_Problem.atp_type) ATP_Problem.atp_term) = 
  let
    fun get_index list element acc =
      (case list of
        [] => NONE
      | l::ls => if l=element then SOME acc
                 else get_index ls element (acc+1)
      ) 
  in
    (case atp_term of
      ATP_Problem.ATerm ((name, ty), []) =>
        (case get_index var_list name 0 of
          NONE => atp_term
        | SOME index => ATP_Problem.ATerm (("bound." ^ (string_of_int index), ty), [])
        ) 
    | ATP_Problem.ATerm ((name, ty), args) =>
        ATP_Problem.ATerm ((name, ty), List.map (fix_bound_vars_atp_term var_list) args)

    (*Not supporting the AAbs atp_term*)
    | _ => error "Invalid atp_term in atp_proof."
    )
  end

fun fix_bound_vars_atp_formula (var_list : string list)
                               (atp_formula 
  : (string, string, (string, string ATP_Problem.atp_type) ATP_Problem.atp_term, 
     string) ATP_Problem.atp_formula) =

  (case atp_formula of
    ATP_Problem.AQuant (quantifier, binder_list, phi) =>
      ATP_Problem.AQuant (quantifier, binder_list, 
        (fix_bound_vars_atp_formula (List.foldl (fn ((var, _), var_list) => var::var_list) var_list binder_list) phi))
  | ATP_Problem.AConn (conn, phis) =>
      ATP_Problem.AConn (conn, List.map (fix_bound_vars_atp_formula var_list) phis)
  | ATP_Problem.AAtom atp_term => ATP_Problem.AAtom (fix_bound_vars_atp_term var_list atp_term)

  (*Not supporting ATyQunat*)
  | _ => error "Invalid atp_formula in atp_proof."
  )

(*Will this work for the large numbers MT uses?! 
  It takes very long when working with the approximations of pi*)
fun num_of_int (i : int) : term =
  let
    fun inc (num : term) : term =
      (case num of
        Const ("Num.num.One", @{typ "num"}) => Const ("Num.num.Bit0", @{typ "num \<Rightarrow> num"}) $ num
      | Const ("Num.num.Bit0", @{typ "num \<Rightarrow> num"}) $ x => Const ("Num.num.Bit1", @{typ "num \<Rightarrow> num"}) $ x
      | Const ("Num.num.Bit1", @{typ "num \<Rightarrow> num"}) $ x => Const ("Num.num.Bit0", @{typ "num \<Rightarrow> num"}) $ (inc x)
      | _ => error "The term is not a valid numeral."
      )

    fun num_of_int_tail_rec (i : int) (acc : term) : term = 
      (case i of
        1 => acc
      | n => if n>1 then num_of_int_tail_rec (n-1) (inc acc)
             else error ("This number cannot be converted to a numeral: " ^ (string_of_int i))
      )
  in
    num_of_int_tail_rec i (Const ("Num.num.One", @{typ "num"}))
  end
  
(*Made type of all Free variables real*)
fun atp_term_to_term (atp_term : (string, string ATP_Problem.atp_type) ATP_Problem.atp_term) 
  : term =
  (case atp_term of
    ATP_Problem.ATerm ((name, _), args) =>
      (case Symtab.lookup tptp_prefix_name_to_isabelle name of
        NONE => if args=[] then 
                  if String.isPrefix "bound." name
                  then 
                    let val index = String.extract (name, (String.size "bound."), NONE)
                    in
                      (case Int.fromString index of
                        SOME i => Bound i
                      | NONE => error ("Invalid bound variable index: " ^ index)
                      )
                    end
                  else
                    (case Int.fromString name of
                      SOME i => Const ("Num.numeral_class.numeral", @{typ "num \<Rightarrow> real"}) $ (num_of_int i)
                    | NONE => Free (name, @{typ real})
                    )
                else error ("Unsupported tptp operator: " ^ name)
      | SOME (isa_name, ty) =>
          (*Need to handle the case of natural powers separately 
            because the type of the exponent needs to be nat not real*)
          if isa_name = ATP_Problem_to_tptp.power andalso List.length args = 2 
          then
            (case atp_term_to_term (List.last args) of
              Const ("Num.numeral_class.numeral", @{typ "num \<Rightarrow> real"}) $ x => 
                Const (isa_name, ty) $ (atp_term_to_term (List.hd args)) $ 
                  (Const ("Num.numeral_class.numeral", @{typ "num \<Rightarrow> nat"}) $ x)
            | _ => error "Invalid natural exponent"
            )
          else  
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
    (*Need to handle multiple variables being quantified over simultaneously*)
    ATP_Problem.AQuant (quantifier, binder_list, phi) =>
      let
        val quant_string =
          (case quantifier of
            ATP_Problem.AForall => "HOL.All"
          | ATP_Problem.AExists => "HOL.Ex"
          )
      in
        List.foldr 
          (fn ((var, _), term) => (Const (quant_string, @{typ  "(real \<Rightarrow> bool) \<Rightarrow> bool"}) $ Abs (var, @{typ "real"}, term))) 
          (atp_formula_to_term phi) 
          binder_list
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
      (name, role, wrap_term (atp_formula_to_term (fix_bound_vars_atp_formula [] phi)), rule, from)
  in
    List.map termify_atp_proof_line atp_proof
  end;

termify_atp_proof atp_proof;
\<close>  
  
end
  