signature TERMIFY_ATP_PROOF =
sig
  val termify_atp_proof : string ATP_Proof.atp_proof -> (term, string) ATP_Proof.atp_step list
end;

structure Termify_atp_proof : TERMIFY_ATP_PROOF =
struct

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
 
    |> Symtab.update_new ("cbrt", (ATP_Problem_to_tptp.nthrt, @{typ "nat \<Rightarrow> real \<Rightarrow> real"}))
    |> Symtab.update_new ("nthrt", (ATP_Problem_to_tptp.nthrt, @{typ "nat \<Rightarrow> real \<Rightarrow> real"}))
    |> Symtab.update_new ("log", (ATP_Problem_to_tptp.log, @{typ "real\<Rightarrow>real\<Rightarrow>real"}))

    (*Not supported in atp_problem_to_tptp*)
    |> Symtab.update_new ("$false", ("HOL.False", @{typ "bool"}))
    |> Symtab.update_new ("lgen", (ATP_Problem_to_tptp.lgen, @{typ "bool \<Rightarrow> real \<Rightarrow> real \<Rightarrow> bool"}))
    |> Symtab.update_new ("interval", (ATP_Problem_to_tptp.interval, @{typ "bool \<Rightarrow> real \<Rightarrow> bool \<Rightarrow> real \<Rightarrow> real \<Rightarrow> bool"}))

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
(*fun num_of_int (i : int) : term =
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
*)
    (*Not tail-recursive*) 
fun num_of_int 1 = Const ("Num.num.One", @{typ "num"})
  | num_of_int n =
      if n>1 then
        (case n mod 2 of
          0 => Const ("Num.num.Bit0", @{typ "num \<Rightarrow> num"}) $ (num_of_int (n div 2))
        | 1 => Const ("Num.num.Bit1", @{typ "num \<Rightarrow> num"}) $ (num_of_int (n div 2))
        | _ => error ("This number cannot be converted to a numeral: " ^ (Int.toString n))
        )
      else error ("This number cannot be converted to a numeral: " ^ (Int.toString n))
    

      (* Tail recursive *)
(*    fun int_to_binary (n : int) : char list =
      let
        fun int_to_binary_aux 0   acc = acc
          | int_to_binary_aux num acc = 
              (case (Char.fromString (String.toString (num mod 2))) of
                SOME c => int_to_binary_aux (num div 2) (c :: acc)
              | NONE => error "Not a binary digit."
              )              
      in
        int_to_binary_aux n []
      end
*)

 
(*Made type of all Free variables real*)
fun atp_term_to_term (atp_term : (string, string ATP_Problem.atp_type) ATP_Problem.atp_term) 
  : term =
  let
    fun power_to_term isa_name ty args : term =
      (case atp_term_to_term (List.last args) of
              Const ("Num.numeral_class.numeral", @{typ "num \<Rightarrow> real"}) $ x => 
                Const (isa_name, ty) $ (atp_term_to_term (List.hd args)) $ 
                  (Const ("Num.numeral_class.numeral", @{typ "num \<Rightarrow> nat"}) $ x)
            | _ => error "Invalid natural exponent"
            )

    fun nthrt_to_term name isa_name ty args : term =
      (case name of
        "cbrt" => 
          Const (isa_name, ty) $ 
            (Const ("Num.numeral_class.numeral", @{typ "num \<Rightarrow> nat"}) $ (num_of_int 3)) $ 
            (atp_term_to_term (List.hd args))
      | "nthrt" =>
        (case atp_term_to_term (List.hd args) of
          Const ("Num.numeral_class.numeral", @{typ "num \<Rightarrow> real"}) $ x => 
            Const (isa_name, ty) $  
              (Const ("Num.numeral_class.numeral", @{typ "num \<Rightarrow> nat"}) $ x) $
              (atp_term_to_term (List.nth (args, 1)))
        | _ => error "Invalid root"
        )
      | _ => error "Unsupported root operator"
    )

    fun log_to_term isa_name ty args : term =
       Const (isa_name, ty) $ 
       (Const ("Num.numeral_class.numeral", @{typ "num \<Rightarrow> real"}) $ (num_of_int 2)) $
       (atp_term_to_term (List.hd args))

    fun lgen_to_term isa_name ty args : term = 
      let val strict = 
        (case List.hd args of 
           ATP_Problem.ATerm(("1", _), _) => Const ("HOL.True", @{typ "bool"}) 
         | ATP_Problem.ATerm(("0", _), _) => Const ("HOL.False", @{typ "bool"})
         | _ => error "Malformed lgen expression"
         )
      in Const (isa_name, ty) $ strict $
         (atp_term_to_term (List.nth (args, 1))) $
         (atp_term_to_term (List.nth (args, 2)))
      end
    
    fun interval_to_term isa_name ty args : term =
      let val strict_left = 
          (case List.hd args of 
             ATP_Problem.ATerm(("1", _), _) => Const ("HOL.True", @{typ "bool"}) 
           | ATP_Problem.ATerm(("0", _), _) => Const ("HOL.False", @{typ "bool"})
           | _ => error "Malformed lgen expression"
           )
          val strict_right = (case List.nth (args, 2) of 
                   ATP_Problem.ATerm(("1", _), _) => Const ("HOL.True", @{typ "bool"}) 
                 | ATP_Problem.ATerm(("0", _), _) => Const ("HOL.False", @{typ "bool"})
                 | _ => error "Malformed lgen expression"
                 )
          in Const (isa_name, ty) $ strict_left $
          (atp_term_to_term (List.nth (args, 1))) $ strict_right $
          (atp_term_to_term (List.nth (args, 3))) $
          (atp_term_to_term (List.nth (args, 4)))
          end
  in
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
            then power_to_term isa_name ty args
  
            (*Need to handle cube and higher roots separately because the root argument has to be nat*)
            else if isa_name = ATP_Problem_to_tptp.nthrt
                 then nthrt_to_term name isa_name ty args
  
                 (*Handle the base two logarithm separately because we need to add the base as an argument*)
                 else if isa_name = ATP_Problem_to_tptp.log andalso List.length args = 1
                      then log_to_term isa_name ty args
  
                      (*Lgen*)
                      else if isa_name = ATP_Problem_to_tptp.lgen andalso List.length args = 3
                           then lgen_to_term isa_name ty args
  
                           (*Interval*)
                           else if isa_name = ATP_Problem_to_tptp.interval andalso List.length args = 5
                                then interval_to_term isa_name ty args
  
                                (*All other operators*)
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
  end

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


(* Transform Free variables to Bound, bound by Pure.All *)
fun bind_free_vars (t : term) : term =
  let
    fun get_index list element acc =
    (case list of
      [] => NONE
    | l::ls => if l=element then SOME acc
               else get_index ls element (acc+1)
    ) 

    val bound_vars : string list Unsynchronized.ref = Unsynchronized.ref []

    fun bind_free_vars_aux (forall_count : int) (t : term) : term =
      (case t of
        Free (name, _) =>
          if String.isPrefix "sko" name then t
          else
            (case get_index (!bound_vars) name 0 of
              NONE => (bound_vars := (name::(!bound_vars));
                       Bound ((List.length (!bound_vars)) - 1 + forall_count)
                      )
            | SOME i => Bound ((List.length (!bound_vars)) - i - 1 + forall_count)
            )

      | t1 $ t2 => (bind_free_vars_aux forall_count t1) $ (bind_free_vars_aux forall_count t2)
          
      | Abs (name, ty, t1) => Abs (name, ty, bind_free_vars_aux (forall_count+1) t1)

      | t1 => t1         
      )

    val renamed_t : term = bind_free_vars_aux 0 t

    fun add_pure_all (bound_list : string list) (t : term) =
      (case bound_list of
        [] => t
      | var::vars => Const ("Pure.all", @{typ "(real \<Rightarrow> prop) \<Rightarrow> prop"}) $
                          Abs (var, @{typ "real"}, add_pure_all vars t)
      )
  in
    add_pure_all (!bound_vars) renamed_t
  end
  

fun termify_atp_proof (atp_proof : string ATP_Proof.atp_proof) 
  : (term, string) ATP_Proof.atp_step list=
  let 
    fun termify_atp_proof_line (name, role, phi, rule, from) =
      (name, role, bind_free_vars (wrap_term (atp_formula_to_term (fix_bound_vars_atp_formula [] phi))), rule, from)
  in
    List.map termify_atp_proof_line atp_proof
  end;


end;