theory GenerateATP
  imports Main Real
begin
  
declare[[ML_print_depth=50]]   
  
lemma foo: "\<forall>X Y .\<exists> Z. \<not> Z = (1::real) \<and> less_eq 0 (times (minus X 1::real) (minus X 1))"  
  sorry
   

ML\<open>
fun traverse ctxt t args =
  (case (t, args) of
    (t1 $ t2, _) => traverse ctxt t1 (t2 :: args)
  | (Abs (s, T, t'), []) => Abs (s, T, traverse ctxt t' [])
  | (Abs _, _) => error "Term not beta-normalized"
  | (@{const one_class.one (real)}, []) => (warning "1"; t)
  | _ =>
    (warning (Syntax.string_of_term ctxt t ^ "(" ^ commas (map (Syntax.string_of_term ctxt) args)  ^ ")");
     betapplys (t, args)));
\<close>  
  
ML\<open>
fun traverse' ctxt t =
  traverse ctxt (Envir.beta_norm t) [];

traverse' @{context} @{term "f a b (g c) (h (g (1::real)))"}
\<close>  

  
ML\<open>
val theorem = Thm.concl_of @{thm foo};
\<close>  
  

ML\<open>
(*Fix types*)
fun atp_term_of_term ctxt args t =
  (case (t, args) of
    (t1 $ t2, _) => atp_term_of_term ctxt (t2 :: args) t1

(*This is never used
  | (Abs (s, _, t'), []) => ATP_Problem.AAbs (((s, ATP_Problem.AType (("real", []), [])), atp_term_of_term ctxt [] t'), [])
  | (Abs _, _) => error "Term not beta-normalized"
*)
  | (Const (name, _), ls) => ATP_Problem.ATerm ((name, []), map (atp_term_of_term ctxt []) ls)

(*Fix bound variables*)
  | (Bound i, ls) => ATP_Problem.ATerm (("bound."^(string_of_int i), []), map (atp_term_of_term ctxt []) ls)

(*Not dealing with free and schematic variables Free and Var*)
  | _ => error (Syntax.string_of_term ctxt t ^ "(" ^ commas (map (Syntax.string_of_term ctxt) args)  ^ ")")
  );

(*Need to support numbers greater than 1 *)
fun atp_formula_of_term ctxt t =
  (case t of
    t1 $ t2 $ t3 =>
      (case t1 of
        (Const ("HOL.conj", _)) => ATP_Problem.AConn (ATP_Problem.AAnd, [atp_formula_of_term ctxt t2, atp_formula_of_term ctxt t3])
      | (Const ("HOL.disj", _)) => ATP_Problem.AConn (ATP_Problem.AOr, [atp_formula_of_term ctxt t2, atp_formula_of_term ctxt t3])
      | (Const ("HOL.implies", _)) => ATP_Problem.AConn (ATP_Problem.AImplies, [atp_formula_of_term ctxt t2, atp_formula_of_term ctxt t3])

      |  _ => ATP_Problem.AAtom (atp_term_of_term ctxt [] t)
      ) 

  | t1 $ t2 =>
      (case t1 of
        (Const ("HOL.Trueprop", @{typ "bool\<Rightarrow>prop"})) => atp_formula_of_term ctxt t2
      | (Const ("HOL.All", _)) =>
          (case t2 of 
            (Abs (var, _, t3)) =>  ATP_Problem.AQuant (ATP_Problem.AForall, [(var, SOME (ATP_Problem.AType (("real", []), [])))], atp_formula_of_term ctxt t3)
          |  _ => error ("Error in:" ^ Syntax.string_of_term ctxt t)
          )
      | (Const ("HOL.Ex", _)) =>
          (case t2 of 
            (Abs (var, _, t3)) =>  ATP_Problem.AQuant (ATP_Problem.AExists, [(var, SOME (ATP_Problem.AType (("real", []), [])))], atp_formula_of_term ctxt t3)
          |  _ => error ("Error in:" ^ Syntax.string_of_term ctxt t)
          )

      | (Const ("HOL.Not", _)) => ATP_Problem.AConn (ATP_Problem.ANot, [atp_formula_of_term ctxt t2])

      |  _ => ATP_Problem.AAtom (atp_term_of_term ctxt [] t)
      )

  | _ => ATP_Problem.AAtom (atp_term_of_term ctxt [] t)
  );


fun fix_bound_vars bound_vars atp_formula = 
  let 
    fun replace_bound_vars bound_vars atp_term = 
      (case atp_term of 
        ATP_Problem.ATerm ((name, ty), args) => 
          if String.isPrefix "bound." name then 
            let val index_option = Int.fromString (String.extract (name, (String.size "bound."), NONE))
                val index = (case index_option of
                              NONE => error "Invalid index of bound variable"
                            | SOME i => i
                            )  
            in
              ATP_Problem.ATerm ((List.nth (bound_vars, index), ty), map (replace_bound_vars bound_vars) args)
            end
          else
            ATP_Problem.ATerm ((name, ty), map (replace_bound_vars bound_vars) args)
      
      (*Not dealing with ATP_Problem.AAbs*)
      | _ => atp_term
      );
  in
    (case atp_formula of
      ATP_Problem.AQuant (q, ls, phi) =>
        (case ls of
          [] => ATP_Problem.AQuant (q, ls, fix_bound_vars bound_vars phi)
        | [(var, _)] => ATP_Problem.AQuant (q, ls, fix_bound_vars (var::bound_vars) phi)
        (*There can only ever be one variable bound by each quantifier*)
        | _ => atp_formula
        )
    | ATP_Problem.AConn (conn, phis) =>
        ATP_Problem.AConn (conn, map (fix_bound_vars bound_vars) phis)
    | ATP_Problem.AAtom tm => ATP_Problem.AAtom (replace_bound_vars bound_vars tm)

    (*Not supporting type quantifiers ATyQuant*)
    | _ => atp_formula
    )
  end;

fix_bound_vars [] (atp_formula_of_term @{context} (Envir.beta_norm theorem));

\<close>
    
end
  