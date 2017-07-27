structure String_Redirect = ATP_Proof_Redirect(
  type key = ATP_Proof.atp_step_name
  val ord = fn ((s, _ : string list), (s', _)) => fast_string_ord (s, s')
  val string_of = fst)

open ATP_Util;
open ATP_Proof_Reconstruct;
open String_Redirect;
open Sledgehammer_Isar_Proof;
open Sledgehammer_Proof_Methods;

    
let 
    (*Parse the tstp string into the atp_proof datatype. The first argument, "problem", is not really needed.*)
    val atp_proof = ATP_Satallax.atp_proof_of_tstplike_proof "1" [("2", [ATP_Problem.Class_Decl("3", "4", [])])] 
                        (TSTP_Input.read "Documents/internship/verified-metitarski/problems/cristina-problem-2.tstpout")



    (*Remove the "strip" and "subgoal_0" step because they confuse the redirection algorithm. 
      The clause derived by strip is not really part of the proof.*)

    (*Remove the clause derived by strip*)
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

   
    (*Replace "1" with "Groups.one_class.one"*)
    fun replace1_term (ATP_Problem.ATerm ((name, ls), args)) : (string, 'a) ATP_Problem.atp_term = 
            if name = "1" then ATP_Problem.ATerm (("Groups.one_class.one", ls), map replace1_term args)
            else ATP_Problem.ATerm ((name, ls), map replace1_term args)
       |replace1_term (ATP_Problem.AAbs ((x, term), terms)) =
            ATP_Problem.AAbs ((x, replace1_term term), map replace1_term terms)

    fun replace1_formula (ATP_Problem.ATyQuant (quant, vars, formula)) =
            ATP_Problem.ATyQuant (quant, vars, replace1_formula formula)
       |replace1_formula (ATP_Problem.AQuant (quant, vars, formula)) = 
            ATP_Problem.AQuant (quant, vars, replace1_formula formula)
       |replace1_formula (ATP_Problem.AConn (conn, fs)) = 
            ATP_Problem.AConn (conn, map replace1_formula fs)
       |replace1_formula (ATP_Problem.AAtom term) = ATP_Problem.AAtom (replace1_term term)


    val atp_proof = 
        atp_proof
            |>remove_strip []
            |>replace_from [] conjecture_name
(*            |> map (fn (name, role, formula, rule, from) => 
                    (name, role, replace1_formula formula, rule, from))
*)


   
    fun choose_type_enc strictness best_type_enc format =
      the_default best_type_enc
      #> ATP_Problem_Generate.type_enc_of_string strictness
      #> ATP_Problem_Generate.adjust_type_enc format

    (*Translate some of the tstp prefix operations to Isabelle*)
    val pool = Symtab.empty
                |> Symtab.update_new ("multiply", "times" (*"c_Groups.times_class.times"*))     (*t_ for type comstant *)
                |> Symtab.update_new ("add", "plus" (*"c_Groups.plus_class.plus"*))
                |> Symtab.update_new ("subtract", "minus" (*"c_Groups.minus_class.minus"*))
                |> Symtab.update_new ("neg", "uminus" (*"c_Groups.uminus_class.uminus"*))
                |> Symtab.update_new ("less_equal", "less_eq" (*"c_Orderings.ord_class.less_eq"*))
                |> Symtab.update_new ("0", "c_Groups.zero_class.zero")
                |> Symtab.update_new ("1", "c_Groups.one_class.one")    (*c_ prefix from ATP_Proof_Reconstruct.do_term*)                
(*                |> Symtab.update_new ("2", "c_Groups.two_class.two")  *)

    (*Termify atp_proof and factify*)
    val termified_atp_proof = 
        atp_proof 
            |> termify_atp_proof 
                @{context} 
                "" (*local prover name*)
                ATP_Problem.FOF (*format*)
                (choose_type_enc ATP_Problem_Generate.Strict "mono_native" (*from ATP_Problem_Generate.type_enc_of_string*) ATP_Problem.FOF NONE (*?*)) (*type encoding*)
                pool (*Symtab.empty ? pool*)
                [] (*? lifted*) 
                Symtab.empty (*? sym_tab*)
(*            |> factify_atp_proof (map fst []) hyp_ts concl_t  *)



    (*Change all free type variables to real*)
    fun to_real_types (Type (tname, tys)) = Type (tname, (map to_real_types tys))
       |to_real_types (TFree (tname, s)) = Type ("Real.real", [])
       |to_real_types (TVar (index, s)) = TVar (index, s)

    fun to_real_term (Const (name, ty)) = Const (name, to_real_types ty)

        |to_real_term (Free (name, ty)) = Free(name, to_real_types ty)
            
        |to_real_term (Var (index, ty)) =  Var (index, to_real_types ty)

        |to_real_term (Bound i) = Bound i 

        |to_real_term (Abs (x, ty, t1)) = Abs (x, to_real_types ty, (to_real_term t1))

        |to_real_term (t1 $ t2) = ((to_real_term t1) $ (to_real_term t2))


    (*Change terms 1 from Free to Const*)
(*    fun to_const (Free (name, ty)) = 
        if name = "one" then Const (name, ty)
        else Free (name, ty)
       |to_const (Abs (x, ty, t1)) = Abs (x, ty, to_const t1)
       |to_const (t1 $ t2) = (to_const t1) $ (to_const t2)
       |to_const x = x
*)
    val termified_atp_proof =
        termified_atp_proof
            |> map (fn (name, role, the_term, rule, from) => 
                        (name, role, (to_real_term the_term) (*|> to_const*), rule, from) ) 




    val bot = #1 (List.last termified_atp_proof)

    fun add_line_pass1 (line as (name, role, t, rule, [])) lines =
        if role = ATP_Problem.Axiom then
          lines (* axioms (facts) need no proof lines *)
        else line::lines
      | add_line_pass1 line lines = line :: lines

    val termified_atp_proof =
      fold_rev add_line_pass1 termified_atp_proof []

    val conjs =
              map_filter (fn (name, role, _, _, _) =>
                  if member (op =) [ATP_Problem.Conjecture, ATP_Problem.Negated_Conjecture] role then SOME name else NONE)
                termified_atp_proof

    (*Construct the refutation graph from the atp_proof datastructure*)
    val refute_graph = (termified_atp_proof
                              |> map (fn (name, _, _, _, from) => (from, name))
                              |> make_refute_graph bot
                              |> fold (Atom_Graph.default_node o rpair ()) conjs
                       )
 
    val tainted = tainted_atoms_of_refute_graph refute_graph conjs
    val is_clause_tainted = exists (member (op =) tainted)
   
    val axioms = axioms_of_refute_graph refute_graph conjs

    val tainted = tainted_atoms_of_refute_graph refute_graph conjs

    (*Redirect the refutation graph*)
    val direct_graph = redirect_graph axioms tainted bot refute_graph





    val steps =
      Symtab.empty
      |> fold (fn (name as (s, _), role, t, rule, _) =>
          Symtab.update_new (s, (rule, t
            |> (if is_clause_tainted [name] then
                  HOLogic.dest_Trueprop
                  #> role <> ATP_Problem.Conjecture ? s_not
                  #> fold exists_of (map Var (Term.add_vars t []))
                  #> HOLogic.mk_Trueprop
                else
                  I))))
        termified_atp_proof

    val finish_off = close_form #> rename_bound_vars

    (*Transform the rhs of a sequent into a term*)
    fun prop_of_clause [(num, _)] = Symtab.lookup steps num |> the |> snd |> finish_off
      | prop_of_clause names =
        let
          val lits =
            map (HOLogic.dest_Trueprop o snd) (map_filter (Symtab.lookup steps o fst) names)
        in
          (case List.partition (can HOLogic.dest_not) lits of
            (negs as _ :: _, pos as _ :: _) =>
            s_imp (Library.foldr1 s_conj (map HOLogic.dest_not negs),
              Library.foldr1 s_disj pos)
          | _ => fold (curry s_disj) lits @{term False})
        end
        |> HOLogic.mk_Trueprop |> finish_off



    fun raw_label_of_num num = (num, 0)

    fun label_of_clause [(num, _)] = raw_label_of_num num
      | label_of_clause c = (space_implode "___" (map (fst o raw_label_of_num o fst) c), 0)

    fun add_global_fact ss = apsnd (union (op =) ss)

    fun add_fact_of_dependency [(_, ss as _ :: _)] = add_global_fact ss
      | add_fact_of_dependency names = apfst (insert (op =) (label_of_clause names))


    (*Transform the lhs of a sequent into facts*)
    fun deps gamma = ([], [])
      |> fold add_fact_of_dependency gamma
(*      |> is_maybe_ext_rule rule ? add_global_fact [short_thm_name ctxt ext]   *)(*Probably not need this*)
      |> sort_facts

(*----------My function to transform a direct_proof into an isar_proof----------*)
    fun my_isar_steps _ accum ([] : direct_proof) = rev accum
       
       |my_isar_steps outer accum (Have (id, (gamma, c)) :: infs) =
            let val show_then_have = if null infs then [Show]
                                     else if outer then [] else [Then]

                val label = if null infs then no_label else label_of_clause c

                val prop = prop_of_clause c

(*                fun is_fixed ctxt = Variable.is_declared ctxt orf Name.is_skolem                
                fun skolems_of ctxt t = Term.add_frees t [] |> filter_out (is_fixed ctxt o fst) |> rev
                val skolems = skolems_of @{context} prop
*)
                val skolems = []
            in
                my_isar_steps false ((Prove(show_then_have, skolems, label, prop, [], 
                   (deps gamma) (*gamma - assumptions*), [Auto_Method, Metis_Method (NONE, NONE)],"")) :: accum) infs
            end

       |my_isar_steps outer accum (_ :: infs) = my_isar_steps outer accum infs  (*Not treating the "Cases" case for now*)


    fun get_role keep_role ((num, _), role, t, rule, _) =
      if keep_role role then SOME ((raw_label_of_num num, t), rule) else NONE

    val assms = map_filter (Option.map fst o get_role (curry (op =) ATP_Problem.Hypothesis)) termified_atp_proof
            
    fun my_isar_proof fix assms infs =
        Proof (fix, assms, (my_isar_steps true [] infs))

    val the_isar_proof = my_isar_proof [] assms direct_graph
    
in
    (*atp_proof*)
    termified_atp_proof
    (*string_of_refute_graph refute_graph*)
    (*string_of_direct_proof direct_graph*)
    (*the_isar_proof*)
    (*string_of_isar_proof @{context} 1 1 the_isar_proof*)
end;

