signature TERMIFIED_ATP_PROOF_TO_ISAR =
sig

val termified_atp_proof_to_isar : (term, string) ATP_Proof.atp_step list -> string

end;

structure Termified_atp_proof_to_isar : TERMIFIED_ATP_PROOF_TO_ISAR =
struct

structure String_Redirect = ATP_Proof_Redirect(
  type key = ATP_Proof.atp_step_name
  val ord = fn ((s, _ : string list), (s', _)) => fast_string_ord (s, s')
  val string_of = fst)

open String_Redirect;
open ATP_Util;
open ATP_Proof_Reconstruct;
open Sledgehammer_Isar_Proof;
open Sledgehammer_Proof_Methods;

(*Code adapted from Sledgehammer.*)
fun termified_atp_proof_to_isar (termified_atp_proof : (term, string) ATP_Proof.atp_step list) 
    : string =
    let
      val bot = #1 (List.last termified_atp_proof)

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
         
         |my_isar_steps outer accum (Have (_, (gamma, c)) :: infs) =
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
                     (deps gamma) (*gamma - assumptions*), [Auto_Method(*, Metis_Method (NONE, NONE)*)],"")) :: accum) infs
              end
  
         |my_isar_steps outer accum (_ :: infs) = my_isar_steps outer accum infs  (*Not treating the "Cases" case for now*)
  
  
      fun get_role keep_role ((num, _), role, t, rule, _) =
        if keep_role role then SOME ((raw_label_of_num num, t), rule) else NONE
  
      val assms = map_filter (Option.map fst o get_role (curry (op =) ATP_Problem.Hypothesis)) termified_atp_proof
              
      fun my_isar_proof fix assms infs =
          Proof (fix, assms, (my_isar_steps true [] infs))
  
      val the_isar_proof = my_isar_proof [] assms direct_graph

    in 
      (*string_of_isar_proof @{context} 1 1 the_isar_proof*)
      string_of_direct_proof direct_graph
    end

end;