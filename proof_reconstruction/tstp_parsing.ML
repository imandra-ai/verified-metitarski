structure String_Redirect = ATP_Proof_Redirect(
  type key = ATP_Proof.atp_step_name
  val ord = fn ((s, _ : string list), (s', _)) => fast_string_ord (s, s')
  val string_of = fst)

open ATP_Util;
open ATP_Proof_Reconstruct;
open String_Redirect;
open Sledgehammer_Isar_Proof;
open Sledgehammer_Proof_Methods;

    
let (*Parse the tstp string into the atp_proof datatype. The first argument, "problem", is not really needed.*)
    val atp_proof = ATP_Satallax.atp_proof_of_tstplike_proof "1" [("2", [ATP_Problem.Class_Decl("3", "4", [])])] 
                        (TSTP_Input.read "Documents/internship/verified-metitarski/problems/cristina-problem-6.tstpout")

    val bot = #1 (List.last atp_proof)


    val conjs =
              map_filter (fn (name, role, _, _, _) =>
                  if member (op =) [ATP_Problem.Conjecture, ATP_Problem.Negated_Conjecture] role then SOME name else NONE)
                atp_proof

    (*Construct the refutation graph from the atp_proof datastructure*)
    val refute_graph = (atp_proof
                              |> map (fn (name, _, _, _, from) => (from, name))
                              |> make_refute_graph bot
                              |> fold (Atom_Graph.default_node o rpair ()) conjs
                       )
    
    val axioms = axioms_of_refute_graph refute_graph conjs

    val tainted = tainted_atoms_of_refute_graph refute_graph conjs

    (*Redirect the refutation graph*)
    val direct_graph = redirect_graph axioms tainted bot refute_graph

(*----------My function to transform a direct_proof into an isar_proof----------*)

    (*Transform a clause to a term. Type error in the steps function. Why?*)
(*    val tainted = tainted_atoms_of_refute_graph refute_graph conjs
    val is_clause_tainted = exists (member (op =) tainted)

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
        atp_proof

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
*)

    fun my_isar_steps accum ([] : direct_proof) = rev accum
       
       |my_isar_steps accum (Have (id, (gamma, c)) :: infs) =
            (Prove([Then], [], ("bla", 0), (prop_of_clause c), [], gamma, [Metis_Method (NONE, NONE)],"")) :: accum

       |my_isar_steps accum _ = accum
            

    fun my_isar_proof direct_proof = 
        Proof([], [], (my_isar_steps [] direct_proof))
    
in
    (*string_of_refute_graph refute_graph;*)
    string_of_direct_proof direct_graph
end;

