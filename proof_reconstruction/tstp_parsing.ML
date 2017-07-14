structure String_Redirect = ATP_Proof_Redirect(
  type key = ATP_Proof.atp_step_name
  val ord = fn ((s, _ : string list), (s', _)) => fast_string_ord (s, s')
  val string_of = fst)

open String_Redirect;

    
let (*Parse the tstp string into the atp_proof datatype*)
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
in
    (*string_of_refute_graph refute_graph;*)
    string_of_direct_proof direct_graph
end;

