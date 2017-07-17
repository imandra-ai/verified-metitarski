structure String_Redirect = ATP_Proof_Redirect(
  type key = ATP_Proof.atp_step_name
  val ord = fn ((s, _ : string list), (s', _)) => fast_string_ord (s, s')
  val string_of = fst)

open String_Redirect;
open Sledgehammer_Isar_Proof;

    
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

(*---------Producing an isar_proof datatype------------*)
    val (params, _, concl_t) = ATP_Util.strip_subgoal goal subgoal ctxt

    fun massage_methods (meths as meth :: _) =
              if not try0 then [meth]
              else if smt_proofs = SOME true then SMT_Method :: meths
              else meths

    
    fun raw_label_of_num num = (num, 0)

    fun label_of_clause [(num, _)] = raw_label_of_num num
      | label_of_clause c = (space_implode "___" (map (fst o raw_label_of_num o fst) c), 0)

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

    fun isar_steps outer predecessor accum [] =
        accum
        |> (if tainted = [] then
              (* e.g., trivial, empty proof by Z3 *)
              cons (Prove (if outer then [Show] else [], [], no_label, concl_t, [],
                sort_facts (the_list predecessor, []), massage_methods systematic_methods',
                ""))
            else
              I)
        |> rev
      | isar_steps outer _ accum (Have (id, (gamma, c)) :: infs) =
        let
          val l = label_of_clause c
          val t = prop_of_clause c
          val rule = rule_of_clause_id id
          val skolem = is_skolemize_rule rule

          val deps = ([], [])
            |> fold add_fact_of_dependency gamma
            |> is_maybe_ext_rule rule ? add_global_fact [short_thm_name ctxt ext]
            |> sort_facts
          val meths =
            (if skolem then skolem_methods
             else if is_arith_rule rule then arith_methods
             else if is_datatype_rule rule then datatype_methods
             else systematic_methods')
            |> massage_methods

          fun prove sub facts = Prove (maybe_show outer c, [], l, t, sub, facts, meths, "")
          fun steps_of_rest step = isar_steps outer (SOME l) (step :: accum) infs
        in
          if is_clause_tainted c then
            (case gamma of
              [g] =>
              if skolem andalso is_clause_tainted g then
                let
                  val skos = skolems_of ctxt (prop_of_clause g)
                  val subproof = Proof (skos, [], rev accum)
                in
                  isar_steps outer (SOME l) [prove [subproof] ([], [])] infs
                end
              else
                steps_of_rest (prove [] deps)
            | _ => steps_of_rest (prove [] deps))
          else
            steps_of_rest
              (if skolem then
                 (case skolems_of ctxt t of
                   [] => prove [] deps
                 | skos => Prove ([], skos, l, t, [], deps, meths, ""))
               else
                 prove [] deps)
        end
      | isar_steps outer predecessor accum (Cases cases :: infs) =
        let
          fun isar_case (c, subinfs) =
            isar_proof false [] [(label_of_clause c, prop_of_clause c)] [] subinfs
          val c = succedent_of_cases cases
          val l = label_of_clause c
          val t = prop_of_clause c
          val step =
            Prove (maybe_show outer c, [], l, t,
              map isar_case (filter_out (null o snd) cases),
              sort_facts (the_list predecessor, []), massage_methods systematic_methods',
              "")
        in
          isar_steps outer (SOME l) (step :: accum) infs
        end
    and isar_proof outer fix assms lems infs =
      Proof (fix, assms,
        fold_rev insert_lemma_in_steps lems (isar_steps outer NONE [] infs))
(*----------------------------------*)

in
    (*string_of_refute_graph refute_graph;*)
    string_of_direct_proof direct_graph
end;

