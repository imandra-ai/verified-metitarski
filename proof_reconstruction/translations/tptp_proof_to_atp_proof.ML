signature TPTP_PROOF_TO_ATP_PROOF =
sig
  val tptp_proof_to_atp_proof : 
    string ATP_Problem.atp_problem -> string -> string ATP_Proof.atp_proof (*(ATP_Proof.atp_step_name * ATP_Problem.atp_formula_role *
    (string, string, (string, string ATP_Problem.atp_type) ATP_Problem.atp_term, string) ATP_Problem.atp_formula * string * (string * string list) list
   )
   list*)
end;

structure TPTP_Proof_to_atp_proof : TPTP_PROOF_TO_ATP_PROOF =
struct

fun tptp_proof_to_atp_proof (atp_problem : string ATP_Problem.atp_problem) (tptp_proof : string) 
  : string ATP_Proof.atp_proof =
  let

    (*Remove cnf axioms*)
    val trimmed_tptp_proof : string = 
      if String.isSubstring "GaveUp" tptp_proof 
      then raise Fail "Metitarski gave up."  (*To deal with a failed proof*)
      else Substring.position "fof" (CharVectorSlice.full tptp_proof)
            |> #2
            |> CharVectorSlice.vector;
    
    (*Use translation from Isabelle/src/HOL/Tools/ATP*)
    val atp_proof = ATP_Satallax.atp_proof_of_tstplike_proof "1" atp_problem trimmed_tptp_proof
    
    (*Remove the clause derived by strip=subgoal_0 and the Axioms*)
    fun remove_strip accum [] = rev accum
       |remove_strip accum ((step as (_, role, _, rule, _))::proof) =   
            if rule = "strip" orelse role = ATP_Problem.Axiom 
            then remove_strip accum proof
            else remove_strip (step::accum) proof
    
    (*Clauses derived from subgoal_0 now derived from original goal*)
    fun replace_from accum _ [] = rev accum
       |replace_from accum name'' ((name, role, t, rule, from)::proof) = 
            let val from' = map (fn (name',ls) => if name' = "subgoal_0" then (name'', ls) else (name',ls)) from
            in replace_from ((name, role, t, rule, from')::accum) name'' proof
            end
    
    val conjecture_name = 
      (#1 (#1 (hd atp_proof)))
          handle Empty => 
            let
             (*To handle a weird thing that tactic does*)
             val message = (case atp_problem of
                            [(_, [ATP_Problem.Formula (_, _, ATP_Problem.AAtom (ATP_Problem.ATerm (("Pure.dummy_pattern", [ATP_Problem.AType (("prop", []), [])]), [])), _, _)])] =>
                              "toplevel term is Pure.dummy_pattern"
                           | _ => ""
                           )
            in
              if message = ""
              then raise Fail ("The parsed atp_proof is empty: " ^ message)
              else ""
            end
    
    val atp_proof = 
        atp_proof
            |>remove_strip []
            |>replace_from [] conjecture_name
  in
    atp_proof
  end

end;