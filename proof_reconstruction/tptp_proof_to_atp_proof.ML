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
    (*Remove axioms*)
    val trimmed_tptp_proof : string = 
      Substring.position "fof" (CharVectorSlice.full tptp_proof)
        |> #2
        |> CharVectorSlice.vector;
    
    (*Use translation from Isabelle/src/HOL/Tools/ATP*)
    val atp_proof = ATP_Satallax.atp_proof_of_tstplike_proof "1" atp_problem trimmed_tptp_proof
    
    (*Remove the clause derived by strip=subgoal_0*)
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
    
    val atp_proof = 
        atp_proof
            |>remove_strip []
            |>replace_from [] conjecture_name
  in
    atp_proof
  end

end;