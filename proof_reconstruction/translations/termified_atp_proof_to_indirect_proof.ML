signature TERMIFIED_ATP_PROOF_TO_INDIRECT_PROOF =
sig

val termified_atp_proof_to_indirect_proof 
  : (term, string) ATP_Proof.atp_step list -> Proof.context -> string * string

end

structure Termified_atp_proof_to_indirect_proof =
struct

fun termified_atp_proof_to_indirect_proof (ctxt : Proof.context) (termified_proof 
  : (term, string) ATP_Proof.atp_step list)
  : string * string =
  let
    fun term_to_string (ctxt : Proof.context) (term : term) : string =
      let
        val ctxt_with_types = Config.put show_types true ctxt
        val pretty_string = 
          (ML_Pretty.format_polyml ML_Pretty.default_margin (Pretty.to_polyml  (Syntax.unparse_term ctxt_with_types term)))
      in
        (*Delete the new line at the end of the term string.*)
        String.extract (pretty_string, 0, (SOME (String.size pretty_string -1)))
      end

    val proof_method = "proof(rule ccontr)\n"
    val qed = "qed"

    (*The assumption*)
    fun assumption ((name, _), _, term, _, _) =
      ("   assume " ^ name ^ ": \"" ^ (term_to_string ctxt term) ^ "\"\n\n")

    (*The lemma we are trying to prove*)
    fun lemma_statement ((name, _), _, term, _, _) =
      ("lemma " ^ name ^ ": \"" ^ (term_to_string ctxt term) ^ "\"\n\n")

    (*Transform each proof line in a have clause*)
    fun isar_proof_line (last_line : bool) ((name, _), _, term, rule, (premises : ATP_Proof.atp_step_name list)) =
      let
        val keyword = if last_line then "then show " else "have "
        val prop_line = "   " ^ keyword ^ name ^ ": \"" ^ (term_to_string ctxt term) ^ "\"\n"
        val prems_line = 
          (case premises  of
            [] => ""
          | _::_ =>
              let
                fun concat (str1, str2) = str1 ^ " " ^ str2
                val premises_proj = List.map (fn (a, _) => a) premises
              in
                "using " ^ (List.foldr concat "" premises_proj)
              end
          )

        (*Sorry everything for now*)
        val proof_method = "sorry\n\n" (*" by auto\n\n"*) (*Don't forget the newline!*)
        val indent = "       "
      in
        prop_line ^ indent ^ prems_line ^ proof_method
      end 
  in
    (case termified_proof of
      conjecture::(line as ((name, _), _, _, _, _))::proof_lines => 
        if String.isPrefix "negate" name then
          let
            fun string_of_proof_lines lines =
              (case lines of
                [l] => isar_proof_line true l
              | l::ls => (isar_proof_line false l) ^ (string_of_proof_lines ls)
              | [] => error "There are no proof lines after the negated conjecture."
              )
          in
            ( lemma_statement conjecture,
              proof_method ^
              assumption line ^
              (string_of_proof_lines proof_lines) ^
              qed
            )
          end
        else error "Invalid termified proof: doesn't have the negated conjecture as the second proof line"
    | _ => error "The termified proof has less than two lines."
    )
  end

end;