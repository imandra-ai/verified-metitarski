let
    fun choose_type_enc strictness best_type_enc format =
      the_default best_type_enc
      #> ATP_Problem_Generate.type_enc_of_string strictness
      #> ATP_Problem_Generate.adjust_type_enc format

    val value as (atp_problem, _, _, _) = ATP_Problem_Generate.generate_atp_problem 
                                              @{context}
                                              false (*generate_info: true only for format = DFG*)
                                              ATP_Problem.FOF   (*atp_format*)
                                              ATP_Problem.Conjecture (*prem_role*)
                                              (choose_type_enc ATP_Problem_Generate.Strict "mono_native" ATP_Problem.FOF NONE) (*type encoding*)
                                              ATP_Problem_Generate.Metis (*mode*)
                                              ATP_Problem_Generate.hide_lamsN (*lam_trans ? *)
                                              true (*uncurried_aliases ? false = the hypothesis and axioms change*)
                                              true (*readable_names ? false makes term names longer*)
                                              true (*presimps ? false makes the problem much bigger*)
                                              []    (*hypothesis*)
                                              (Const ("HOL.Trueprop", Type ("fun", [Type ("HOL.bool", []), Type ("prop", [])]) (*"bool ⇒ prop"*)) $ 
                                               (Const ("HOL.All", Type ("fun", [Type ("fun", [Type ("Real.real", []), Type ("HOL.bool", [])]), Type ("HOL.bool", [])])   (*"(real ⇒ bool) ⇒ bool"*)) $
                                                 Abs ("X", Type ("Real.real", []),
                                                   Const ("Orderings.ord_class.less_eq", Type ("fun", [Type ("Real.real", []), Type ("fun", [Type ("Real.real", []), Type ("HOL.bool", [])])]) (*"real ⇒ real ⇒ bool"*)) $
                                                     Const ("Groups.zero_class.zero", Type ("Real.real", [])) $
                                                     (Const ("Groups.times_class.times", Type ("fun", [Type ("Real.real", []), Type ("fun", [Type ("Real.real", []), Type ("Real.real", [])])]) (*"real ⇒ real ⇒ real"*)) $
                                                       (Const ("Groups.minus_class.minus", Type ("fun", [Type ("Real.real", []), Type ("fun", [Type ("Real.real", []), Type ("Real.real", [])])]) (*"real ⇒ real ⇒ real"*)) $ Bound 0 $
                                                         Const ("Groups.one_class.one", Type ("Real.real", []))) $
                                                       (Const ("Groups.minus_class.minus", Type ("fun", [Type ("Real.real", []), Type ("fun", [Type ("Real.real", []), Type ("Real.real", [])])]) (*"real ⇒ real ⇒ real"*)) $ Bound 0 $
                                                         Const ("Groups.one_class.one", Type ("Real.real", [])))))
                                              ))     (*conclusion*)
                                              []    (*facts*)

    fun ord_info () = ATP_Problem_Generate.atp_problem_term_order_info atp_problem
in
  atp_problem
(*  |> ATP_Problem.lines_of_atp_problem ATP_Problem.FOF (*format*) 
                                      (ATP_Systems.effective_term_order @{context} ATP_Proof.eN (*name of prover to send problem to*)) (*ord*) 
                                      ord_info
(*  |> cons ("% " ^ command ^ "\n" ^ (if comment = "" then "" else "% " ^ comment ^ "\n"))  *)
  |> File.write_list (Path.append (Path.explode "/home/cristina/Documents/internship/verified-metitarski/proof_reconstruction") (Path.basic "problem-6.txt")) (*"/home/cristina/Documents/internship/verified-metitarski/proof_reconstruction/problem-6.txt"*)   (*prob_path*)
*)
end
