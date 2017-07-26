let
    fun choose_type_enc strictness best_type_enc format =
      the_default best_type_enc
      #> ATP_Problem_Generate.type_enc_of_string strictness
      #> ATP_Problem_Generate.adjust_type_enc format
in

ATP_Problem_Generate.generate_atp_problem @{context}
                                          false (*generate_info: true only of format = DFG*)
                                          ATP_Problem.FOF   (*atp_format*)
                                          ATP_Problem.Conjecture (*prem_role*)
                                          (choose_type_enc ATP_Problem_Generate.Strict "mono_native" ATP_Problem.FOF NONE) (*type encoding*)
                                          ATP_Problem_Generate.Metis (*mode*)
                                          "" (*lam_trans*)
                                          true (*uncurried_aliases*)
                                          true (*readable_names*)
                                          true
                                          []    (*hypothesis*)
                                          (Const ("HOL.All", "(real ⇒ bool) ⇒ bool") $
                                             Abs ("X", "real",
                                               Const ("Orderings.ord_class.less_eq", "real ⇒ real ⇒ bool") $
                                                 Const ("Groups.zero_class.zero", "real") $
                                                 (Const ("Groups.times_class.times", "real ⇒ real ⇒ real") $
                                                   (Const ("Groups.minus_class.minus", "real ⇒ real ⇒ real") $ Bound 0 $
                                                     Const ("Groups.one_class.one", "real")) $
                                                   (Const ("Groups.minus_class.minus", "real ⇒ real ⇒ real") $ Bound 0 $
                                                     Const ("Groups.one_class.one", "real"))))
                                          )     (*conclusion*)
end
