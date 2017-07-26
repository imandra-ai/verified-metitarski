theory Isar
  imports Main Real CristinaProblem6
begin

declare[[ML_print_depth=50]]  
  
ML \<open> @{term "\<forall>X::real. less_eq 0 (times (minus X 1::real) (minus X 1))"} \<close>
ML\<open> 
local
fun pp_pair (x, y) = Pretty.list "(" ")" [x, y]
fun pp_list xs = Pretty.list "[" "]" xs
fun pp_str s   = Pretty.str s
fun pp_qstr s  = Pretty.quote (pp_str s)
fun pp_int i   = pp_str (string_of_int i)
fun pp_sort S  = pp_list (map pp_qstr S)
fun pp_constr a args = Pretty.block [pp_str a, Pretty.brk 1, args]
in
fun raw_pp_typ (TVar ((a, i), S)) =
pp_constr "TVar" (pp_pair (pp_pair (pp_qstr a, pp_int i), pp_sort S))
| raw_pp_typ (TFree (a, S)) =
pp_constr "TFree" (pp_pair (pp_qstr a, pp_sort S))
| raw_pp_typ (Type (a, tys)) =
pp_constr "Type" (pp_pair (pp_qstr a, pp_list (map raw_pp_typ tys)))
end;
PolyML.addPrettyPrinter
(fn _ => fn _ => ml_pretty o Pretty.to_ML o raw_pp_typ);
@{typ "(real \<Rightarrow> bool) \<Rightarrow> bool"}
\<close>  
ML\<open>Syntax.read_term @{context} "1"\<close>  
  
ML_file "~/Documents/internship/verified-metitarski/proof_reconstruction/tstp_input.ML" 

ML_file "~/Documents/internship/verified-metitarski/proof_reconstruction/tstp_parsing.ML"
  
ML_file "~/Documents/internship/verified-metitarski/proof_reconstruction/problem_generate.ml"
  
ML\<open>map_filter\<close>

  
end
  