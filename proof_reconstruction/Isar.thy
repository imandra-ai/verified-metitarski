theory Isar
  imports Main Real
begin

declare[[ML_print_depth=50]]  
  
ML {* @{term "1"} *}  
ML\<open>Syntax.read_term @{context} "1"\<close>  
  
ML_file "~/Documents/internship/verified-metitarski/proof_reconstruction/tstp_input.ML" 

ML_file "~/Documents/internship/verified-metitarski/proof_reconstruction/tstp_parsing.ML"
  
ML\<open>open Symtab\<close>

  
end
  