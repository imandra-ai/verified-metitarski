theory Isar
  imports Main Real CristinaProblem6
begin

declare[[ML_print_depth=50]]  
  
ML \<open> @{term "\<forall>X::real. less_eq 0 (times (minus X 1::real) (minus X 1))"} \<close> 
ML \<open>@{term "P \<Longrightarrow> P::bool"}\<close>
ML \<open>@{typ "prop"}\<close>  
  
ML\<open>Syntax.read_term @{context} "1"\<close>  
  
ML_file "~/Documents/internship/verified-metitarski/proof_reconstruction/tstp_input.ML" 

ML_file "~/Documents/internship/verified-metitarski/proof_reconstruction/tstp_parsing.ML"
  
ML_file "~/Documents/internship/verified-metitarski/proof_reconstruction/problem_generate.ML"
  
ML\<open>open PolyML\<close>

  
end
  