theory CristinaProblem2
  imports Main Real "~~/src/HOL/Library/Sum_of_Squares"
begin

 
(*ML\<open>
  let
val ctxt1 = Variable.declare_term @{term "x::nat"} @{context}
val ctxt2 = Variable.declare_term @{term "x::int"} ctxt1
in
(Syntax.read_term ctxt1 "x",
Syntax.read_term ctxt2 "x")
end
\<close>  
*)  

lemma "\<forall>X::real. less_eq 0 (times (minus X 1::real) (minus X 1))"
proof -
  have refute_0_10: "\<not> less (1::real) (times (skoXC1::real) (plus (2::real) (times skoXC1 (uminus 1::real)::real)))"
    by (*metis*) sos
      
  then have refute_0_00: "\<not> less (times (minus skoXC1 1) (minus skoXC1 1)) 0"
    using refute_0_10 by (*metis*) simp
      
  then have normalize_0_10: "\<not> less (times (minus skoXC1 1) (minus skoXC1 1)) 0"
    using refute_0_00 by metis
      
  then have normalize_0_00: "\<forall>r. \<not> less (times (minus r 1) (minus r 1)) 0"
    using normalize_0_10 by (*metis*) simp
      
  then have negate_0_00: "\<forall>r. less_eq 0 (times (minus r 1) (minus r 1))"
    using normalize_0_00 by simp

  (* Why do we have this step? *)      
  then have subgoal_00: "\<exists>r. \<not> less_eq 0 (times (minus r 1) (minus r 1))"
    using negate_0_00 by metis
      
  show "\<forall>r. less_eq 0 (times (minus r 1) (minus r 1))"
    using subgoal_00 by metis
qed  
  
end