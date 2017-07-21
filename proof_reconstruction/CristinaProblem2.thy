theory CristinaProblem2
  imports Main
begin
  
lemma "less_eq 0 (plus (minus X 1) (minus X 1))"
proof -
  have refute_0_10: "\<not> less (1::'b) (times (skoXC1::'a) (plus 2 (times skoXC1 (uminus 1::'a)::'b)))"
    by metis
      
  then have refute_0_00: "\<not> less (times (minus skoXC1 1) (minus skoXC1 1)) 0"
    using refute_0_10 by metis
      
  then have normalize_0_10: "\<not> less (times (minus skoXC1 1) (minus skoXC1 1)) 0"
    using refute_0_00 by metis
      
  then have normalize_0_00: "\<forall>a. \<not> less (times (minus a 1) (minus a 1)) "
    using normalize_0_10 by metis
      
  then have negate_0_00: "\<forall>a. less_eq 0 (times (minus a 1) (minus a 1))"
    using normalize_0_00 by metis
      
  then have subgoal_00: "\<exists>a. \<not> less_eq 0 (times (minus a 1) (minus a 1))"
    using negate_0_00 by metis
      
  show "\<forall>a. less_eq 0 (times (minus a 1) (minus a 1))"
    using subgoal_00 by metis
qed

end