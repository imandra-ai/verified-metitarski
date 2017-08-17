theory Tests
  imports Main Real Complex_Main
begin
  
(*Missing paran at the end. 
  \<longrightarrow> instead of \<Longrightarrow>.
  MT "power(X, 2)" or "X^2" should be in Isabelle: "(power X 2)" or "X^2". This is for natural exponents only.
  MT "pow(X, 2)" becomes Isabelle "X powr 2". For any real exponent.
*)
(*abs-problem-1.tptp*)  
lemma "\<forall>(X::real).(((0 <= X) \<longrightarrow> (abs((ln((1 + X)) - X)) <= power X 2)))"
sorry  
  
  
(*Missing paran at the end. 
  \<longrightarrow> instead of \<Longrightarrow>.
  MT "power(X, 2)" or "X^2" should be in Isabelle: "(power X 2)" or "X^2". This is for natural exponents only.
  MT "pow(X, 2)" becomes Isabelle "X powr 2". For any real exponent.
*)  
(*abs-problem-2.tptp*)
lemma "\<forall>(X::real).(((abs(X) <= 1/2) \<longrightarrow> (abs((ln((1 + X)) - X)) <= (2 * (power X  2)))))"  
sorry
    
  
(*"\and" should be "\<and>".
  \<longrightarrow> instead of \<Longrightarrow>.
*)  
(*abs-problem-3.tptp*)
lemma "\<forall>(X::real).(((Not((X <= 0)) \<and> (X <= 582811643/1000000000)) --> (abs(ln((1 - X))) <= ((3 * X) / 2))))"  
sorry
    

(*"\and" should be "\<and>".
  \<longrightarrow> instead of \<Longrightarrow>.
*)
(*sin-problem-3.tptp*)    
lemma "\<forall>(X::real).(((Not((X <= 0)) \<and> (X <= pi)) --> ((sin(X) / X) <= 1)))"
sorry
    

(*"\and" should be "\<and>".
  \<longrightarrow> instead of \<Longrightarrow>.
*)  
(*cos-problem-1.tptp*)
lemma "\<forall>(X::real).(((Not((X <= 0)) \<and> Not((1/2 <= X))) --> Not((cos((pi * X)) <= (1 - (2 * X))))))"    
sorry
  

(*"\and" should be "\<and>".
  \<longrightarrow> instead of \<Longrightarrow>.
*)   
(*cos-problem-2.tptp*)
lemma "\<forall>(X::real).(((Not((X <= 1/2)) \<and> Not((1 <= X))) --> Not(((1 - (2 * X)) <= cos((pi * X))))))"
sorry
    

(*\<longrightarrow> instead of \<Longrightarrow>.
*)  
(*cos-problem-3.tptp*)
lemma "\<forall>(X::real).((Not((1 <= abs(X))) --> (abs(cos(X)) <= 1)))"
sorry
    

(*"\and" should be "\<and>".
  \<longrightarrow> instead of \<Longrightarrow>.
*)  
(*tan-problem-1.tptp*)
lemma "\<forall>(X::real).((((0 <= X) \<and> Not(((pi / 2) <= X))) --> ((1 - cos(X)) <= tan((X / 2)))))"
sorry
    

(*"\and" should be "\<and>".
  \<longrightarrow> instead of \<Longrightarrow>.
*)  
(*tan-problem-2.tptp*)
lemma "\<forall>(X::real).((((0 <= X) \<and> Not((314159/200000 <= X))) --> (X <= tan(X))))"
sorry
    

(*"\and" should be "\<and>".
  \<longrightarrow> instead of \<Longrightarrow>.
*)  
(*two-variable-problem-1.tptp*)
lemma "\<forall>(X::real).(\<forall>(Y::real).(((Not((Y <= 0)) \<and> Not((X <= Y))) --> Not(((ln((X / Y)) / 2) <= ((X - Y) / (X + Y)))))))"
sorry
    

(*"\and" should be "\<and>".
  \<longrightarrow> instead of \<Longrightarrow>.
*)   
(*two-variable-problem-2.tptp*)
lemma "\<forall>(X::real).(\<forall>(Y::real).(((Not((X <= 0)) \<and> Not((Y <= 0))) --> Not((exp(X) <= exp(((X * Y) / (X + Y))))))))"
sorry  
end
  