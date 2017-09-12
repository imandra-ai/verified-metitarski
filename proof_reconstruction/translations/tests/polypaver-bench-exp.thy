theory "polypaver-bench-exp"
imports "../GenerateATP"
begin
 
(*Weird MT error*)  
lemma "\<forall>(X::real).(\<forall>(Y::real).((((0 <= X) \<and> ((X <= 1) \<and> ((0 <= Y) \<and> (Y <= 1)))) --> (exp((X + Y)) <= ((exp(X) * exp(Y)) + (2 powr -8))))))"  
  apply(tactic {*fn st => (writeln (isar_proof st [] @{context}); Seq.single st) *})
end
  