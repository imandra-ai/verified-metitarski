theory "exp-problem-1"
imports "../GenerateATP"
begin
  
lemma "\<forall>(X::real).((((0 <= X) \<and> (X <= 1)) --> ((exp(X) - (1 + X)) <= (X ^ 2 * exp(X)))))"
  apply(tactic {*fn st => (writeln (isar_proof st [] @{context}); Seq.single st) *})
  
end  