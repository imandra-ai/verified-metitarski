theory "abs-problem-3"
  imports "../GenerateATP"
begin
  
(* MT fails because --autoInclude doesn't include all necessary axioms.*)  
lemma "abs-problem-3": "\<forall>(X::real).(((Not((X <= 0)) \<and> (X <= 582811643/1000000000)) --> (abs(ln((1 - X))) <= ((3 * X) / 2))))"
  apply(tactic {*fn st => (writeln (isar_proof st [] @{context}); Seq.single st) *})
end  