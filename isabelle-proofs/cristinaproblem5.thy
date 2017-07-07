theory cristinaproblem5
  imports Main Real "~~/src/HOL/Library/Sum_of_Squares" AxiomsGeneral
begin
  
lemma cristinaproblem5:
  "(interval False  1  False  2  x) \<longrightarrow> 0 < x * x"
proof(rule ccontr)
  assume hypothesis: "\<not>((interval False  1  False  2  x) \<longrightarrow> 0 < x * x)"
  
  (*conjunct*)    
  have normalize_0_2: "(interval False  1  False  2  x)"
    using hypothesis by blast

  (*conjunct*)
  have normalize_0_3: "x * x \<le> 0"
    using hypothesis by linarith
  
  (*resolve*)
  have refute_0_2: "lgen False 1 x"  
    using interval_elim1_axiom normalize_0_2 by auto
      
  (*arithmetic*)    
  have refute_0_3:"1 \<le> x"
    using refute_0_2 by auto
   
  (*decision*)    
  have refute_0_5: "x < 1"
    using normalize_0_3 by sos
      
  (*resolve*)    
  then show False
    using refute_0_3 refute_0_5 by auto
qed
  
end