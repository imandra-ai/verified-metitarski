theory Example
  imports Main Real Transcendental
    "~/Documents/internship/verified-metitarski/isabelle-proofs/AxiomsGeneral"
    "~~/src/HOL/Library/Sum_of_Squares"
    "~~/src/HOL/Eisbach/Eisbach"
begin
 
declare[[ML_print_depth=50]]  
  
ML
\<open>@{term "\<And>(X_000043::real) X_000044. X_000044 < - 1 + X_000043"}\<close>

ML
\<open>@{term "\<forall>(X_000043::real) X_000044. X_000044 < - 1 + X_000043"}\<close>  
 

lemma refute_28_lemm: "(- 1 + X_000050) / X_000050 < X_000051 \<or> X_000050 \<le> 0 \<or> X_000051 \<le> ln X_000050"
  sorry    
  
lemma "abs-problem-1": "\<forall>(X::real).(0\<le>X \<longrightarrow> abs(ln(1+X)-X) \<le> X^2)"
proof -
  {fix rr :: real
   have refute_28: "(- 1 + X_000050) / X_000050 < X_000051 \<or> X_000050 \<le> 0 \<or> X_000051 \<le> ln X_000050"
     sorry
   have refute_30_neg: "\<not> (- 1 + (1 + rr)) / (1 + rr) < rr * (1 + rr * - 1) \<and> \<not> 1 + rr \<le> 0 \<and> \<not> rr \<le> ln (1 + rr)"    
     sorry
   then have refute_24_neg: "\<not> ln (1 + rr) < rr * (1 + rr * - 1) \<and> \<not> rr \<le> ln (1 + rr)"
     using refute_28_lemm by fastforce
 }
   then show ?thesis
     sorry
 qed
   
lemma "\<forall>(X::real).(0\<le>X \<longrightarrow> abs(ln(1+X)-X) \<le> X^2)"
proof -
  {
    fix rr :: real
    assume "\<not> 0 < rr * (rr * (rr * - 1)) \<and> \<not> rr \<le> - 1"
    then have "\<not> rr < rr * (1 + rr * - 1) * (1 + rr) \<and> \<not> 1 + rr \<le> 0"
(*    sledgehammer [max_facts = 25, isar_proof] (add: algebra_simps)*)
     by(simp add: algebra_simps)
(*      sledgehammer[max_facts = 25]
      by (smt mult.commute mult.left_commute semiring_normalization_rules(2))*)
(*      by (smt mult.commute mult.left_commute semiring_normalization_rules(2)) ()*)
(*      by (smt mult.assoc mult.commute mult_minus_right semiring_normalization_rules(2)) *)
  }
  then show ?thesis
     sorry
 qed
  
(* Making a custom MT simpset*)   
named_theorems metitarski_simps "arithmetic simplification rules used by Metitarski"
 
declare power2_eq_square[metitarski_simps]    
  
lemma "\<forall>(X::real).(0\<le>X \<longrightarrow> abs(ln(1+X)-X) \<le> X^2)"
proof -
  {
    fix rr :: real
    assume "\<not> rr * rr < \<bar>rr * - 1 + ln (1 + rr)\<bar>"
    then have "\<not> rr\<^sup>2 < \<bar>ln (1 + rr) - rr\<bar>"
      by (force simp add: metitarski_simps)
  }
  then show ?thesis
     sorry
qed  

lemma "1 / 2 * (1 + 5 * (X_000060::real)) * (X_000060 - 1) = - 1 / 2 + X_000060 * (- 2 + X_000060 * (5 / 2))"  
  apply(simp add: algebra_simps divide_simps)
  done
    
 
(* Eisbach *)
method mt_arith = ((simp add: divide_simps split: if_splits); use nothing in sos)
  
notepad
begin
  fix rr :: real
  assume assm: "\<not> rr < 0 \<and> \<not> rr * (3 + rr * (5 / 2)) / (3 + rr * (4 + rr)) < rr * 2 / (2 + rr) \<and> \<not> rr \<le> - 1"
  then have "\<not> rr < 0 \<and> \<not> (- 1 / 2 + (1 + rr) * (- 2 + (1 + rr) * (5 / 2))) / ((1 + rr) * (2 + (1 + rr))) < rr * 2 / (2 + rr) \<and> \<not> 1 + rr \<le> 0" 
    by mt_arith
end      
        
notepad
begin  
  have " \<And>r ra X.\<not> (1 / 2 * (ra + 5) * (ra - 1) / (2 * ra + 1)) \<le> r \<or> r \<le> 0 \<or> ra \<le> (X::real)"  
    sorry
  then have " \<And>r ra X. (r::real) < (- 5 / 2 + ra * (2 + ra * (1 / 2))) / (1 + ra * 2) \<or> r \<le> 0 \<or> ra \<le> (X::real)"
    apply(subgoal_tac "\<forall>ra. (1 / 2 * (ra + 5) * (ra - 1) / (2 * ra + 1)) = 
      (- 5 / 2 + ra * (2 + ra * (1 / 2))) / (1 + ra * 2)")  
    
    apply (simp add: divide_simps)
    apply (atomize)    (*need to get rid of \<And> to apply if_splits*)
    apply (simp  split: if_splits)
      apply(sos)
    sorry
      
(*        
    using [[simp_trace_new mode=full]]
    using [[simp_break "?x \<or> ?y"]]
*)
end      
   
notepad
begin
  have "\<And>r ra. \<not> lgen False (1 / 2 * (ra + 5) * (ra - 1) / (2 * ra + 1)) r "  
    sorry
  then have "\<And>r ra. (r::real) < (- 5 / 2 + ra * (2 + ra * (1 / 2))) / (1 + ra * 2)"
    using [[simp_trace_new mode=full]]
    apply - 
    apply (simp  add: arith)
    sorry
end    

(* Fails if the simplification doesn't discharge the goal it was applied to*)  
method mt_simp = (simp; fail | simp add: field_simps metitarski_simps; fail)  
  
notepad
begin
  fix rr :: real
  assume "\<not> 0 < rr * rr \<and> \<not> rr \<le> - 1"
  then have "\<not> rr < rr * (1 + rr) \<and> \<not> 1 + rr \<le> 0"
    by mt_simp
end  
  
notepad
begin
  fix rr :: real
  assume "\<not> ln (1 + rr) < rr * (1 + rr * - 2) \<and> \<not> rr \<le> ln (1 + rr)"
  then have "\<not> rr * (rr * 2) < - (rr * - 1 + ln (1 + rr)) \<and> \<not> 0 \<le> rr * - 1 + ln (1 + rr)"
    by mt_simp   
end
  
notepad
begin
  fix rr :: real
  have "rr * (3 + rr * (5 / 2)) / (3 + rr * (4 + rr) + ln 2) = 
    (- 1 / 2 + (1 + rr) * (- 2 + (1 + rr) * (5 / 2))) / ((1 + rr) * (2 + (1 + rr)) + ln 2)"
    by(algebra)  
end  
  
  
notepad
begin
  fix rr :: real
  assume assm: "\<not> rr < 0 \<and> \<not> rr * (3 + rr * (5 / 2)) / (3 + rr * (4 + rr)) < rr * 2 / (2 + rr) \<and> \<not> rr \<le> - 1"
  then have "\<not> rr < 0 \<and> \<not> (- 1 / 2 + (1 + rr) * (- 2 + (1 + rr) * (5 / 2))) / ((1 + rr) * (2 + (1 + rr))) < rr * 2 / (2 + rr) \<and> \<not> 1 + rr \<le> 0"
    apply(subgoal_tac "rr * (3 + rr * (5 / 2)) / (3 + rr * (4 + rr)) = 
    (- 1 / 2 + (1 + rr) * (- 2 + (1 + rr) * (5 / 2))) / ((1 + rr) * (2 + (1 + rr)))")
     apply(auto)
      apply(algebra)
    done
end  

(* The | in match doesn't work ! *)  
  
(*lemma "A \<Longrightarrow> A \<and> (B \<longrightarrow> B)"
by (match premises in H : A \<Rightarrow> \<open> intro conjI , rule H , rule impI ,
      match premises (local) in A \<Rightarrow> \<open> fail \<close>
                              | H 0 : B \<Rightarrow> \<open> rule H 0 \<close>\<close> )  
  
method match_test = (match premises in "A \<or> B" for A and B \<Rightarrow> \<open>rule disjE\<close>
                                      |"A \<and> B" for A and B \<Rightarrow> \<open>rule conjE\<close>)  
*)  
method div_simp = (simp add: divide_simps split: if_splits) 
  
method div_simp_ifsplit = (simp add: divide_simps split: if_split, algebra)  

(*Nees the "|simp" because algebra chokes when the two sides are already in the same form.*)  
method subst_left_less = 
  (match premises in "\<not> a < b" and I: A for A and a :: real and b :: real \<Rightarrow> 
    \<open>match conclusion in "\<not> a' < b'" for a' :: real and b'::real \<Rightarrow> 
      \<open>(rule ssubst [where ?s=a and ?t=a'], (simp; fail | algebra | 
                    (simp add: divide_simps split: if_split, use I in algebra)))\<close>\<close>)

method subst_left_less_eq = 
  (match premises in "\<not> a \<le> b" and I: A for A and a :: real and b :: real \<Rightarrow> 
    \<open>match conclusion in "\<not> a' \<le> b'" for a' :: real and b'::real \<Rightarrow> 
      \<open>(rule ssubst [where ?s=a and ?t=a'], (simp; fail | algebra |
                    (simp add: divide_simps split: if_split, use I in algebra)))\<close>\<close>)
    
method subst_right_less =
  (match premises in "\<not> a < b" and I: A for A and a :: real and b :: real \<Rightarrow> 
    \<open>match conclusion in "\<not> a < b'" for b' :: real \<Rightarrow> 
      \<open>(rule ssubst [where ?s=b and ?t=b'], (simp; fail | algebra |
                    (simp add: divide_simps split: if_split, use I in algebra)))\<close>\<close>)
    
method subst_right_less_eq =
  (match premises in "\<not> a \<le> b" and I: A for A and a :: real and b :: real \<Rightarrow> 
    \<open>match conclusion in "\<not> a \<le> b'" for b' :: real \<Rightarrow> 
      \<open>(rule ssubst [where ?s=b and ?t=b'], (simp; fail | algebra |
                    (simp add: divide_simps split: if_split, use I in algebra)))\<close>\<close>)    

method mt_algebra = ((subst_left_less|subst_left_less_eq),
      (subst_right_less|subst_right_less_eq),  assumption)    

(*Useful when something is moved to the other side of an inequality.
  An example is in two-variable-problem-1.tptp

  assume "\<not> ln (rra / rr) \<le> (rra + rr * - 1) / (rra * (1 / 2) + rr * (1 / 2)) \<and> \<not> rr \<le> rra * - 1"
  then have "\<not> ln (rra / rr) * (rra * (1 / 2) + rr * (1 / 2)) \<le> rra + rr * - 1"
*)   
  
method mt_arith_drule_conj = (mt_simp | ((erule conjE)+, mt_algebra))
  
(* rule automatically chooses conjI *)
(* Need the | in case the inequality that requires algebra is the last one *)  
method mt_arith_rule = 
  (-, ((((use nothing in rule, use nothing in mt_arith_drule_conj) | use nothing in mt_arith_drule_conj)+) 
        | use nothing in div_simp))
  
notepad
begin
  fix rr :: real
  assume assm: "\<not> rr < 0 \<and> \<not> rr * (3 + rr * (5 / 2)) / (3 + rr * (4 + rr)) < rr * 2 / (2 + rr) \<and> \<not> rr \<le> - 1"
  then have "\<not> rr < 0 \<and> \<not> (- 1 / 2 + (1 + rr) * (- 2 + (1 + rr) * (5 / 2))) / ((1 + rr) * (2 + (1 + rr))) < rr * 2 / (2 + rr) \<and> \<not> 1 + rr \<le> 0"
    (*apply -
      apply rule
     apply(erule conjE)+
     apply simp
      apply rule
     apply(erule conjE)+
     apply(subst_left_less|subst_left_less_eq)  
      apply(algebra)*)
    apply mt_arith_rule
    by mt_arith_rule
        
end
 
(*Check mt_arith_rule works when the hard inequality is the last one*)  
notepad
begin
  fix rr :: real
  have "\<not> rr < 0 \<and> \<not> rr * (3 + rr * (5 / 2)) / (3 + rr * (4 + rr)) < rr * 2 / (2 + rr) \<and> \<not> rr \<le> - 1 \<Longrightarrow>
    \<not> (- 1 / 2 + (1 + rr) * (- 2 + (1 + rr) * (5 / 2))) / ((1 + rr) * (2 + (1 + rr))) < rr * 2 / (2 + rr)"
    by mt_arith_rule
end  

(*terms moved from one side of the inequality to another*)  
notepad
begin
  fix rr :: real and rra :: real
  assume "\<not> ln (rra / rr) \<le> (rra + rr * - 1) / (rra * (1 / 2) + rr * (1 / 2)) \<and> \<not> rr \<le> rra * - 1"
  then have "\<not> ln (rra / rr) * (rra * (1 / 2) + rr * (1 / 2)) \<le> rra + rr * - 1"
    apply -
    apply(simp add: divide_simps split: if_splits)
  done    
      
end  
  
notepad
begin
  fix rr :: real and rra :: real
  assume "rr * rr \<noteq> 0 \<and> rr \<noteq> 0"  
  then have "(rra * (rra * (5 / 2)) + rr * (rra * - 2 + rr * (- 1 / 2))) / (rra * rra + rr * (rra * 2))
    = (- 1 / 2 + rra / rr * (- 2 + rra / rr * (5 / 2))) / (rra / rr * (2 + rra / rr))"
    apply -
      apply(erule conjE)
    apply(simp add: divide_simps split: if_split, algebra)
    done
      
end  
  
(*The side conditions in the assumptions are needed by algebra to prove the equality*)
(* Integrated in mt_arith_rule, but it breaks some proofs *)  
notepad
begin
  fix rr :: real and rra :: real
  assume "\<not> (rra * (rra * (5 / 2)) + rr * (rra * - 2 + rr * (- 1 / 2))) / (rra * rra + rr * (rra * 2)) \<le> (rra + rr * - 1) / (rra * (1 / 2) + rr * (1 / 2)) (*\<and> \<not> rra / rr \<le> 0*) \<and> rr * rr \<noteq> 0 \<and> rr \<noteq> 0"
  then have "\<not> (- 1 / 2 + rra / rr * (- 2 + rra / rr * (5 / 2))) / (rra / rr * (2 + rra / rr)) \<le> (rra + rr * - 1) / (rra * (1 / 2) + rr * (1 / 2)) (*\<and> \<not> rra / rr \<le> 0*)"
    apply -
    apply(erule conjE)+
    apply(match premises in  "\<not> a \<le> b" and I: A for A and a :: real and b :: real \<Rightarrow> 
        \<open>match conclusion in "\<not> a' \<le> b'" for a' :: real and b'::real \<Rightarrow> 
          \<open>(rule ssubst [where ?s=a and ?t=a'], (simp; fail | algebra | simp add: divide_simps split: if_split, use I in algebra))\<close>\<close>) 
     (* div_simp_ifsplit doesn't work inside the match, because it can't access the premises 
        (they have been lifted to theorems) 
        but it should go there in order for subst_left to work *)   
        apply(assumption)
     (* Needs if_split NOT if_splits *)     
    done
      
end
 
(*terms moved from one side of the inequlity to another.
  Incorporated in mt_arith_rule*)  
notepad
begin
  fix rr :: real
  have "\<not> rr * (- 3 + rr * (- 1 / 2)) < rr * (- 6 + rr * - 4) / (2 + rr) \<Longrightarrow>
    \<not> rr * 2 / (2 + rr) * (3 + rr * 2) < rr * (3 + rr * (1 / 2))"
    apply(div_simp; mt_simp)
    done
end  
  
end