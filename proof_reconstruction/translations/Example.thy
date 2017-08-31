theory Example
  imports Main Real Transcendental "~/Documents/internship/verified-metitarski/isabelle-proofs/AxiomsGeneral"
begin
 
declare[[ML_print_depth=50]]  

ML\<open>
fun bind_free_vars (t : term) : term =
  let
    fun get_index list element acc =
    (case list of
      [] => NONE
    | l::ls => if l=element then SOME acc
               else get_index ls element (acc+1)
    ) 

    val bound_vars : string list Unsynchronized.ref = Unsynchronized.ref []

    fun bind_free_vars_aux (forall_count : int) (t : term) : term =
      (case t of
        Free (name, _) =>
          (case get_index (!bound_vars) name 0 of
            NONE => (bound_vars := (name::(!bound_vars));
                     Bound ((List.length (!bound_vars)) - 1 + forall_count)
                    )
          | SOME i => Bound ((List.length (!bound_vars)) - i - 1 + forall_count)
          )

      | t1 $ t2 => (bind_free_vars_aux forall_count t1) $ (bind_free_vars_aux forall_count t2)
          
      | Abs (name, ty, t1) => Abs (name, ty, bind_free_vars_aux (forall_count+1) t1)

      | t1 => t1         
      )

    val renamed_t : term = bind_free_vars_aux 0 t

    fun add_pure_all (bound_list : string list) (t : term) =
      (case bound_list of
        [] => t
      | var::vars => Const ("Pure.all", @{typ "(real \<Rightarrow> prop) \<Rightarrow> prop"}) $
                          Abs (var, @{typ "real"}, add_pure_all vars t)
      )
  in
    add_pure_all (!bound_vars) renamed_t
  end;

bind_free_vars @{term "\<forall> X_000044. X_000044 < - 1 + (X_000043::real)"};

bind_free_vars (Const ("HOL.Trueprop", @{typ "bool \<Rightarrow> prop"}) $ (@{term "\<forall>z1 z2.(X_000044::real) < - 1 + X_000043 + z1 +z2"}))
\<close>
  
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
    
  
lemma "True"
proof -
  {
    fix rr :: real
    assume h: "\<not> lgen False X_000061 (1 / 2 * (1 + 5 * X_000060) * (X_000060 - 1) / (X_000060 * (2 + X_000060))) \<or> X_000060 \<le> 0 \<or> X_000061 \<le> ln X_000060"
    then have "1 / 2 * (1 + 5 * (X_000060::real)) * (X_000060 - 1) = - 1 / 2 + X_000060 * (- 2 + X_000060 * (5 / 2))"  
      by(simp add: algebra_simps divide_simps)
    then have "(- 1 / 2 + X_000060 * (- 2 + X_000060 * (5 / 2))) / (X_000060 * (2 + X_000060)) < X_000061 \<or> X_000060 \<le> 0 \<or> X_000061 \<le> ln X_000060"
     (* sledgehammer (add: algebra_simps)*)
      using h by auto
  }
  then show ?thesis
     sorry
qed    
  
end