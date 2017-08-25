theory AxiomsGeneral
  imports Main Real
begin

fun lgen :: "bool \<Rightarrow> real \<Rightarrow> real \<Rightarrow> bool" where
  "lgen False x y = (x\<le>y)"
 |"lgen True x y = (x<y)"  
   
fun interval :: "bool \<Rightarrow> real \<Rightarrow> bool \<Rightarrow> real \<Rightarrow> real \<Rightarrow> bool" where
  "interval False a False b x = (a\<le>x \<and> x\<le>b)"
 |"interval False a True b x = (a\<le>x \<and> x<b)"
 |"interval True a False b x = (a<x \<and> x\<le>b)"
 |"interval True a True b x = (a<x \<and> x<b)"
   
section \<open>Generalised orderings\<close>
  
lemma lgen_le_pos:
  "(\<not>(x\<le>y)) \<or> (lgen False x y)"
  by auto
    
lemma lgen_less_pos:
  "(\<not>(x<y)) \<or> (lgen True x y)"
  by auto
    
lemma lgen_le_neg:
  "(x\<le>y) \<or> \<not> (lgen False x y)"
  by auto
    
lemma lgen_less_neg:
  "(x<y) \<or> \<not> (lgen True x y)"
  by auto
    
section\<open>Division Axioms\<close>
    
lemma leq_left_divide_mul_pos:
  "(\<not> ((x::real) \<le> y*z))
    \<or> x/z \<le> y
    \<or> z \<le> 0"
  using pos_divide_le_eq by force
    
lemma leq_left_mul_divide_pos:
  "(\<not> ((x::real) \<le> y/z))
    \<or> x*z \<le> y
    \<or> z \<le> 0"
  using pos_le_divide_eq by force

lemma leq_right_divide_mul_pos:
  "(\<not> ((x::real)*z \<le> y))
    \<or> x \<le> y/z
    \<or> z \<le> 0"
  using pos_le_divide_eq by force
    
lemma leq_right_mul_divide_pos:
  "(\<not> ((x::real)/z \<le> y))
    \<or> x \<le> y*z
    \<or> z \<le> 0"
  using pos_divide_le_eq by force
  
lemma leq_left_divide_mul_neg:
  "(\<not>((x::real) \<le> y*z))
    \<or> y \<le> x/z
    \<or> 0 \<le> z"
  using neg_le_divide_eq by force
    
lemma leq_left_mul_divide_neg:
  "(\<not> ((x::real) \<le> y/z))
    \<or> y \<le> x*z
    \<or> 0 \<le> z"
  using neg_le_divide_eq by force
    
lemma leq_right_divide_mul_neg:
  "(\<not> ((x::real)*z \<le> y))
    \<or> y/z \<le> x
    \<or> 0 \<le> z"
  using neg_divide_le_eq by force
    
lemma leq_right_mul_divide_neg:
  "(\<not> ((x::real)/z \<le> y))
    \<or> y*z \<le> x
    \<or> 0 \<le> z"
  using neg_divide_le_eq by force
    
section\<open>Intervals\<close>    
    
lemma interval_intro:
  "\<not> (lgen r a x)
    \<or> \<not> (lgen s x b)
    \<or> (interval r a s b x)"
  by (metis interval.simps(1) interval.simps(2) interval.simps(3) interval.simps(4) lgen.elims(2))
    
lemma interval_elim1:
  "\<not>(interval r a s b x)
    \<or> (lgen r a x)"
  by (smt interval.elims(2) lgen.elims(3))
    
lemma interval_elim2:
  "\<not>(interval r a s b x)
    \<or> (lgen s x b)"
  by (smt interval.elims(2) lgen.elims(3))
end