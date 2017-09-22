---------------------------------------------------------------------

Bounds:

- stuck on one of the cos bounds in CosBounds.thy

- massage existing bounds to the form MT expects

- there re no bounds proved for cube and nth root, hyperbolic functions


---------------------------------------------------------------------


Translation:

- not supporting hyperbolic functions. How do you represent them in Isabelle?

- problem: MT "^" is for integer exponents, "pow" for all other exponents; Isabelle "^" is for natural exponents, "powr" for any kind of exponent. 

atp_problem_to_tptp.ML translates:
    - Isabelle "^" to MT "^"/"power"
    - Isabelle "powr" to MT "pow"
termify_atp_proof.ML does the reverse translation.

When translating "powr" with negative integer exponent to MT "pow", MT raises a strange error. See polypaver-bench-exp.thy.  


---------------------------------------------------------------------


Proof methods:

- make mt_arith_rule work on proof steps with meta-universal quantifiers:

  assume " ⋀r ra X.¬ (1 / 2 * (ra + 5) * (ra - 1) / (2 * ra + 1)) ≤ r ∨ r ≤ 0 ∨ ra ≤ (X::real)"  
  then have " ⋀r ra X. (r::real) < (- 5 / 2 + ra * (2 + ra * (1 / 2))) / (1 + ra * 2) ∨ r ≤ 0 ∨ ra ≤ (X::real)"

- use the univariate RCF instead of SOS

- try the proof reconstruction on more MT problems to see if the proof methods work.

- cos-problem-4.thy: sos doesn't know how to interpret pi so it fails. It seems like MT "decision" can interpret pi??!!

- exp-problem-1.thy: why does sos time out on a univariate problem? Because of the vary large constants?


---------------------------------------------------------------------


Other:

- provide counter-example in Isabelle when MT gives up

- wrap MT in a command in Isabelle, like sledgehammer

- from Isabelle, we always call MT with case splitting disabled (and a set of default parameters, see config.ML); this makes a lot of problems unprovable or very slow.

- exp-general.ax in the MT axioms: why are the two axioms in this file the same?
