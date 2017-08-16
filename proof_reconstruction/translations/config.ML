(*All the paths used in the translation from an isabelle lemma to a termified atp proof*)

(*Path to the translation folder. Not needed if GenerateATP is in the same folder.
  Will be used in a .thy file*)
val trans_path = "~/Documents/internship/verified-metitarski/proof_reconstruction/translations/"

(*Path to the MT axioms formalised in Isabelle. Will be written to a .thy file as an import*)
val abs_ax_path = "~/Documents/internship/verified-metitarski/isabelle-proofs/AxiomsAbs"
val general_ax_path = "~/Documents/internship/verified-metitarski/isabelle-proofs/AxiomsGeneral"
val ln_bounds_path = "~/Documents/internship/verified-metitarski/isabelle-proofs/LnBounds"

(*Path to the MT executable*)
val mt_path = "/home/cristina/Documents/internship/metitarski/metit"

(*Path to the file where MT reads the problem from*)
val problem_path = "/home/cristina/problem.tptp"