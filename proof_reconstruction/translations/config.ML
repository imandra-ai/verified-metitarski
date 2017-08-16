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

(*Path to the file where the tptp problem is written and MT reads it from*)
val problem_path = "/home/cristina/problem.tptp"

(*Path to the file the isar proof is written to.*)
val isar_proof_path = "/home/cristina/Proof.thy"