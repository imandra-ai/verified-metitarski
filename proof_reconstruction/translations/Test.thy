theory Test
  imports Main Real Transcendental "~/Documents/internship/verified-metitarski/isabelle-proofs/AxiomsGeneral"
begin
  
ML_file "config.ML"  
  
ML_file "thm_to_atp_problem.ML"
ML_file "atp_problem_to_tptp.ML"
ML_file "mt_call.ML"
ML_file "tptp_proof_to_atp_proof.ML"
ML_file "termify_atp_proof.ML"
ML_file "termified_atp_proof_to_indirect_proof.ML"  
  
ML_file "prove.ML"

ML\<open>
fun read_conjectures (file_path : string) : unit =
  let
    val inStream = TextIO.openIn file_path

    fun read_line (inStream : TextIO.instream) =
      (case TextIO.inputLine inStream of
        NONE => ()
      | SOME problem =>
        let
          fun delimiter #"," = true
            | delimiter #"\n" = true
            | delimiter _ = false
          val tokens_list = String.tokens delimiter problem
        in
          (case tokens_list of
            name::conjecture::_ => 
              ((Prover.prove @{context} name conjecture 
                handle Fail message => writeln ("Fail for problem: " ^ name ^ ": " ^ conjecture ^"\n" ^ message))
               ; read_line inStream)
          | _ => (writeln ("Malformed problem line: " ^ problem); read_line inStream)
          )
        end
      )

    val line = read_line inStream

    val _ = TextIO.closeIn inStream
  in
    line
  end
\<close>  
  
ML\<open>
val problems_file = "/home/cristina/Documents/internship/verified-metitarski/proof_reconstruction/translations/problems.in";

read_conjectures problems_file
\<close>  
  
end
  