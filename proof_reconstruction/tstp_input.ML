signature TSTP_INPUT = 
sig
    val read : string -> string
end;

structure TSTP_Input : TSTP_INPUT = 
struct

(* Also remove lines before the beginning of the proof. Works in SML but not Isabelle/ML *)
fun read file =
    let val sawFirstLine = Unsynchronized.ref false
        val inStream = TextIO.openIn file
        fun line_by_line stream = 
            case TextIO.inputLine stream of
                SOME s => if not(!sawFirstLine) andalso not(String.isPrefix "cnf" s) andalso not(String.isPrefix "fof" s)  
                          then line_by_line stream
                          else if not(!sawFirstLine) 
                               then (sawFirstLine := true; s ^ (line_by_line stream))
                               else s ^ (line_by_line stream)                                    
               |NONE => ""
        val input_string = line_by_line inStream
        val _ = TextIO.closeIn inStream
    in
        input_string   
    end

end;

(*TSTP_Input.read "Documents/internship/verified-metitarski/proof_reconstruction/input.txt";*)
