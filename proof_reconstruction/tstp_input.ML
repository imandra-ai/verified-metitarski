signature TSTP_INPUT = 
sig
    val read : string -> string
end;

structure TSTP_Input : TSTP_INPUT = 
struct

fun read file =
    let val inStream = TextIO.openIn file
        fun line_by_line stream = 
        case TextIO.inputLine stream of
            SOME s => s ^ (line_by_line stream)
           |NONE => ""
    in
        line_by_line inStream   
    end

end;

(*tstp_input.read "Documents/internship/verified-metitarski/problems/cristina-problem-5.tstpout"*)
(*tstp_input.read "Documents/internship/verified-metitarski/proof_reconstruction/input.txt"*)
