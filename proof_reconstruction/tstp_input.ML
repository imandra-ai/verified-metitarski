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
        val input_string = line_by_line inStream
        val _ = TextIO.closeIn inStream
    in
        input_string   
    end

end;
