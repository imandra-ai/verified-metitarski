signature CALL_METITARSKI =
sig
  val call_mt : string -> string
end;

structure Call_Metitarski : CALL_METITARSKI =
struct

fun call_mt (tptp_problem : string) :string =
  let
    val problem_path = "/home/cristina/problem.tptp"
    
    (*Write the tptp_problem to a file*)
    fun write (file : string) (text : string) =
      let
        val out_str = TextIO.openOut file
        val _ = TextIO.output (out_str, text)
        val _ = TextIO.closeOut out_str
      in
        ()
      end
    
    val _ = write problem_path tptp_problem
    
    (*Run MT on this problem*)
    val mt_path = "/home/cristina/Documents/internship/metitarski/metit"
    val mt_args = ["-p", "--cases", "0", "--autoInclude", problem_path];
    
    val mt_process = Unix.execute(mt_path, mt_args)
    
    val in_str = Unix.textInstreamOf mt_process
    
    val tptp_proof = 
      let
        fun read_input acc = 
          (case TextIO.inputLine in_str of
            SOME str => read_input (str::acc)
          | NONE => String.concat (List.rev acc)
          )
      in
        read_input []
      end
    
    val _ = TextIO.closeIn in_str
    
    (*For debugging *)
    (*Functions for printing a signal from Mathematica.sml*)
    (*fun string_of_signal s =
        if s = Posix.Signal.hup then "Hangup"
        else if s = Posix.Signal.ill then "Illegal instruction"
        else if s = Posix.Signal.int then "Interrupt"
        else if s = Posix.Signal.kill then "Kill"
        else if s = Posix.Signal.segv then "Segmentation violation"
        else if s = Posix.Signal.bus then "Bus error"
        else "signalled " ^ SysWord.toString (Posix.Signal.toWord s);
    
    fun stringOfStatus Unix.W_EXITED = "exited"
      | stringOfStatus (Unix.W_EXITSTATUS w) = "exit " ^ Word8.toString w
      | stringOfStatus (Unix.W_SIGNALED s) = string_of_signal s
      | stringOfStatus (Unix.W_STOPPED _) = "stopped"
    
    val status = stringOfStatus (Unix.fromStatus (Unix.reap mt_process))
    *)
  in
    tptp_proof
  end

end;