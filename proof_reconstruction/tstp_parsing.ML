structure tstp_Parsing = 
struct

open ATP_Proof
open ATP_Util
open ATP_Problem
open ATP_Satallax


end;

tstp_Parsing.hash_string "abc";
ATP_Satallax.atp_proof_of_tstplike_proof "" [("", [ATP_Problem.Class_Decl("", "", [])])] "";

fun read file =
let val inStream = TextIO.openIn file

in
        TextIO.input1 inStream
end;
(* read "home/cristina/Documents/internship/verified-metitarski/problems/cristina-problem-5.tstpout"*)
read "home/cristina/Documents/internship/verified-metitarski/proof_reconstruction/input.txt"


