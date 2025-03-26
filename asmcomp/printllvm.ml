(* File: asmcomp/printllvm.ml *)
open Format
open Linear

let fundecl ppf (f : fundecl) =
  fprintf ppf "@[<v 2>; LLVM IR for %s@," f.fun_name