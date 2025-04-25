(* File: asmcomp/printllvm.ml *)
open Format
open Linear

(* Track register mappings for SSA form *)
let reg_counter = ref 0
let reg_names = Hashtbl.create 100

let get_reg_name reg =
  try Hashtbl.find reg_names reg
  with Not_found ->
    let name = "%r" ^ string_of_int !reg_counter in
    incr reg_counter;
    Hashtbl.add reg_names reg name;
    name

let label_name lbl = "L" ^ string_of_int lbl

(* Print Linear operation as LLVM instruction *)
let print_operation ppf op args res =
  match op with
  | Mach.Imove ->
      fprintf ppf "  %s = add i32 %s, 0 ; move" 
        (get_reg_name res.(0)) (get_reg_name args.(0))
  | Mach.Iintop(Mach.Iadd) ->
      fprintf ppf "  %s = add i32 %s, %s" 
        (get_reg_name res.(0)) (get_reg_name args.(0)) (get_reg_name args.(1))
  | Mach.Iintop(Mach.Isub) ->
      fprintf ppf "  %s = sub i32 %s, %s" 
        (get_reg_name res.(0)) (get_reg_name args.(0)) (get_reg_name args.(1))
  | Mach.Iconst_int(n) ->
      fprintf ppf "  %s = add i32 0, %nd" 
        (get_reg_name res.(0)) n
  | _ ->
      fprintf ppf "  ; unsupported operation"

(* Print Linear instruction as LLVM IR *)
let instr ppf i =
  match i.desc with
  | Lend -> ()
  | Lprologue ->
      fprintf ppf "  ; function prologue"
  | Lop op ->
      print_operation ppf op i.arg i.res
  | Lreturn ->
      if Array.length i.arg > 0 then
        fprintf ppf "  ret i32 %s" (get_reg_name i.arg.(0))
      else
        fprintf ppf "  ret void"
  | Llabel lbl ->
      fprintf ppf "%s:" (label_name lbl)
  | Lbranch lbl ->
      fprintf ppf "  br label %%%s" (label_name lbl)
  | _ ->
      fprintf ppf "  ; unsupported instruction"

(* Process all instructions in a function *)
let rec all_instr ppf i =
  match i.desc with
  | Lend -> ()
  | _ -> 
      fprintf ppf "%a@," instr i;
      all_instr ppf i.next

(* Main entry point *)
let fundecl ppf f =
  reg_counter := 0;
  Hashtbl.clear reg_names;
  fprintf ppf "; Function: %s@," f.fun_name;
  fprintf ppf "define i32 @%s() {@," f.fun_name;
  fprintf ppf "entry:@,";
  all_instr ppf f.fun_body;
  fprintf ppf "}@,"
