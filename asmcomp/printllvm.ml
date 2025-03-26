(* File: asmcomp/printllvm.ml *)
open Format
open Llvm
open Linear

(* Global LLVM context *)
let context = global_context ()
let the_module = create_module context "ocaml_module"
let builder = builder context

(* Track basic blocks and register mappings *)
let label_blocks : (label, llbasicblock) Hashtbl.t = Hashtbl.create 10
let reg_map : (Reg.t, llvalue) Hashtbl.t = Hashtbl.create 100
let current_function = ref (dummy_function context)

(* Helper functions *)
let llvm_type = i32_type context  (* Assuming 32-bit integers for simplicity *)
let label_name l = "L" ^ string_of_int l

(* Convert Mach operations to LLVM instructions *)
let translate_operation op args builder =
  match op with
  | Iadd -> build_add args.(0) args.(1) "addtmp" builder
  | Isub -> build_sub args.(0) args.(1) "subtmp" builder 
  | Imul -> build_mul args.(0) args.(1) "multmp" builder
  | Ialloc _ -> build_alloca llvm_type "alloc" builder
  | _ -> failwith "Unsupported operation"

(* Convert Linear instructions to LLVM *)
let rec translate_instr i current_block =
  match i.desc with
  | Lprologue ->
      (* Function prologue setup *)
      let entry = entry_block !current_function in
      position_at_end entry builder
  
  | Lop op ->
      let args = Array.map (fun r -> Hashtbl.find reg_map r) i.arg in
      let res = translate_operation op args builder in
      Hashtbl.replace reg_map i.res.(0) res
  
  | Lreturn ->
      let ret_val = Hashtbl.find reg_map i.arg.(0) in
      ignore (build_ret ret_val builder)
  
  | Llabel lbl ->
      let bb = append_block context (label_name lbl) !current_function in
      Hashtbl.add label_blocks lbl bb;
      position_at_end bb builder
  
  | Lbranch lbl ->
      let target = Hashtbl.find label_blocks lbl in
      ignore (build_br target builder)
  
  | Lcondbranch(test, lbl) ->
      let cond = Hashtbl.find reg_map i.arg.(0) in
      let true_bb = Hashtbl.find label_blocks lbl in
      let false_bb = append_block context "fallthrough" !current_function in
      ignore (build_cond_br cond true_bb false_bb builder);
      position_at_end false_bb builder
  
  | Lpushtrap { lbl_handler } ->
      let handler_bb = Hashtbl.find label_blocks lbl_handler in
      let normal_bb = append_block context "normal" !current_function in
      ignore (build_invoke (Hashtbl.find reg_map i.arg.(0)) [||] normal_bb handler_bb "invoke" builder)
  
  | Lpoptrap ->
      ignore (build_resume (const_null llvm_type) builder)
  
  | _ -> ()  (* Other cases omitted for brevity *)

(* Process all instructions in a function *)
let process_function fdecl =
  (* Reset state *)
  Hashtbl.clear reg_map;
  Hashtbl.clear label_blocks;
  
  (* Create function type *)
  let param_types = Array.make (Reg.Set.cardinal fdecl.fun_args) llvm_type in
  let func_type = function_type llvm_type param_types in
  let func = define_function fdecl.fun_name func_type the_module in
  current_function := func;
  
  (* Map parameters to registers *)
  Array.iteri (fun i reg ->
    let param = param func i in
    Hashtbl.add reg_map reg param
  ) (Reg.Set.elements fdecl.fun_args |> Array.of_list);
  
  (* Process instruction chain *)
  let rec process i =
    if i != end_instr then (
      translate_instr i (insertion_block builder);
      process i.next
    )
  in
  process fdecl.fun_body

(* Public API *)  
let fundecl ppf f =
  process_function f;
  dump_module the_module
