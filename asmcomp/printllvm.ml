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

(* Helper functions to convert Cmm comparisons to LLVM predicates *)

let llvm_int_pred = function
  | Cmm.Ceq -> "eq"
  | Cmm.Cne -> "ne"
  | Cmm.Clt -> "slt"
  | Cmm.Cle -> "sle"
  | Cmm.Cgt -> "sgt"
  | Cmm.Cge -> "sge"

let llvm_uint_pred = function
  | Cmm.Ceq -> "eq"
  | Cmm.Cne -> "ne"
  | Cmm.Clt -> "ult"
  | Cmm.Cle -> "ule"
  | Cmm.Cgt -> "ugt"
  | Cmm.Cge -> "uge"

let llvm_float_pred = function
  | Cmm.CFeq -> "oeq"
  | Cmm.CFneq -> "une"
  | Cmm.CFlt -> "olt"
  | Cmm.CFnlt -> "uge"  (* Not less than = greater or equal *)
  | Cmm.CFle -> "ole"
  | Cmm.CFnle -> "ugt"  (* Not less or equal = greater *)
  | Cmm.CFgt -> "ogt"
  | Cmm.CFngt -> "ule"  (* Not greater than = less or equal *)
  | Cmm.CFge -> "oge"
  | Cmm.CFnge -> "ult"  (* Not greater or equal = less than *)


(* Print Linear operation as LLVM instruction *)
let print_operation ppf (op, args, res) =
    (* Create mapping from register names to argument indices *)
    let reg_name_to_index =
      let tbl = Hashtbl.create (Array.length args) in
      Array.iteri (fun idx reg -> 
        Hashtbl.add tbl (get_reg_name reg) idx
      ) args;
      tbl
    in
  match op with
  | Mach.Imove ->
      fprintf ppf "%s = add i32 %s, 0"
        (get_reg_name res.(0)) (get_reg_name args.(0))

  | Mach.Iintop Mach.Iadd ->
      fprintf ppf "%s = add i32 %s, %s"
        (get_reg_name res.(0)) (get_reg_name args.(0)) (get_reg_name args.(1))

  | Mach.Iintop Mach.Isub ->
      fprintf ppf "%s = sub i32 %s, %s"
        (get_reg_name res.(0)) (get_reg_name args.(0)) (get_reg_name args.(1))

  | Mach.Iintop Mach.Imul ->
      fprintf ppf "%s = mul i32 %s, %s"
        (get_reg_name res.(0)) (get_reg_name args.(0)) (get_reg_name args.(1))

  | Mach.Iconst_int n ->
      fprintf ppf "%s = add i32 0, %nd"
        (get_reg_name res.(0)) n

  | Mach.Iload { memory_chunk; addressing_mode; mutability; is_atomic } ->
    let ty, _ = match memory_chunk with
      | Cmm.Byte_unsigned -> ("i8", " zext")
      | Cmm.Byte_signed -> ("i8", " sext")
      | Cmm.Sixteen_unsigned -> ("i16", " zext")
      | Cmm.Sixteen_signed -> ("i16", " sext")
      | Cmm.Thirtytwo_unsigned -> ("i32", " zext")
      | Cmm.Thirtytwo_signed -> ("i32", " sext")
      | Cmm.Word_int -> ("i64", "")    (* OCaml unboxed integers *)
      | Cmm.Word_val -> ("i64", "")    (* OCaml boxed values *)
      | _ -> ("i32", "") in
    
    let addr_str = match addressing_mode with
      | Arch.Ibased(base_name, displ) ->
          let base_idx = Hashtbl.find reg_name_to_index base_name in
          let base_reg = get_reg_name args.(base_idx) in
          fprintf ppf "%%addr_%d = getelementptr i8, i8* %s, i32 %d@,"
            !reg_counter base_reg displ;
          sprintf "%%addr_%d" !reg_counter
      | _ -> get_reg_name args.(0) in
    
    let atomic = if is_atomic then " atomic" else "" in
    let ordering = if is_atomic then " monotonic" else "" in
    
    fprintf ppf "%%ptr_%d = bitcast i8* %s to %s*@,\
                %s = load%s%s %s, %s* %%ptr_%d align 1@,\
                ; mutability: %a"
      !reg_counter addr_str ty
      (get_reg_name res.(0)) atomic ordering ty ty !reg_counter
      (fun pp -> function
        | Asttypes.Mutable -> fprintf pp "mutable"
        | Asttypes.Immutable -> fprintf pp "immutable") mutability

    | Mach.Istore (memory_chunk, addressing_mode, is_assign) ->
      let ty, align = match memory_chunk with
        | Cmm.Byte_unsigned | Cmm.Byte_signed -> ("i8", 1)
        | Cmm.Sixteen_unsigned | Cmm.Sixteen_signed -> ("i16", 2)
        | Cmm.Thirtytwo_unsigned | Cmm.Thirtytwo_signed -> ("i32", 4)
        | Cmm.Word_int | Cmm.Word_val -> ("i64", 8)  (* 64-bit alignment *)
        | _ -> ("i32", 4) in
      
      let addr_str = match addressing_mode with
        | Arch.Ibased(base_name, displ) ->
            let base_idx = Hashtbl.find reg_name_to_index base_name in
            let base_reg = get_reg_name args.(base_idx) in
            fprintf ppf "%%addr_%d = getelementptr inbounds i8, i8* %s, i64 %d@,"
              !reg_counter base_reg displ;
            let addr_reg = !reg_counter in
            incr reg_counter;
            sprintf "%%addr_%d" addr_reg
  
        | Arch.Iindexed scale ->
            let base_reg = get_reg_name args.(0) in
            let index_reg = get_reg_name args.(1) in
            (* Generate scaled index *)
            let scaled_idx_reg = !reg_counter in
            fprintf ppf "%%scaled_idx_%d = mul i64 %s, %d@," 
              scaled_idx_reg index_reg scale;
            incr reg_counter;
            (* Generate address *)
            let addr_reg = !reg_counter in
            fprintf ppf "%%addr_%d = getelementptr inbounds i8, i8* %s, i64 %%scaled_idx_%d@,"
              addr_reg base_reg scaled_idx_reg;
            incr reg_counter;
            sprintf "%%addr_%d" addr_reg
  
        | _ -> get_reg_name args.(1) in
          
          (* Generate pointer cast and store *)
          let ptr_reg = !reg_counter in
          fprintf ppf "%%ptr_%d = bitcast i8* %s to %s*@,\
                      store %s %s, %s* %%ptr_%d align %d@,\
                      ; %s"
            ptr_reg addr_str ty
            ty (get_reg_name args.(0)) ty ptr_reg align
            (if is_assign then "assignment" else "initialization");
          incr reg_counter;  (* Increment after ptr_reg *)
      
            

  (* | Mach.Icall_ind | Mach.Icall_imm _ | Mach.Iextcall _ ->
      let callee = match op with
        | Mach.Icall_imm func -> "@" ^ func
        | Mach.Iextcall (func, _) -> "@" ^ func
        | _ -> get_reg_name args.(0) in
      fprintf ppf "%s = call i32 %s(%a)"
        (get_reg_name res.(0)) callee
        (pp_print_array ~pp_sep:(fun ppf () -> fprintf ppf ", ") get_reg_name) args *)

  | _ -> fprintf ppf "; UNSUPPORTED OPERATION"


  (* Print Linear instruction as LLVM IR *)
let instr ppf i =
  match i.desc with
  | Lend -> ()

  | Lprologue ->
      fprintf ppf "  ; prologue@,"

  | Lop op ->
      (match op with
      | Mach.Ialloc _ -> fprintf ppf "  ; allocation@,"
      | Mach.Ipoll _ -> fprintf ppf "  ; poll@,"
      | Mach.Icall_ind | Mach.Icall_imm _ | Mach.Iextcall _ ->
          fprintf ppf "  ; call prep@,"
      | _ -> ());
      fprintf ppf "  %a@," print_operation (op, i.arg, i.res)

  | Lreloadretaddr ->
      fprintf ppf "  ; reload retaddr@,"

  | Lreturn ->
      if Array.length i.arg > 0 then
        fprintf ppf "  ret i32 %s@," (get_reg_name i.arg.(0))
      else
        fprintf ppf "  ret void@,"

  | Llabel lbl ->
      fprintf ppf "%s:@," (label_name lbl)

  | Lbranch lbl ->
      fprintf ppf "  br label %%%s@," (label_name lbl)
 
  | Lcondbranch(tst, lbl) ->
    let cmp_reg = !reg_counter in
    incr reg_counter;
    
    (match tst with
      | Mach.Itruetest ->
          fprintf ppf "%%cond_%d = icmp ne i32 %s, 0@," 
            cmp_reg (get_reg_name i.arg.(0))
      
      | Mach.Ifalsetest ->
          fprintf ppf "%%cond_%d = icmp eq i32 %s, 0@," 
            cmp_reg (get_reg_name i.arg.(0))
      
      | Mach.Iinttest cmp ->
        let pred = match cmp with
          | Mach.Isigned c -> llvm_int_pred c
          | Mach.Iunsigned c -> llvm_uint_pred c in
        fprintf ppf "%%cond_%d = icmp %s i32 %s, %s@," 
          cmp_reg pred (get_reg_name i.arg.(0)) (get_reg_name i.arg.(1))
      
      | Mach.Iinttest_imm(cmp, n) ->
        let pred = match cmp with
          | Mach.Isigned c -> llvm_int_pred c
          | Mach.Iunsigned c -> llvm_uint_pred c in
        fprintf ppf "%%cond_%d = icmp %s i32 %s, %d@," 
          cmp_reg pred (get_reg_name i.arg.(0)) n
      
      | Mach.Ifloattest cmp ->
          let pred = llvm_float_pred cmp in
          fprintf ppf "%%cond_%d = fcmp %s double %s, %s@," 
            cmp_reg pred (get_reg_name i.arg.(0)) (get_reg_name i.arg.(1))
      
      | Mach.Ieventest ->
          fprintf ppf "%%and_%d = and i32 %s, 1@," 
            cmp_reg (get_reg_name i.arg.(0));
          fprintf ppf "%%cond_%d = icmp eq i32 %%and_%d, 0@," 
            cmp_reg cmp_reg
      
      | Mach.Ioddtest ->
          fprintf ppf "%%and_%d = and i32 %s, 1@," 
            cmp_reg (get_reg_name i.arg.(0));
          fprintf ppf "%%cond_%d = icmp ne i32 %%and_%d, 0@," 
            cmp_reg cmp_reg);
    
    fprintf ppf "br i1 %%cond_%d, label %%%s, label %%next@," 
      cmp_reg (label_name lbl)

  | Lcondbranch3(lbl0, lbl1, lbl2) ->
      fprintf ppf "  switch i32 %s, label %%next [@,"
        (get_reg_name i.arg.(0));
      let emit_case idx lbl_opt =
        match lbl_opt with
        | Some lbl ->
            fprintf ppf "    i32 %d, label %%%s@," idx (label_name lbl)
        | None -> ()
      in
      emit_case 0 lbl0;
      emit_case 1 lbl1;
      emit_case 2 lbl2;
      fprintf ppf "  ]@,"

  | Lswitch lblv ->
      fprintf ppf "  switch i32 %s, label %%default [@," (get_reg_name i.arg.(0));
      Array.iteri (fun idx lbl ->
        fprintf ppf "    i32 %d, label %%%s@," idx (label_name lbl)
      ) lblv;
      fprintf ppf "  ]@,"

  | Lentertrap ->
      fprintf ppf "  ; enter trap@,"

  | Ladjust_trap_depth { delta_traps } ->
      fprintf ppf "  ; adjust trap depth by %d@," delta_traps

  | Lpushtrap { lbl_handler } ->
      fprintf ppf "  ; push trap %s@," (label_name lbl_handler)

  | Lpoptrap ->
      fprintf ppf "  ; pop trap@,"

  | Lraise k ->
      let raise_str = match k with
        | Lambda.Raise_regular -> "raise"
        | Lambda.Raise_reraise -> "reraise"
        | Lambda.Raise_notrace -> "raise_notrace" in
      fprintf ppf "  ; %s %s@," raise_str (get_reg_name i.arg.(0))
  ;
  if not (Debuginfo.is_none i.dbg) && !Clflags.locations then
    fprintf ppf "  ; %s@," (Debuginfo.to_string i.dbg)

(* Process all instructions in a function *)
let rec all_instr ppf i =
  match i.desc with
  | Lend -> ()
  | _ ->
      fprintf ppf "%a" instr i;
      all_instr ppf i.next

(* Main entry point *)
let fundecl ppf f =
  reg_counter := 0;
  Hashtbl.clear reg_names;
  fprintf ppf "@[<v 2>define i32 @%s() {@," f.fun_name;
  fprintf ppf "entry:@,%a@]@," all_instr f.fun_body;
  fprintf ppf "}@."
