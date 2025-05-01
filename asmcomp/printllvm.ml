(* File: asmcomp/printllvm.ml *)
open Format
open Linear

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
    | Cmm.CFnlt -> "uge"  
    | Cmm.CFle -> "ole"
    | Cmm.CFnle -> "ugt"  
    | Cmm.CFgt -> "ogt"
    | Cmm.CFngt -> "ule"  
    | Cmm.CFge -> "oge"
    | Cmm.CFnge -> "ult"  

let print_intop ppf op args res =
    let print_binop opcode arg1 arg2 =
        fprintf ppf "%s = %s i32 %s, %s" res opcode arg1 arg2
    in
    match op with
    | Mach.Iadd -> print_binop "add" args.(0) args.(1)
    | Mach.Isub -> print_binop "sub" args.(0) args.(1)
    | Mach.Imul -> print_binop "mul" args.(0) args.(1)
    | Mach.Imulh ->
        fprintf ppf "%%tmp64_%d = sext i32 %s to i64@," !reg_counter args.(0);
        fprintf ppf "%%tmp64_%d = sext i32 %s to i64@," (!reg_counter + 1) args.(1);
        fprintf ppf "%s = call i64 @llvm.smulh.i64(i64 %%tmp64_%d, i64 %%tmp64_%d)@," 
            res !reg_counter (!reg_counter + 1);
        fprintf ppf "%s = trunc i64 %s to i32" res res;
        reg_counter := !reg_counter + 2
    | Mach.Idiv -> print_binop "sdiv" args.(0) args.(1)
    | Mach.Imod -> print_binop "srem" args.(0) args.(1)
    | Mach.Iand -> print_binop "and" args.(0) args.(1)
    | Mach.Ior -> print_binop "or" args.(0) args.(1)
    | Mach.Ixor -> print_binop "xor" args.(0) args.(1)
    | Mach.Ilsl -> print_binop "shl" args.(0) args.(1)
    | Mach.Ilsr -> print_binop "lshr" args.(0) args.(1)
    | Mach.Iasr -> print_binop "ashr" args.(0) args.(1)
    | Mach.Icomp cmp ->
        let pred = match cmp with
            | Mach.Isigned c -> llvm_int_pred c
            | Mach.Iunsigned c -> llvm_uint_pred c in
        fprintf ppf "%%cmp_%d = icmp %s i32 %s, %s@," !reg_counter pred args.(0) args.(1);
        fprintf ppf "%s = zext i1 %%cmp_%d to i32" res !reg_counter;
        incr reg_counter
    | Mach.Icheckbound ->
        fprintf ppf "%%bound_%d = icmp ult i32 %s, %s@," !reg_counter args.(0) args.(1);
        fprintf ppf "br i1 %%bound_%d, label %%continue, label %%bounds_fail" !reg_counter;
        incr reg_counter

let print_intop_imm ppf op arg n res =
    let imm_reg = Printf.sprintf "%%imm_%d" !reg_counter in
    fprintf ppf "%s = add i32 0, %d@," imm_reg n;
    incr reg_counter;
    print_intop ppf op [|arg; imm_reg|] res

let llvm_of_exttype = function
    | Cmm.XInt -> "i32"   
    | Cmm.XInt32 -> "i32" 
    | Cmm.XInt64 -> "i64"
    | Cmm.XFloat -> "double" 

let llvm_of_machtype = function
    | Cmm.Val -> "i32"   
    | Cmm.Addr -> "i64"  
    | Cmm.Int -> "i32"   
    | Cmm.Float -> "double" 

(* Print Mach operation as LLVM instruction *)
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

    | Mach.Ispill ->
        fprintf ppf "%s = alloca i32, align 4@," (get_reg_name res.(0));
        fprintf ppf "store i32 %s, i32* %s"
            (get_reg_name args.(0)) (get_reg_name res.(0))

    | Mach.Ireload ->
        fprintf ppf "%s = load i32, i32* %s" 
            (get_reg_name res.(0)) (get_reg_name args.(0))

    | Mach.Iconst_int n ->
        fprintf ppf "%s = add i32 0, %nd"
            (get_reg_name res.(0)) n

    | Mach.Iconst_float f ->
        fprintf ppf "%s = bitcast i64 %Ld to double" 
            (get_reg_name res.(0)) f

    | Mach.Iconst_symbol s ->
        fprintf ppf "@%s = private unnamed_addr constant [%d x i8] c\"%s\\00\"@," 
            s (String.length s + 1) s;
        fprintf ppf "%s = getelementptr inbounds [%d x i8], [%d x i8]* @%s, i64 0, i64 0"
            (get_reg_name res.(0)) 
            (String.length s + 1) (String.length s + 1) s
    
    | Mach.Icall_ind ->
        let args_str = 
            Array.sub args 1 (Array.length args - 1)
            |> Array.map get_reg_name
            |> Array.to_list  
            |> String.concat ", " in
        fprintf ppf "%s = call fastcc i32 %s(%s)"
            (get_reg_name res.(0)) 
            (get_reg_name args.(0))
            args_str

    | Mach.Icall_imm { func } ->
        let args_str = 
            Array.map get_reg_name args
            |> Array.to_list
            |> String.concat ", " in
        (match Array.length res with
        | 0 -> 
            fprintf ppf "call fastcc void @%s(%s)" func args_str
        | 1 -> 
            fprintf ppf "%s = call fastcc i32 @%s(%s)"
                (get_reg_name res.(0))
                func
                args_str
        | _ -> 
            failwith "Unsupported multi-register return")

    | Mach.Itailcall_ind ->
        let args_str = 
            Array.sub args 1 (Array.length args - 1)
            |> Array.map get_reg_name
            |> Array.to_list 
            |> String.concat ", " in
        fprintf ppf "tail call fastcc i32 %s(%s)"
            (get_reg_name args.(0))
            args_str

    | Mach.Itailcall_imm { func } ->
        let args_str = 
            Array.map get_reg_name args
            |> Array.to_list 
            |> String.concat ", " in
        fprintf ppf "tail call fastcc i32 @%s(%s)"
            func
            args_str

    | Mach.Iextcall { func; ty_res; ty_args; alloc; stack_ofs } ->
        let args_str =
            List.mapi (fun i ty ->
                let reg = get_reg_name args.(i) in
                let ty_str = llvm_of_exttype ty in
                Printf.sprintf "%s %s" ty_str reg
            ) ty_args
            |> String.concat ", "
        in
        let ret_str = 
            match Array.length res with
            | 0 -> "void"
            | 1 -> llvm_of_machtype ty_res.(0)
            | _ -> failwith "Multiple return values not supported"
        in
        let noalloc_str = if alloc then "" else " (noalloc)" in
        (match Array.length res with
        | 0 ->
            fprintf ppf "call %s @%s(%s) ; stack_ofs = %d%s"
                ret_str func args_str stack_ofs noalloc_str
        | 1 ->
            fprintf ppf "%s = call %s @%s(%s) ; stack_ofs = %d%s"
                (get_reg_name res.(0)) ret_str func args_str stack_ofs noalloc_str
        | _ -> failwith "Unsupported multi-result extcall")

    | Mach.Istackoffset n ->
        fprintf ppf "%s = alloca i8, i64 %d, align 16" 
            (get_reg_name res.(0)) n

    | Mach.Iload { memory_chunk; addressing_mode; mutability; is_atomic } ->
        let ty, _ = match memory_chunk with
            | Cmm.Byte_unsigned -> ("i8", " zext")
            | Cmm.Byte_signed -> ("i8", " sext")
            | Cmm.Sixteen_unsigned -> ("i16", " zext")
            | Cmm.Sixteen_signed -> ("i16", " sext")
            | Cmm.Thirtytwo_unsigned -> ("i32", " zext")
            | Cmm.Thirtytwo_signed -> ("i32", " sext")
            | Cmm.Word_int -> ("i64", "")    
            | Cmm.Word_val -> ("i64", "")    
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
            | Cmm.Word_int | Cmm.Word_val -> ("i64", 8) 
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
                
                let scaled_idx_reg = !reg_counter in
                fprintf ppf "%%scaled_idx_%d = mul i64 %s, %d@," 
                    scaled_idx_reg index_reg scale;
                incr reg_counter;
                
                let addr_reg = !reg_counter in
                fprintf ppf "%%addr_%d = getelementptr inbounds i8, i8* %s, i64 %%scaled_idx_%d@,"
                    addr_reg base_reg scaled_idx_reg;
                incr reg_counter;
                sprintf "%%addr_%d" addr_reg

            | _ -> get_reg_name args.(1) in
            let ptr_reg = !reg_counter in
            fprintf ppf "%%ptr_%d = bitcast i8* %s to %s*@,\
                        store %s %s, %s* %%ptr_%d align %d@,\
                        ; %s"
                ptr_reg addr_str ty
                ty (get_reg_name args.(0)) ty ptr_reg align
                (if is_assign then "assignment" else "initialization");
            incr reg_counter;

    | Mach.Ialloc { bytes } ->
        let words = bytes / 8 in  
        fprintf ppf "%s = call fastcc i8* @caml_alloc(i64 %d, i64 0)"
            (get_reg_name res.(0)) words

    | Mach.Iintop op ->
        let args = Array.map get_reg_name args in
        let res = get_reg_name res.(0) in
        print_intop ppf op args res
    
    | Mach.Iintop_imm(op, n) ->
        let arg = get_reg_name args.(0) in
        let res = get_reg_name res.(0) in
        print_intop_imm ppf op arg n res

    | Mach.Icompf cmp ->
        let args = Array.map get_reg_name args in
        let res = get_reg_name res.(0) in
        let pred = llvm_float_pred cmp in
        fprintf ppf "%%cmp_%d = fcmp %s double %s, %s@," 
            !reg_counter pred args.(0) args.(1);
        fprintf ppf "%s = zext i1 %%cmp_%d to i32" 
            res !reg_counter;
        incr reg_counter

    | Mach.Inegf ->
        fprintf ppf "%s = fneg double %s"
            (get_reg_name res.(0)) (get_reg_name args.(0))

    | Mach.Iabsf ->
        fprintf ppf "%s = call double @llvm.fabs.f64(double %s)"
            (get_reg_name res.(0)) (get_reg_name args.(0))

    | Mach.Iaddf ->
        fprintf ppf "%s = fadd double %s, %s"
            (get_reg_name res.(0)) (get_reg_name args.(0)) (get_reg_name args.(1))

    | Mach.Isubf ->
        fprintf ppf "%s = fsub double %s, %s"
            (get_reg_name res.(0)) (get_reg_name args.(0)) (get_reg_name args.(1))

    | Mach.Imulf ->
        fprintf ppf "%s = fmul double %s, %s"
            (get_reg_name res.(0)) (get_reg_name args.(0)) (get_reg_name args.(1))

    | Mach.Idivf ->
        fprintf ppf "%s = fdiv double %s, %s"
            (get_reg_name res.(0)) (get_reg_name args.(0)) (get_reg_name args.(1))

    | Mach.Ifloatofint ->
        fprintf ppf "%s = sitofp i32 %s to double"
            (get_reg_name res.(0)) (get_reg_name args.(0))

    | Mach.Iintoffloat ->
        fprintf ppf "%s = fptosi double %s to i32"
            (get_reg_name res.(0)) (get_reg_name args.(0))

    | Mach.Iopaque ->
        (* Opaque operation - treat as no-op but preserve value *)
        fprintf ppf "%s = add i32 %s, 0" 
            (get_reg_name res.(0)) (get_reg_name args.(0))
    
    (* | Mach.Ispecific op ->
        (* Architecture-specific operation *)
        Arch.print_specific_operation (Array.map get_reg_name args) (get_reg_name res.(0)) ppf op *)

    | Mach.Idls_get ->
        (* Dynamic linker symbol resolution *)
        fprintf ppf "%s = call i8* @caml_dlsym(i8* %s)"
            (get_reg_name res.(0)) (get_reg_name args.(0))

    (* | Mach.Ireturn_addr ->
        (* Return address - architecture specific *)
        (match Arch.return_addr_operation with
            | Some f -> f (get_reg_name res.(0)) ppf
            | None -> 
                fprintf ppf "%s = call i8* @llvm.returnaddress(i32 0)"
                    (get_reg_name res.(0))) *)

    | Mach.Ipoll { return_label } ->
        (* Poll point for async checks *)
        fprintf ppf ";; poll point@.";
        fprintf ppf "%%poll_%d = call i32 @caml_poll(i32 0)@;" !reg_counter;
        fprintf ppf "%%needs_%d = icmp ne i32 %%poll_%d, 0@;" !reg_counter !reg_counter;
        fprintf ppf "br i1 %%needs_%d, label %%async_handler, label %%continue@;" !reg_counter;
        (match return_label with
            | None -> ()
            | Some lbl ->
                fprintf ppf "async_handler:@.";
                fprintf ppf "  call void @caml_async_handler(i64 %d)@;" lbl;
                fprintf ppf "  br label %%continue" );
        incr reg_counter

    | _ -> fprintf ppf "; UNSUPPORTED OPERATION"

(* Print Linear instruction as LLVM IR *)
let instr ppf i =
    match i.desc with
    | Lend -> ()

    | Lprologue ->
        fprintf ppf "  ; prologue@,"

    | Lop op ->
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
        fprintf ppf "  ; %s %s@," raise_str (get_reg_name i.arg.(0));
    if not (Debuginfo.is_none i.dbg) && !Clflags.locations then
        fprintf ppf "  ; %s@," (Debuginfo.to_string i.dbg)

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