#use "semantic-analyser.ml";;
open Semantics;;

(* This module is here for you convenience only!
   You are not required to use it.
   you are allowed to change it. *)
module type CODE_GEN = sig
  (* This signature assumes the structure of the constants table is
     a list of key-value pairs:
     - The keys are constant values (Sexpr(x) or Void)
     - The values are pairs of:
       * the offset from the base const_table address in bytes; and
       * a string containing the byte representation (or a sequence of nasm macros)
         of the constant value
     For example: [(Sexpr(Nil), (1, "T_NIL"))]
   *)
  val make_consts_tbl : expr' list -> (constant * (int * string)) list

  (* This signature assumes the structure of the fvars table is
     a list of key-value pairs:
     - The keys are the fvar names as strings
     - The values are the offsets from the base fvars_table address in bytes
     For example: [("boolean?", 0)]
   *)  
  val make_fvars_tbl : expr' list -> (string * int) list

  (* If you change the types of the constants and fvars tables, you will have to update
     this signature to match: The first argument is the constants table type, the second 
     argument is the fvars table type, and the third is an expr' that has been annotated 
     by the semantic analyser.
   *)
  val generate : (constant * (int * string)) list -> (string * int) list -> expr' -> string
end;;

(*module Code_Gen : CODE_GEN = struct*)
  (*Primitives*)
  let primitive_names_to_labels =
  [
    (* Type queries  *)
    "boolean?", "boolean?"; "flonum?", "flonum?"; "rational?", "rational?";
    "pair?", "pair?"; "null?", "null?"; "char?", "char?"; "string?", "string?";
    "procedure?", "procedure?"; "symbol?", "symbol?";
    (* String procedures *)
    "string-length", "string_length"; "string-ref", "string_ref"; "string-set!", "string_set";
    "make-string", "make_string"; "symbol->string", "symbol_to_string";
    (* Type conversions *)
    "char->integer", "char_to_integer"; "integer->char", "integer_to_char"; "exact->inexact", "exact_to_inexact";
    (* Identity test *)
    "eq?", "eq?";
    (* Arithmetic ops *)
    "+", "add"; "*", "mul"; "/", "div"; "=", "eq"; "<", "lt";
    (* Additional rational numebr ops *)
    "numerator", "numerator"; "denominator", "denominator"; "gcd", "gcd";
    (* you can add yours here *)
    "apply", "apply"; "car", "car"; "cdr", "cdr"; "cons", "cons"; "set-car!", "set_car"; "set-cdr!", "set_cdr";
  ];;
  let free_primitives = List.map (fun (x, y) -> x) primitive_names_to_labels;;

  (*(*Constants Table*)
  let make_consts_tbl asts = raise X_not_yet_implemented;;*)
  
  (*Free Variables Table*)
  let rec fvars_scanner asts =
    match asts with
    | [] -> []
    | hd::tl -> let x = (match hd with
                         | Const'(c) -> []
                         | Var'(VarFree(var)) -> [var]
                         | Var'(VarParam(var, major)) -> []
                         | Var'(VarBound(var, major, minor)) -> []
                         | Box'(var) -> fvars_scanner [Var'(var)]
                         | BoxGet'(var) -> fvars_scanner [Var'(var)]
                         | BoxSet'(var, expr) -> fvars_scanner [Var'(var); expr]
                         | If'(test, dit, dif) -> fvars_scanner [test; dit; dif]
                         | Seq'(exprs) -> fvars_scanner exprs
                         | Set'(var, expr) -> fvars_scanner [Var'(var); expr]
                         | Def'(var, expr) -> fvars_scanner [Var'(var); expr]
                         | Or'(exprs) -> fvars_scanner exprs
                         | LambdaSimple'(params, body) -> fvars_scanner [body]
                         | LambdaOpt'(params, opt, body) -> fvars_scanner [body]
                         | Applic'(app, args) -> fvars_scanner ([app]@args)
                         | ApplicTP'(app, args) -> fvars_scanner ([app]@args)
                         (*| _ -> []*)) in
                x@(fvars_scanner tl);;

  (*let rec remove_duplicates lst =
    match lst with
    | [] -> []
    | hd::tl -> if(List.mem hd tl)
                then 
                else*)
  let rec remove_duplicates input output =
    match input with
    | [] -> output
    | hd::tl -> if(List.mem hd output)
                then remove_duplicates tl output
                else remove_duplicates tl (output@[hd]);;

  let rec fvars_tbl_constructor fvars index output =
    match fvars with
    | [] -> output
    | hd::tl -> fvars_tbl_constructor tl (index+1) (output@[(hd, index)]);;

  (*let make_fvars_tbl asts =
    fvars_tbl_constructor
      (remove_duplicates
        (free_primitives@(fvars_scanner asts)) []) 0 [];;*)
  
  (*Generate*)
  let rec get_fvar_address name fvars =
    match fvars with
    | [] -> -1
    | (fvar_name, fvar_index)::tl -> if(name = fvar_name)
                                     then fvar_index
                                     else get_fvar_address name tl;;


  module type GENSYM = 
  sig
    val reset : unit -> unit
    val next : string -> string 
  end ;;

  module Gensym : GENSYM = 
  struct 
    let c = ref 0
    let reset () = c:=0
    let next s = incr c ; s ^ (string_of_int !c)
 end;;
(*module Gensym : GENSYM;;*)


let rec sexpExist x lst  =
  match lst with 
      |[] -> false
      |_ -> (match lst with
              |(frst::rest) -> (match x with 
                                  |Sexpr(contentX)->
                                    (match frst with
                                      |Sexpr(contentFrst)->
                                        (match rest with
                                          | [] -> sexpr_eq contentX contentFrst
                                          | _ -> if (sexpr_eq contentX contentFrst) then true else (sexpExist x rest))
                                          |_ ->  raise X_no_match)
                                    |_ ->  raise X_no_match)
              |_ ->  raise X_no_match)

      (*|_-> let (frst:: rest) = lst in
            let Sexpr(contentX)= x in
            let Sexpr(contentFrst)= frst in
            (match rest with
              | [] -> sexpr_eq contentX contentFrst
              | _ -> if (sexpr_eq contentX contentFrst) then true else (sexpExist x rest));;*)



let rec make_Consts_List_from_expr' expr =
  match expr with 
    | Const' (x) -> [x]
    | BoxSet' (v, exprTag) -> make_Consts_List_from_expr' exprTag
    | If' (exprPred, exprThen, exprElse) ->  (make_Consts_List_from_expr' exprPred ) @ (make_Consts_List_from_expr' exprThen ) @ (make_Consts_List_from_expr' exprElse)
    | Seq' (seqList) -> List.flatten ( List.map make_Consts_List_from_expr' seqList)
    | Set' (v, exprTag) ->   make_Consts_List_from_expr' exprTag
    | Def' (var, exprTag) -> make_Consts_List_from_expr' exprTag
    | Or' (lst) -> List.flatten ( List.map make_Consts_List_from_expr' lst)
    | LambdaSimple' (strLst,  exprTag) -> make_Consts_List_from_expr' exprTag
    | LambdaOpt' (strLst, str, exprTag) -> make_Consts_List_from_expr' exprTag
    | Applic' (exprTag, exprTaglst) -> (make_Consts_List_from_expr' exprTag) @ (List.flatten (List.map make_Consts_List_from_expr' exprTaglst))
    | ApplicTP' (exprTag, exprTaglst) -> (make_Consts_List_from_expr' exprTag) @ (List.flatten (List.map make_Consts_List_from_expr' exprTaglst))
    | _ -> []

let rec cleaning_doubles input output =
  match input with
  | [] -> output
  | x:: rest -> (match x with
                  |Void -> cleaning_doubles rest output
                  |_ ->   if (sexpExist x output) then (cleaning_doubles rest output) else (cleaning_doubles rest (output@[x]) ));;

let rec extending_Const_List input output =
  match input with
  | [] -> output 
  |frst:: rest -> (match frst with
                  | Sexpr (Symbol (str))-> (extending_Const_List rest (output@[Sexpr (String(str))]@ [Sexpr (Symbol str)]))
                  | Sexpr (Pair(car, cdr)) -> (extending_Const_List rest (output@ (extending_Const_List [(Sexpr (car))] [])  @ (extending_Const_List [(Sexpr (cdr))] []) @ [Sexpr (Pair(car, cdr))]))
                  | _ -> extending_Const_List rest (output@[frst]) );;

let rec getOffset expression const_table =
  match const_table with 
  |[] -> 0
  | (frst:: rest) -> 
        (match expression with
        | Void -> 0
        | Sexpr (Nil) -> 1
        | Sexpr(contentE) ->
          (match frst with  
            | (Void, (index, str)) -> (getOffset expression rest)
            | (Sexpr (contentFrst), (index, str)) -> if (sexpr_eq contentE contentFrst) then index else (getOffset expression rest)));;

let rec create_Const_Table final_cnst_list index const_table =
  if final_cnst_list=[] then const_table else
  match final_cnst_list with
  | frst::rest -> (match frst with
                  | Void -> (create_Const_Table rest (index+1) (const_table@[ (frst, (0, "db T_VOID"))]))
                  | Sexpr(Nil)-> (create_Const_Table rest (index+1) (const_table@[(frst, (1, "db T_NIL"))]))
                  | Sexpr(Bool false)-> (create_Const_Table rest (index+2) (const_table@[(frst, (2, "db T_BOOL, 0"))]))
                  | Sexpr(Bool true)->  (create_Const_Table rest (index+2) (const_table@[ (frst, (4, "db T_BOOL, 1"))]))
                  | Sexpr(String (str)) -> (create_Const_Table rest (index+ 1+ 8+ (String.length str) ) (const_table@[ (frst, (index, "MAKE_LITERAL_STRING\""^ str ^ "\""))]))
                  | Sexpr(Number(Fraction(num1, num2))) -> (create_Const_Table rest (index+ 1+ 8+ 8) (const_table@[ (frst, (index, "MAKE_LITERAL_RATIONAL("^(string_of_int num1)^ "," ^(string_of_int num2)^")"))]))
                  | Sexpr (Number (Float num)) -> (create_Const_Table rest (index+ 1+8) (const_table@[(frst, (index, "MAKE_LITERAL_FLOAT(" ^ (string_of_float num)^ ")"))]))
                  | Sexpr(Pair(car,cdr)) -> (create_Const_Table rest (index+1+ 8+8) (
                    const_table@[(frst, (index, "MAKE_LITERAL_PAIR(const_tbl+" ^(string_of_int (getOffset (Sexpr(car)) const_table))^ ", const_tbl+"^(string_of_int (getOffset (Sexpr(cdr)) const_table))^")"))]))
                  | Sexpr(Symbol (sym)) ->   (create_Const_Table rest (index+ 1+8) (const_table@[ (frst, (index, "MAKE_LITERAL_SYMBOL(const_tbl+"^(string_of_int (getOffset ( Sexpr (String sym)) const_table))^")"))]))
                  | Sexpr ( Char chr)  ->    (create_Const_Table rest (index+1+1) (const_table@[ (frst, (index, "MAKE-LITERAL_CHAR("^ (Char.escaped chr)^")"))]))
                  )

  |_-> const_table;;

let rec get_fvar_address name fvars =
  match fvars with
  | [] -> -1
  | (fvar_name, fvar_index)::tl -> if(name = fvar_name)
                                    then fvar_index
                                    else get_fvar_address name tl;;




let create_Assembly_Const_Expr consts expr =
  "; create a const\nmov rax, const_tbl+"^ (string_of_int (getOffset expr consts))^"\n";;

let create_Assembly_VarParam param position =
  (*"; create a varParam: "^ param ^"\n mov rax, qword[rbp+ 8*(4+"^(string_of_int position) ^")]\n";;*)
  "; create a varParam: "^ param ^"\n mov rax, PVAR("^(string_of_int position) ^")\n";;
let create_Assembly_BoundVar boundVar major minor =
  "; create a bound param: " ^ boundVar^"\n mov rax, qword [rbp + 8*2]\nmov rax, qword[rax + 8*"^(string_of_int major)^"]\n mov rax, qword[rax+ 8*"^(string_of_int minor)^"]\n";;

let create_Assembly_Freevar varS fvars =
  "; create a free param: " ^ varS^"\n mov rax, qword [fvar_tbl+ WORD_SIZE*"^(string_of_int (get_fvar_address varS fvars)) ^"]\n";; (*TODO -> maybe *8 *)


let rec generate_Expression consts fvars expr depth=
  match expr with
  |Const'(x) -> create_Assembly_Const_Expr consts x
  |Var' (VarParam (param, position)) -> create_Assembly_VarParam param position 
  |Var' (VarBound (boundVar , major, minor)) -> create_Assembly_BoundVar boundVar major minor
  |Var' (VarFree varS) -> create_Assembly_Freevar varS fvars 
  |Seq' (lst) -> create_Assembly_Seq lst consts fvars depth
  |Or' (lst)-> create_Assembly_Or lst consts fvars depth
  |If' (pred, thenCase, elseCase) -> create_Assembly_If pred thenCase elseCase consts fvars depth
  |Set' (var, inExpr) -> create_Assembly_Set var inExpr consts fvars depth
  |Def'(var, inExpr) -> create_Assembly_Def var inExpr consts fvars depth
  |BoxGet' (var) -> create_Assembly_Box_Get var consts fvars depth
  |BoxSet' (var, expr) ->  create_Assembly_Box_Set var expr consts fvars depth
  |Box' (var) -> create_Assembly_Box var consts fvars depth
  |LambdaSimple' (lstParams, body) -> create_Assembly_LambdaSimple lstParams body consts fvars depth
  |Applic' (proc, params) -> create_Assembly_Applic proc params consts fvars depth
  |LambdaOpt' (lstParams , strOpt, body)->  create_Assembly_LambdaOpt lstParams strOpt body consts fvars depth
  |ApplicTP' (proc, params) -> create_Assembly_Applic proc params consts fvars depth
  
and create_Assembly_Seq lst consts fvars depth =
  let generate_Same_Tables expR = (generate_Expression consts fvars expR depth) in
  ";create a seq:\n"^ List.fold_left (^) "" (List.map generate_Same_Tables lst)

and create_Assembly_Or lst consts fvars depth =
let index= (Gensym.next ("")) in
  (*let lexit= (Gensym.next ("Lexit")) in*)
  let generate_Same_Tables expR= (generate_Expression consts fvars expR depth) in
    match lst with
    |(frst::rest)->
      let func str1 str2= (str1^"cmp rax, SOB_FALSE_ADDRESS\njne lexit"^ index^"\n"^str2) in
      ";create Or:\n"^ (List.fold_left (func) (generate_Expression consts fvars frst depth) (List.map generate_Same_Tables rest))^"lexit"^index^":\n"
    |_ ->  raise X_no_match

and create_Assembly_If pred thenCase elseCase consts fvars depth=
let indexIf= (Gensym.next ("")) in
(*let lelse= (Gensym.next ("lelse")) in
let lexit= (Gensym.next ("lexit")) in*)
  ";create If:\n"^(generate_Expression consts fvars pred depth)^"cmp rax, SOB_FALSE_ADDRESS\nje lelse"^indexIf^"\n"^ (generate_Expression consts fvars thenCase depth) ^"jmp lexit"^indexIf^"\nlelse"
  ^indexIf^":\n"^(generate_Expression consts fvars elseCase depth)^"lexit"^indexIf^":\n"

and create_Assembly_Set var inExpr consts fvars depth=
match var with
|VarParam(varStr, varPosition)-> create_Assembly_Set_Param varStr varPosition inExpr consts fvars depth
|VarBound (varStr, majorB, minorB)-> create_Assembly_Set_Bound varStr majorB minorB inExpr consts fvars depth
|VarFree (strVFree)-> create_Assembly_Set_Free strVFree inExpr consts fvars depth

and create_Assembly_Def var inExpr consts fvars depth=
";create Def: \n"^
(match var with
|VarParam(varStr, varPosition)-> create_Assembly_Set_Param varStr varPosition inExpr consts fvars depth
|VarBound (varStr, majorB, minorB)-> create_Assembly_Set_Bound varStr majorB minorB inExpr consts fvars depth
|VarFree (strVFree)-> create_Assembly_Set_Free strVFree inExpr consts fvars depth)

and create_Assembly_Set_Param varStr varPosition inExpr consts fvars depth=
  ";create Set for varParam "^varStr^":\n"^(generate_Expression consts fvars inExpr depth)^ "mov PVAR("^(string_of_int varPosition)^"), rax\n mov rax, SOB_VOID_ADDRESS\n"

and create_Assembly_Set_Bound varStr major minor inExpr consts fvars depth =
  ";create Set for varBound "^varStr^":\n"^(generate_Expression consts fvars inExpr depth)^"mov rbx, qword [rbp+ 8*2]\n mov rbx, qword [rbx+ 8*"^(string_of_int major)^
  "]\nmov qword [rbx+8*"^(string_of_int minor) ^"], rax\nmov rax, SOB_VOID_ADDRESS\n"

and create_Assembly_Set_Free strVFree inExpr consts fvars depth =
  ";create Set for varFree "^strVFree^":\n"^(generate_Expression consts fvars inExpr depth)^"mov qword[fvar_tbl+WORD_SIZE*"^(string_of_int (get_fvar_address strVFree fvars)) ^ (*maybe 8* *)
  "], rax\nmov rax, SOB_VOID_ADDRESS\n"

and create_Assembly_Box_Get var consts fvars depth=
  ";create BoxGet :\n"^(generate_Expression consts fvars (Var'(var)) depth)^"mov rax, qword[rax]\n" (*havent Cheked!*)

and create_Assembly_Box_Set var expr consts fvars depth =
  ";create BoxSet :\n"^(generate_Expression consts fvars (expr) depth)^"push rax\n"^(generate_Expression consts fvars (Var' (var)) depth)^ "pop qword[rax]\nmov rax, SOB_VOID_ADDRESS\n" (*havent Cheked!*)

and create_Assembly_Box var consts fvars depth=
  ";create a Box:\n"^
  "MALLOC r8, WORD_SIZE\n"^
  (generate_Expression consts fvars (Var'(var)) depth)^"\n"^
  "mov qword [r8], rax\n"^
  "mov rax, r8\n"

and create_Assembly_LambdaSimple lstParams body consts fvars depth =
  let newDepth= (depth+1) in
  match depth with
  |0-> create_Assembly_LambdaSimple_First_Layer lstParams body consts fvars newDepth
  |_-> create_Assembly_LambdaSimple_Multiple_Layers lstParams body consts fvars newDepth

and create_Assembly_LambdaSimple_First_Layer lstParams body consts fvars depth =
  let closureIndex = (Gensym.next ("")) in
    ";create LambdaSimple first layer:
    MAKE_CLOSURE(rax,  SOB_NIL_ADDRESS, Lcode"^closureIndex^")
    ;jump beyond the Body
    jmp Lcont"^closureIndex^"
    Lcode"^closureIndex^":
    push rbp
    mov rbp, rsp
    "^(generate_Expression consts fvars body depth)^
    "leave
    ret
;end of the body (closure)
    Lcont"^closureIndex^":\n"
  
and create_Assembly_LambdaSimple_Multiple_Layers lstParams body consts fvars depth =
  let closureIndex = (Gensym.next ("")) in
  ";create LambdaSimple multiple layers\n"^
  ";code for_ext env\n"^
  "MALLOC rdx, WORD_SIZE*"^(string_of_int depth)^"\n"^ (*maybe depth+1*)
  "; store old env in rbx \n"^
  "mov rbx, qword[rbp+ 8*2]\n"^
  "mov r8, rdx ;store 0 index of the ext_env\n"^
  "add rdx, WORD_SIZE ;rdx now point to index 1 ext env\n"^
  "checking"^closureIndex^":\n"^
  "mov rcx, "^(string_of_int (depth-2))^" ; numbers of loops \n"^ (*TODO CHANGED from depth-1*)
  "cmp rcx, 0\n"^
  "je Continue_Ext_Env"^closureIndex^" ;if (the depth-1) is 0 then thres nothing to copy besides paramsn\n"^
  "Copy_Ext_Env_Loop"^closureIndex^":\n"^
  "mov r10, qword[rbx]\n"^
  "mov [rdx], r10 ; now extEnv[i+1]= oldEnv[i]\n"^
  "add rbx, WORD_SIZE ; add 8 to the next vector oldEnv\n"^
  "add rdx, WORD_SIZE ; add 8 to the next vector extEnv\n"^
  "loop Copy_Ext_Env_Loop"^closureIndex^"\n"^
  
  ";now code to copy the old env Params to extEnv index 0\n"^
  "Continue_Ext_Env"^closureIndex^":\n"^
  "mov rdx, r8 ;restore index 0\n"^
  "mov qword[rdx], SOB_NIL_ADDRESS ;just in case n==0\n"^
  "mov rcx, qword[rbp+ 8*3] ;rcx=n (num of params)\n"^
  "check1"^closureIndex^":\n"^
  "cmp rcx, 0\n"^
  "je Continue_Allocate_Closure_Object"^closureIndex^"\n"^
  (*"mov rbx, qword[rbp+8*4] ; rbx= A0\n"^*)
  "check2"^closureIndex^":\n"^
  "mov r11, rcx ;keep rcx unchanged\n"^
  "shl r11,  3 ; mutiply n*8-> number of bytes to allocate\n"^
  "add r11, 1 ; saving space for the magic\n"^
  "MALLOC r10, r11 ;allocating memory for index 0 in extEnv\n"^
  "mov [rdx], r10 ; now ext env 0 pointing to the allocated memory\n"^
  "mov rdx, r10 ; rdx is the start of allocated memory' the atcual vector of ext env 0\n"^

  "mov r14, 32 ; 8*4-> qwors[rbp+ 8*4]=A0\n"^
  "Copy_Params_Ext_Env_Loop"^closureIndex^":\n"^
  "mov rbx, qword[rbp+r14] ; rbx= A0\n"^
  "mov [rdx], rbx ; Ai -> extEnx[0][i] \n"^
  "add r14, WORD_SIZE\n"^
  "add rdx, WORD_SIZE\n"^
  "loop Copy_Params_Ext_Env_Loop"^closureIndex^"\n"^
  "mov qword[rdx], SOB_NIL_ADDRESS ; magic at the and of extEnv 0\n"^
  
  "Continue_Allocate_Closure_Object"^closureIndex^":\n"^
  "; done with extending the env. now making closure\n"^
  "MAKE_CLOSURE(rax,  r8, Lcode"^closureIndex^")\n"^
  ";jump beyond the Body\n"^
  "jmp Lcont"^closureIndex^"\n"^
  "Lcode"^closureIndex^":\n"^
  "push rbp\n"^
  "mov rbp, rsp\n"^
  (generate_Expression consts fvars body depth)^"\n"^
  "leave\n"^
  "ret\n"^
  ";end of the body (closure)\n"^
  "Lcont"^closureIndex^":\n"
  
and create_Assembly_Applic proc params consts fvars depth =
let closureIndex = (Gensym.next ("")) in
  let n= List.length params in
  let generate_Same_Tables expR= (generate_Expression consts fvars expR depth) in
  let func str1 str2= (str2^"push rax\n"^str1) in
  ";create Applic:\n"^
  "push SOB_NIL_ADDRESS ; pushing magic\n"^
  (List.fold_left (func) ("") (List.map generate_Same_Tables params))^"\n"^
  "Noa"^closureIndex^":\n"^
  "mov r10, "^(string_of_int n)^";r10 now holds n (num of params)\n"^
  "push r10 ;pushing n (num of params)\n"^
  ";generating the proc. should be a closure\n"^
  (generate_Expression consts fvars proc depth)^"\n"^
  (*TODO verify that rax is actually closure*)
  "push qword[rax+TYPE_SIZE]\n"^
  "call [rax+TYPE_SIZE+WORD_SIZE]\n"^
  "add rsp, 8*1 ; pop env\n"^
  "pop rbx ; pop arg count\n"^
  "shl rbx, 3 ; rbx = rbx * 8\n"^
  "add rsp, rbx; pop args\n"^
  "add rsp, 8; poping magic\n"

and  create_Assembly_ApplicTP proc params consts fvars depth =
let n= List.length params in
  let generate_Same_Tables expR= (generate_Expression consts fvars expR depth) in
  let func str1 str2= (str2^"push rax\n"^str1) in
  ";create Applic:\n"^
  "push SOB_NIL_ADDRESS ; pushing magic\n"^
  (List.fold_left (func) ("") (List.map generate_Same_Tables params))^"\n"^
  "mov r10, "^(string_of_int n)^";r10 now holds n (num of params)\n"^
  "push r10 ;pushing n (num of params)\n"^
  ";generating the proc. should be a closure\n"^
  (generate_Expression consts fvars proc depth)^"\n"^
  (*TODO verify that rax is actually closure*)
  "push qword[rax+TYPE_SIZE] ;env\n"^
  "push qword[rbp+8*1] ;old ret addr\n"^
  ""
  

and create_Assembly_LambdaOpt lstParams strOpt body consts fvars depth =
  let newDepth= (depth+1) in
  match depth with
  |0-> create_Assembly_LambdaOpt_First_Layer lstParams strOpt body consts fvars newDepth
  |_-> create_Assembly_LambdaOpt_Multiple_Layers lstParams strOpt body consts fvars newDepth

and create_Assembly_LambdaOpt_First_Layer lstParams strOpt body consts fvars depth =
  let numMustParams= (List.length lstParams) in

  let closureIndex = (Gensym.next ("")) in
  ";create LambdaOpt first layer:\n"^
  "MAKE_CLOSURE(rax,  SOB_NIL_ADDRESS, Lcode"^closureIndex^")\n"^
  ";jump beyond the Body\n"^
  "jmp Lcont"^closureIndex^"\n"^
  "Lcode"^closureIndex^":\n"^
  "push rbp\n"^
  "mov rbp, rsp\n"^
  "mov rbx, qword[rbp+ 8*3] ; rbp=n (num of initial params)\n"^
  
  "mov r8, "^(string_of_int (List.length lstParams))^" ; r8= num of must params\n"^
 
  "cmp rbx, r8 ;comparing the numbers of params with the number of the must params \n"^
  "je Cont_After_Adjust"^closureIndex^"\n"^

  ";now code to adjust the params \n"^
  "mov rcx, rbx ; ecx in now num of params \n"^
  "sub rcx, r8; ecx now is num of iterations=> (num of params)- (num of must params)\n"^
  "add rbx, 3  ; \n"^

  "shl rbx,  3 ; mutiply (n+3)*8-> distance from the An to rbx\n"^
  "mov r9, [rbp+rbx] ;r9=A0\n"^
  "mov r10, [rbp+rbx+WORD_SIZE] ;r10 holds the magic\n"^
  "MAKE_PAIR(r11, r9, r10) ; r11 now point to the pair(An, SOB_NIl_ADDRESS\n"^
  "sub rcx, 1 ; one less iteraition\n"^
  "cmp rcx, 0\n"^
  "je Continue_List_ready"^closureIndex^"\n"^
  
  "sub rbx, WORD_SIZE\n"^
  "Loop_Make_List"^closureIndex^":\n"^
  ";Looop invariant r11 always points to the last Pair\n"^
  "mov r8, r11 ; now r8 point to the last Pair\n"^
  "mov r9, [rbp+rbx]; r9 point to A(i-1)\n"^
  "MAKE_PAIR(r11, r9,r8)\n"^
  "sub rbx, WORD_SIZE\n"^
  "loop Loop_Make_List"^closureIndex^"\n"^
  "Continue_List_ready"^closureIndex^":\n"^
  ";now r11 point to the Pairs. to the list\n"^
  (*"mov qword[rbp + 8*3], "^( string_of_int (numMustParams+1))^" ; new n(num of params equals num of must params+1 for the list\n"^*)
  "mov qword [rbp + (4+"^(string_of_int numMustParams)^")*8], r11 ;the pointer to the list is right above the last must params\n"^
  "mov qword [rbp + (4+"^(string_of_int (numMustParams+1))^")*8], SOB_NIL_ADDRESS ; magic above the list\n"^
  
  "Cont_After_Adjust"^closureIndex^":\n"^
  (generate_Expression consts fvars body depth)^
  "leave\n"^
  "ret\n"^
  ";end of the body (closure)\n"^
  "Lcont"^closureIndex^":\n"

    
and create_Assembly_LambdaOpt_Multiple_Layers lstParams strOpt body consts fvars depth=
let numMustParams= (List.length lstParams) in
let closureIndex = (Gensym.next ("")) in
  ";create LambdaOpt multiple layers:\n"^
  ";code for_ext env\n"^
  "MALLOC rdx, WORD_SIZE*"^(string_of_int depth)^"\n"^ (*maybe depth+1*)
  "; store old env in rbx \n"^
  "mov rbx, qword[rbp+ 8*2]\n"^
  "mov r8, rdx ;store 0 index of the ext_env\n"^
  "add rdx, WORD_SIZE ;rdx now point to index 1 ext env\n"^
  "checking"^closureIndex^":\n"^
  "mov rcx, "^(string_of_int (depth-2))^" ; numbers of loops \n"^ (*TODO CHANGED from depth-1*)
  "cmp rcx, 0\n"^
  "je Continue_Ext_Env"^closureIndex^" ;if (the depth-1) is 0 then thres nothing to copy besides paramsn\n"^
  "Copy_Ext_Env_Loop"^closureIndex^":\n"^
  "mov r10, qword[rbx]\n"^
  "mov [rdx], r10 ; now extEnv[i+1]= oldEnv[i]\n"^
  "add rbx, WORD_SIZE ; add 8 to the next vector oldEnv\n"^
  "add rdx, WORD_SIZE ; add 8 to the next vector extEnv\n"^
  "loop Copy_Ext_Env_Loop"^closureIndex^"\n"^
  
  ";now code to copy the old env Params to extEnv index 0\n"^
  "Continue_Ext_Env"^closureIndex^":\n"^
  "mov rdx, r8 ;restore index 0\n"^
  "mov qword[rdx], SOB_NIL_ADDRESS ;just in case n==0\n"^
  "mov rcx, qword[rbp+ 8*3] ;rcx=n (num of params)\n"^
  "check1"^closureIndex^":\n"^
  "cmp rcx, 0\n"^
  "je Continue_Allocate_Closure_Object"^closureIndex^"\n"^
  (*"mov rbx, qword[rbp+8*4] ; rbx= A0\n"^*)
  "check2"^closureIndex^":\n"^
  "mov r11, rcx ;keep rcx unchanged\n"^
  "shl r11,  3 ; mutiply n*8-> number of bytes to allocate\n"^
  "MALLOC r10, r11 ;allocating memory for index 0 in extEnv\n"^
  "mov [rdx], r10 ; now ext env 0 pointing to the allocated memory\n"^
  "mov rdx, r10 ; rdx is the start of allocated memory' the atcual vector of ext env 0\n"^

  "mov r14, 32 ; 8*4-> qwors[rbp+ 8*4]=A0\n"^
  "Copy_Params_Ext_Env_Loop"^closureIndex^":\n"^
  "mov rbx, qword[rbp+r14] ; rbx= A0\n"^
  "mov [rdx], rbx ; Ai -> extEnx[0][i] \n"^
  "add r14, WORD_SIZE\n"^
  "add rdx, WORD_SIZE\n"^
  "loop Copy_Params_Ext_Env_Loop"^closureIndex^"\n"^
  
  "Continue_Allocate_Closure_Object"^closureIndex^":\n"^
  "; done with extending the env. now making closure\n"^
  "MAKE_CLOSURE(rax,  r8, Lcode"^closureIndex^")\n"^
  ";jump beyond the Body\n"^
  "jmp Lcont"^closureIndex^"\n"^
  "Lcode"^closureIndex^":\n"^
  "push rbp\n"^
  "mov rbp, rsp\n"^
  "mov rbx, qword[rbp+ 8*3] ; rbp=n (num of initial params)\n"^
  
  "mov r8, "^(string_of_int (List.length lstParams))^" ; r8= num of must params\n"^
 
  "cmp rbx, r8 ;comparing the numbers of params with the number of the must params \n"^
  "je Cont_After_Adjust"^closureIndex^"\n"^

  ";now code to adjust the params \n"^
  "mov rcx, rbx ; ecx in now num of params \n"^
  "sub rcx, r8; ecx now is num of iterations=> (num of params)- (num of must params)\n"^
  "add rbx, 3  ; \n"^

  "shl rbx,  3 ; mutiply (n+3)*8-> distance from the An to rbx\n"^
  "mov r9, [rbp+rbx] ;r9=A0\n"^
  "mov r10, [rbp+rbx+WORD_SIZE] ;r10 holds the magic\n"^
  "MAKE_PAIR(r11, r9, r10) ; r11 now point to the pair(An, SOB_NIl_ADDRESS\n"^
  "sub rcx, 1 ; one less iteraition\n"^
  "cmp rcx, 0\n"^
  "je Cont_after_r11_list"^closureIndex^"\n"^
  
  "sub rbx, WORD_SIZE\n"^
  "Loop_Make_List"^closureIndex^":\n"^
  ";Looop invariant r11 always points to the last Pair\n"^
  "mov r8, r11 ; now r8 point to the last Pair\n"^
  "mov r9, [rbp+rbx]; r9 point to A(i-1)\n"^
  "MAKE_PAIR(r11, r9,r8)\n"^
  "sub rbx, WORD_SIZE\n"^
  "loop Loop_Make_List"^closureIndex^"\n"^

  "Cont_after_r11_list"^closureIndex^":\n"^
  ";now r11 point to the Pairs. to the list\n"^
  (*"mov qword[rbp + 8*3], "^( string_of_int (numMustParams+1))^" ; new n(num of params equals num of must params+1 for the list\n"^*)
  "mov qword [rbp + (4+"^(string_of_int numMustParams)^")*8], r11 ;the pointer to the list is right above the last must params\n"^
  "mov qword [rbp + (4+"^(string_of_int (numMustParams+1))^")*8], SOB_NIL_ADDRESS ; magic above the list\n"^
  
  "Cont_After_Adjust"^closureIndex^":\n"^
  (generate_Expression consts fvars body depth)^
  "leave\n"^
  "ret\n"^
  ";end of the body (closure)\n"^
  "Lcont"^closureIndex^":\n"




module Code_Gen : CODE_GEN = struct
  let make_consts_tbl asts = 
    let frst_cnst_list = List.flatten ( List.map make_Consts_List_from_expr' asts) in
    let frst_cnst_list_No_doubles = cleaning_doubles frst_cnst_list [] in
    let extended_cnst_list = (extending_Const_List frst_cnst_list_No_doubles []) in
    let final_cnst_list= ([Void] @ cleaning_doubles extended_cnst_list [Sexpr(Nil); Sexpr (Bool false); Sexpr (Bool true)]) in
      create_Const_Table final_cnst_list 0 [];;
  let make_fvars_tbl asts = fvars_tbl_constructor
                            (remove_duplicates
                            (free_primitives@(fvars_scanner asts)) []) 0 [];;
  let generate consts fvars e = generate_Expression consts fvars e 0;;
end;;

