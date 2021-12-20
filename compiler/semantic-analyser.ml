#use "tag-parser.ml";;
open Tag_Parser;;

type var = 
  | VarFree of string
  | VarParam of string * int
  | VarBound of string * int * int;;

type expr' =
  | Const' of constant
  | Var' of var
  | Box' of var
  | BoxGet' of var
  | BoxSet' of var * expr'
  | If' of expr' * expr' * expr'
  | Seq' of expr' list
  | Set' of var * expr'
  | Def' of var * expr'
  | Or' of expr' list
  | LambdaSimple' of string list * expr'
  | LambdaOpt' of string list * string * expr'
  | Applic' of expr' * (expr' list)
  | ApplicTP' of expr' * (expr' list);;

let rec expr'_eq e1 e2 =
  match e1, e2 with
  | Const' Void, Const' Void -> true
  | Const'(Sexpr s1), Const'(Sexpr s2) -> sexpr_eq s1 s2
  | Var'(VarFree v1), Var'(VarFree v2) -> String.equal v1 v2
  | Var'(VarParam (v1,mn1)), Var'(VarParam (v2,mn2)) -> String.equal v1 v2 && mn1 = mn2
  | Var'(VarBound (v1,mj1,mn1)), Var'(VarBound (v2,mj2,mn2)) -> String.equal v1 v2 && mj1 = mj2  && mn1 = mn2
  | Box'(VarFree v1), Box'(VarFree v2) -> String.equal v1 v2
  | Box'(VarParam (v1,mn1)), Box'(VarParam (v2,mn2)) -> String.equal v1 v2 && mn1 = mn2
  | Box'(VarBound (v1,mj1,mn1)), Box'(VarBound (v2,mj2,mn2)) -> String.equal v1 v2 && mj1 = mj2  && mn1 = mn2
  | BoxGet'(VarFree v1), BoxGet'(VarFree v2) -> String.equal v1 v2
  | BoxGet'(VarParam (v1,mn1)), BoxGet'(VarParam (v2,mn2)) -> String.equal v1 v2 && mn1 = mn2
  | BoxGet'(VarBound (v1,mj1,mn1)), BoxGet'(VarBound (v2,mj2,mn2)) -> String.equal v1 v2 && mj1 = mj2  && mn1 = mn2
  | BoxSet'(VarFree v1,e1), BoxSet'(VarFree v2, e2) -> String.equal v1 v2 && (expr'_eq e1 e2)
  | BoxSet'(VarParam (v1,mn1), e1), BoxSet'(VarParam (v2,mn2),e2) -> String.equal v1 v2 && mn1 = mn2 && (expr'_eq e1 e2)
  | BoxSet'(VarBound (v1,mj1,mn1),e1), BoxSet'(VarBound (v2,mj2,mn2),e2) -> String.equal v1 v2 && mj1 = mj2  && mn1 = mn2 && (expr'_eq e1 e2)
  | If'(t1, th1, el1), If'(t2, th2, el2) -> (expr'_eq t1 t2) &&
                                            (expr'_eq th1 th2) &&
                                              (expr'_eq el1 el2)
  | (Seq'(l1), Seq'(l2)
  | Or'(l1), Or'(l2)) -> List.for_all2 expr'_eq l1 l2
  | (Set'(var1, val1), Set'(var2, val2)
  | Def'(var1, val1), Def'(var2, val2)) -> (expr'_eq (Var'(var1)) (Var'(var2))) &&
                                             (expr'_eq val1 val2)
  | LambdaSimple'(vars1, body1), LambdaSimple'(vars2, body2) ->
     (List.for_all2 String.equal vars1 vars2) &&
       (expr'_eq body1 body2)
  | LambdaOpt'(vars1, var1, body1), LambdaOpt'(vars2, var2, body2) ->
     (String.equal var1 var2) &&
       (List.for_all2 String.equal vars1 vars2) &&
         (expr'_eq body1 body2)
  | Applic'(e1, args1), Applic'(e2, args2)
  | ApplicTP'(e1, args1), ApplicTP'(e2, args2) ->
	 (expr'_eq e1 e2) &&
	   (List.for_all2 expr'_eq args1 args2)
  | _ -> false;;	
                      
exception X_syntax_error;;

module type SEMANTICS = sig
  val run_semantics : expr -> expr'
  val annotate_lexical_addresses : expr -> expr'
  val annotate_tail_calls : expr' -> expr'
  val box_set : expr' -> expr'
end;;

module Semantics : SEMANTICS = struct


let number_to_str n =
  match n with
  | Fraction(numer, denom) -> Printf.sprintf "Fraction(%s%s, %s)" (if(numer<0) then "-" else "") (string_of_int numer) (string_of_int denom)
  | Float(num) -> Printf.sprintf "Float(%s%s)" (if(num<0.0) then "-" else "") (string_of_float num);;

let rec sexpr_to_str = function
  | Nil -> "Nil"
  | Bool(b) -> Printf.sprintf "Bool(%b)" b
  | Number(n) -> Printf.sprintf "Number(%s)" (number_to_str n)
  | Char(c) -> Printf.sprintf "Char('%c')" c
  | String(s) -> Printf.sprintf "String(\"%s\")" s
  | Symbol(s) -> Printf.sprintf "Symbol(\"%s\")" s
  | Pair(s1, s2) -> Printf.sprintf "Pair(%s, %s)" (sexpr_to_str s1) (sexpr_to_str s2);;

let rec constant_to_str const =
  match const with
  | Sexpr(sexpr) -> Printf.sprintf "Sexpr(%s)" (sexpr_to_str sexpr)
  | Void -> Printf.sprintf "Void";;

let rec expr_to_str expr =
  let expr_list_to_str exprs = Printf.sprintf "[%s]" (String.concat ", " (List.map expr_to_str exprs)) in 
  match expr with
  | Const(c) -> Printf.sprintf "Const(%s)" (constant_to_str c)
  | Var(s) -> Printf.sprintf (*"Var(%s)"*)"%s" s
  | If(test, dit, dif) -> Printf.sprintf "If(%s, %s, %s)" (expr_to_str test) (expr_to_str dit) (expr_to_str dif)
  | Seq(exprs) -> Printf.sprintf "Seq(%s)" (expr_list_to_str exprs)
  | Set(var, expr) -> Printf.sprintf "Set(%s, %s)" (expr_to_str var) (expr_to_str expr)
  | Def(var, expr) -> Printf.sprintf "Def(%s, %s)" (expr_to_str var) (expr_to_str expr)
  | Or(exprs) -> Printf.sprintf "Or(%s)" (expr_list_to_str exprs)
  | LambdaSimple(params, body) -> Printf.sprintf "LambdaSimple ([%s], %s)" (String.concat ", " params) (expr_to_str body)
  | LambdaOpt(params, param, body) -> Printf.sprintf "LambdaOpt ([%s], %s, %s)" (String.concat ", " params) param (expr_to_str body)
  | Applic(proc, args) -> Printf.sprintf "Applic(%s, %s)" (expr_to_str proc) (expr_list_to_str args);;

let rec var_to_str = function
  | VarFree(v) -> Printf.sprintf "VarFree(%s)" v
  | VarParam(v, i) -> Printf.sprintf "VarParam(%s, %d)" v i
  | VarBound(v, major, minor) -> Printf.sprintf "VarBound(%s, %d, %d)" v major minor;;

let rec expr'_to_str expr = 
  let expr'_list_to_str exprs = Printf.sprintf "[%s]" (String.concat ", " (List.map expr'_to_str exprs)) in 
  let tagged_var_to_str tag var = Printf.sprintf "%s (%s)" tag (var_to_str var) in
  let tagged_list_to_str tag exprs = Printf.sprintf "%s (%s)" tag (expr'_list_to_str exprs) in
  let tagged_assignment_to_str tag var e2 = Printf.sprintf "%s (%s, %s)" tag (var_to_str var) (expr'_to_str e2) in
  let tagged_applic_to_str tag proc args = Printf.sprintf "%s (%s, %s)" tag (expr'_to_str proc) (expr'_list_to_str args) in
  match expr with 
  | Const'(Void) -> "Const' (#<Void>)"
  | Const'(Sexpr(sexpr)) -> Printf.sprintf "Const' (Sexpr(%s))" (sexpr_to_str sexpr)
  | Var'(var) -> tagged_var_to_str "Var'" var
  | Box'(var) -> tagged_var_to_str "Box'" var
  | BoxGet'(var) -> tagged_var_to_str "BoxGet'" var
  | BoxSet'(var, expr) -> tagged_assignment_to_str "BoxSet'" var expr
  | If'(test, dit, dif) -> Printf.sprintf "If' (%s, %s, %s)" (expr'_to_str test) (expr'_to_str dit) (expr'_to_str dif)
  | Seq'(exprs) -> tagged_list_to_str "Seq'" exprs
  | Or'(exprs) -> tagged_list_to_str "Or'" exprs
  | Set'(var, expr) -> tagged_assignment_to_str "Set'" var expr
  | Def'(var, expr) -> tagged_assignment_to_str "Def'" var expr
  | LambdaSimple'(params, body) -> Printf.sprintf "LambdaSimple' ([%s], %s)" (String.concat ", " params) (expr'_to_str body)
  | LambdaOpt'(params, param, body) -> Printf.sprintf "LambdaOpt' ([%s], %s, %s)" (String.concat ", " params) param (expr'_to_str body)
  | Applic'(proc, args) -> tagged_applic_to_str "Applic'" proc args
  | ApplicTP'(proc, args) -> tagged_applic_to_str "ApplicTP'" proc args;;


let is_param x params =
  match params with
  | [] -> false
  | _ -> List.exists (fun a -> a = x) params;;

(*Lexical Addressing*)
let rec lexical_addresses e scope params =
  match e with
  | Const(x) -> Const'(x)
  | Var(x) -> Var'(var_helper x scope params)
  | If(test, dit, dif) -> If'(lexical_addresses test scope params, lexical_addresses dit scope params, lexical_addresses dif scope params)
  | Seq(exprs) -> Seq'(List.map (fun x -> lexical_addresses x scope params) exprs)
  | Set(var, expr) -> Set'(var_helper (expr_to_str var) scope params, lexical_addresses expr scope params)
  | Def(var, expr) -> Def'(var_helper (expr_to_str var) scope params, lexical_addresses expr scope params)
  | Or(exprs) -> Or'(List.map (fun x -> lexical_addresses x scope params) exprs)
  | LambdaSimple(lambda_params, body) -> LambdaSimple'(lambda_params, lexical_addresses body (params::scope) lambda_params)
  | LambdaOpt(lambda_params, opt, body) -> LambdaOpt'(lambda_params, opt, lexical_addresses body ((params@[opt])::scope) (lambda_params@[opt]))
  | Applic(app, args) -> Applic'(lexical_addresses app scope params, List.map (fun x -> lexical_addresses x scope params) args)
  
  and var_helper x scope params =
    if(is_param x params)
    then VarParam(x, index_of x params 0)
    else (let major = get_major_index x scope 0 in
          let minor = get_minor_index x scope in
          if(major < 0 || minor < 0)
          then VarFree(x)
          else VarBound(x, major, minor))

  and get_major_index x scope i =
    match scope with
    | [] -> -1
    | hd::tl -> if(is_param x hd)
                then i
                else get_major_index x tl (i+1)
  
  and get_minor_index x scope =
    match scope with
    | [] -> -1
    | hd::tl -> if(is_param x hd)
                then index_of x hd 0
                else get_minor_index x tl

  and index_of x params i =
    match params with
    | [] -> -1
    | hd::tl -> if(hd = x)
                then i
                else index_of x tl (i+1);;

let annotate_lexical_addresses e = lexical_addresses e [] [];;


(*Annotating Tail Calls*)
let rec tail_calls e tp =
  match e with
  | Const'(v) -> e
  | Var'(x) -> e
  | If'(test, dit, dif) -> If'(tail_calls test false, tail_calls dit tp, tail_calls dif tp)
  | Seq'(exprs) -> Seq'(tail_calls_list exprs tp)
  | Set'(var, expr) -> Set'(var, tail_calls expr false)
  | Def'(var, expr) -> Def'(var, tail_calls expr false)
  | Or'(exprs) -> Or'(tail_calls_list exprs tp)
  | LambdaSimple'(lambda_params, body) -> LambdaSimple'(lambda_params, tail_calls body true)
  | LambdaOpt'(lambda_params, opt, body) -> LambdaOpt'(lambda_params, opt, tail_calls body true)
  | Applic'(app, args) -> (match tp with
                           | false -> Applic'(tail_calls app false, List.map (fun x -> tail_calls x false) args)
                           | true -> ApplicTP'(tail_calls app false, List.map (fun x -> tail_calls x false) args))
  | _ -> raise X_syntax_error

  and tail_calls_list exprs tp =
    match exprs with
    | [] -> []
    | hd::tl -> (match List.length tl with
                 | 0 -> [tail_calls hd true]
                 | _ -> (tail_calls hd false)::(tail_calls_list tl tp));;

let annotate_tail_calls e = tail_calls e false;;


(*Boxing*)
let box param min body =
  let rec add_the_set_expression param min body =
    match body with
    | Seq'(exprs) -> Seq'([Set'(VarParam(param, min), Box'(VarParam(param, min)))]@exprs) (*Set'(Var'...*)
    | _ -> Seq'([Set'(VarParam(param, min), Box'(VarParam(param, min))); body]) in (*Set'(Var'...*)

  let rec replace_get_occurances param body =
    match body with
    | Var'(VarBound (par, n1, n2)) -> if(par = param)
                                      then BoxGet'(VarBound(param, n1, n2))
                                      else body
    | Var'(VarParam (par, n1)) -> if(par = param)
                                  then BoxGet'(VarParam(param, n1))
                                  else body
    | BoxSet'(var, expr) -> BoxSet'(var, replace_get_occurances param expr)
    | If'(test, dit, dif) -> If'(replace_get_occurances param test, replace_get_occurances param dit, replace_get_occurances param dif)
    | Def'(var, expr) -> Def'(var, replace_get_occurances param expr)
    | Seq'(exprs) -> Seq'(List.map (fun e -> replace_get_occurances param e) exprs)
    | Set'(VarBound(par, n1, n2), expr) ->  if(par = param)
                                            then Set'(VarBound(param, n1, n2), replace_get_occurances param expr)
                                            else Set'(VarBound(par, n1, n2), replace_get_occurances param expr)  (*Set' arg0 var*)
    | Set'(VarParam(par, n1), expr) -> if(par = param)
                                        then Set'(VarParam(param, n1), replace_get_occurances param expr )
                                        else Set'(VarParam(par, n1), replace_get_occurances param expr)  (*Set' arg0 var*)
    | Set'(VarFree var, expr) -> Set' (VarFree var, replace_get_occurances param expr)
    | Or'(exprs) -> Or'(List.map (fun e -> replace_get_occurances param e) exprs)
    | LambdaSimple'(params, body) -> if(List.exists (fun e -> e = param) params)
                                     then LambdaSimple'(params, body)
                                     else LambdaSimple'(params, replace_get_occurances param body)
    | LambdaOpt'(params, opt, body) -> if(List.exists (fun e -> e = param) (opt::params))
                                       then LambdaOpt'(params, opt, body)
                                       else LambdaOpt'(params, opt, replace_get_occurances param body)
    | Applic'(app, args) ->	Applic'(replace_get_occurances param app, List.map (fun e -> replace_get_occurances param e) args)
    | ApplicTP'(app, args) ->	ApplicTP'(replace_get_occurances param app, List.map (fun e -> replace_get_occurances param e) args)
    | _ -> body in

  let rec replace_set_occurances param body =
    match body with
    | BoxSet'(var, expr) -> BoxSet'(var, replace_set_occurances param expr)
    | If'(test, dit, dif) -> If'(replace_set_occurances param test, replace_set_occurances param dit, replace_set_occurances param dif)
    | Seq'(exprs) -> Seq'(List.map (replace_set_occurances param) exprs)
    | Set'(VarBound(p, n1, n2), expr) -> if(p = param)
                                         then BoxSet'(VarBound(param, n1, n2), replace_set_occurances param expr)
                                         else Set'(VarBound(p, n1, n2), replace_set_occurances param expr)
    | Set'(VarParam(p, n1), expr) -> if(p = param)
                                     then BoxSet'(VarParam(param, n1), replace_set_occurances param expr)
                                     else Set'(VarParam(p, n1), replace_set_occurances param expr)
    | Set'(VarFree var, expr) -> Set'(VarFree var, replace_set_occurances param expr)
    | Def'(var, expr) -> Def'(var, replace_set_occurances param expr)
    | Or'(exprs) -> Or'(List.map (replace_set_occurances param) exprs)
    | LambdaSimple'(params, body) -> if(List.exists (fun e -> e = param) params)
                                     then LambdaSimple'(params, body)
                                     else LambdaSimple'(params, replace_set_occurances param body)
    | LambdaOpt'(params, opt, body) -> if(List.exists (fun e -> e = param) (opt::params))
                                       then LambdaOpt'(params, opt, body)
                                       else LambdaOpt'(params, opt, replace_set_occurances param body)
    | Applic'(app, args) -> Applic'(replace_set_occurances param app, List.map (replace_set_occurances param) args)
    | ApplicTP'(app, args) -> ApplicTP'(replace_set_occurances param app, List.map (replace_set_occurances param) args)
    | _ -> body in

  let body = replace_get_occurances param body in
  let body = replace_set_occurances param body in
  add_the_set_expression param min body;;

let box_check param body =
  let rec bound_check param body =
    match body with
    | Var'(VarBound (par, maj, min)) -> par = param
    | BoxSet'(var, expr) -> bound_check param expr
    | If'(test, dit, dif) -> bound_check param test || bound_check param dit || bound_check param dif
    | Seq'(exprs) -> ormap (bound_check param) exprs
    | Set'(var, expr) -> bound_check param expr
    | Def'(var, expr) -> bound_check param expr
    | Or'(exprs) -> ormap (bound_check param) exprs
    | LambdaSimple'(params, body) -> if(List.exists (fun e -> e = param) params)
                                     then false
                                     else bound_check param body
    | LambdaOpt'(params, opt, body) -> if(List.exists (fun e -> e = param) (opt::params))
                                       then false
                                       else bound_check param body
    | Applic'(app, args) -> bound_check param app || ormap (fun e -> bound_check param e) args
    | ApplicTP'(app, args) -> bound_check param app || ormap (fun e -> bound_check param e) args
    | _ -> false in

  let rec get_check param body =
    match body with
    | Var'(VarBound (par, maj, min)) -> par = param
    | Var'(VarParam (par, maj)) -> par = param
    | BoxSet'(var, expr) -> get_check param expr
    | If'(test, dit, dif) -> get_check param test || get_check param dit || get_check param dif
    | Seq'(exprs) -> ormap (get_check param) exprs
    | Set'(VarBound(par, maj, min), expr) -> par = param
    | Set'(VarParam(par, maj), expr) -> par = param
    | Set'(var, expr) -> get_check param expr
    | Def'(var, expr) -> get_check param expr
    | Or'(exprs) -> ormap (get_check param) exprs
    | LambdaSimple'(params, body) -> if(List.exists (fun e -> e = param) params)
                                     then false
                                     else get_check param body
    | LambdaOpt'(params, opt, body) -> if(List.exists (fun e -> e = param) (opt::params))
                                       then false
                                       else get_check param body
    | Applic'(app, args) -> get_check param app || ormap (fun e -> get_check param e) args
    | ApplicTP'(app, args) -> get_check param app || ormap (fun e -> get_check param e) args
    | _ -> false in

  let rec set_check param body =
    match body with
    | BoxSet'(var, expr) -> set_check param expr
    | If'(test, dit, dif) -> set_check param test || set_check param dit || set_check param dif
    | Seq'(exprs) -> ormap (set_check param) exprs
    | Set'(VarBound(par, maj, min), expr) -> par = param || set_check param expr
    | Set'(VarParam(par, maj), expr) -> par = param || set_check param expr
    | Set'(var, expr) -> set_check param expr
    | Def'(var, expr) -> set_check param expr
    | Or'(exprs) -> ormap (set_check param) exprs
    | LambdaSimple'(params, body) -> if(List.exists (fun e -> e = param) params)
                                     then false
                                     else set_check param body
    | LambdaOpt'(params, opt, body) -> if(List.exists (fun e -> e = param) (opt::params))
                                       then false
                                       else set_check param body
    | Applic'(app, args) -> set_check param app || ormap (fun e -> set_check param e) args
    | ApplicTP'(app, args) -> set_check param app || ormap (fun e -> set_check param e) args
    | _ -> false in

  (bound_check param body) && (get_check param body) && (set_check param body)

let boxing_helper params body =
  let foldfunc (param, min) body =
    if (box_check param body)
    then (box param min body)
    else body in
  let rec inds = function
    | 0 -> []
    | n -> (inds (n-1))@[(n-1)] in
  let params = List.combine params (inds (List.length params)) in
  List.fold_right foldfunc params body;;

let rec boxing e =
  match e with
  | BoxSet'(var, expr) -> BoxSet'(var, boxing expr) 
  | If'(test, dit, dif) -> If'(boxing test, boxing dit, boxing dif)
  | Seq'(exprs) -> Seq'(List.map boxing exprs)
  | Set'(var, expr) -> Set'(var, boxing expr)
  | Def'(var, expr) -> Def'(var, boxing expr)
  | Or'(exprs) -> Or'(List.map boxing exprs)
  | LambdaSimple'(params, body) -> LambdaSimple'(params, boxing (boxing_helper params body))
  | LambdaOpt'(params, opt, body) -> LambdaOpt'(params, opt, boxing (boxing_helper (opt::params) body))
  | Applic'(app, args) -> Applic'(boxing app, List.map boxing args)
  | ApplicTP'(app, args) -> ApplicTP'(boxing app, List.map boxing args)
  | _ -> e;;

let box_set e = boxing e;;

let run_semantics expr =
  box_set
    (annotate_tail_calls
       (annotate_lexical_addresses expr));;
  
end;; (* struct Semantics *)


