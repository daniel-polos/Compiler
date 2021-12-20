#use "reader.ml";;
open Reader;;

type constant =
  | Sexpr of sexpr
  | Void

type expr =
  | Const of constant
  | Var of string
  | If of expr * expr * expr
  | Seq of expr list
  | Set of expr * expr
  | Def of expr * expr
  | Or of expr list
  | LambdaSimple of string list * expr
  | LambdaOpt of string list * string * expr
  | Applic of expr * (expr list);;

let rec expr_eq e1 e2 =
  match e1, e2 with
  | Const Void, Const Void -> true
  | Const(Sexpr s1), Const(Sexpr s2) -> sexpr_eq s1 s2
  | Var(v1), Var(v2) -> String.equal v1 v2
  | If(t1, th1, el1), If(t2, th2, el2) -> (expr_eq t1 t2) &&
                                            (expr_eq th1 th2) &&
                                              (expr_eq el1 el2)
  | (Seq(l1), Seq(l2)
    | Or(l1), Or(l2)) -> List.for_all2 expr_eq l1 l2
  | (Set(var1, val1), Set(var2, val2)
    | Def(var1, val1), Def(var2, val2)) -> (expr_eq var1 var2) &&
                                             (expr_eq val1 val2)
  | LambdaSimple(vars1, body1), LambdaSimple(vars2, body2) ->
     (List.for_all2 String.equal vars1 vars2) &&
       (expr_eq body1 body2)
  | LambdaOpt(vars1, var1, body1), LambdaOpt(vars2, var2, body2) ->
     (String.equal var1 var2) &&
       (List.for_all2 String.equal vars1 vars2) &&
         (expr_eq body1 body2)
  | Applic(e1, args1), Applic(e2, args2) ->
     (expr_eq e1 e2) &&
       (List.for_all2 expr_eq args1 args2)
  | _ -> false;;
	
                       
exception X_syntax_error;;

module type TAG_PARSER = sig
  val tag_parse_expressions : sexpr list -> expr list
end;; (* signature TAG_PARSER *)

module Tag_Parser : TAG_PARSER = struct

let reserved_word_list =
  ["and"; "begin"; "cond"; "define"; "else";
   "if"; "lambda"; "let"; "let*"; "letrec"; "or";
   "quasiquote"; "quote"; "set!"; "pset!"; "unquote";
   "unquote-splicing"];;  

(* work on the tag parser starts here *)


let rec separating_vs_Expressions pairs_vs_Expressions =
  match pairs_vs_Expressions with
    | Pair (first_duo, rest_duoes) -> (match first_duo with
                                      | Pair(v, _Exp_row) -> (match _Exp_row with
                                                              | Pair(_Exp, Nil) -> if rest_duoes = Nil then (Pair(v, Nil) , Pair(_Exp, Nil)) else
                                                                                    let (next_vs, next_Exps)= (separating_vs_Expressions rest_duoes) in
                                                                                    (Pair(v, next_vs), Pair(_Exp, next_Exps))
                                                              | _ -> raise X_syntax_error)
                                      | _ -> raise X_syntax_error)
    | _ -> raise X_syntax_error;;      

let rec matching_with_upper_case args vals =
  match args with
  | Nil -> Nil
  | Pair (first_arg, Nil)    -> (match vals with 
                              | Pair (first_val, rest_vals) -> (match first_arg with
                                                              | Symbol fa -> let frstA= (String.uppercase_ascii fa) in Pair (Pair(Symbol frstA, Pair(first_val, Nil)), Nil)
                                                              | _ -> raise X_syntax_error) 
                              | _ -> raise X_syntax_error)
  | Pair(first_arg, rest_args) -> (match vals with 
                              | Pair (first_val, rest_vals) -> (match first_arg with
                                                              | Symbol fa -> let frstA= (String.uppercase_ascii fa) in Pair(Pair(Symbol frstA, Pair(first_val, Nil)), (matching_with_upper_case rest_args rest_vals))
                                                              | _ -> raise X_syntax_error) 
                              | _ -> raise X_syntax_error)
  | _ ->  raise X_syntax_error;;

let rec matching_with_set_with_apper_case args =
  match args with
  | Nil -> Nil
  | Pair (first_arg, rest_args) -> (match first_arg with
                                  | Symbol fa -> let frstA= (String.uppercase_ascii fa) in Pair(Pair(Symbol "set!", Pair(first_arg, Pair(Symbol frstA, Nil))), (matching_with_set_with_apper_case rest_args))
                                  | _ -> raise X_syntax_error)
  |_ -> raise X_syntax_error;;

let rec vs_and_quotes vs =
  if vs = Nil then Nil else
  match vs with
  | Pair (first_v, rest_vs)-> Pair(Pair (first_v,   Pair (Pair (Symbol "quote", Pair (Symbol "whatever", Nil)), Nil)), vs_and_quotes rest_vs)
  | _ -> raise X_syntax_error;;

let rec let_rec_final_let exprs=
  Pair (Pair (Symbol "let", Pair(Nil, exprs)), Nil);;

let rec matching_sets3 vs _Expressions exprs =
  match vs with
  | Nil -> Nil
  | Pair (first_vs, Nil)    -> (match _Expressions with 
                              | Pair (first_Expr, rest_Exprs) -> Pair(Pair(Symbol "set!", Pair(first_vs, Pair(first_Expr, Nil))), (let_rec_final_let exprs))
                              | _ -> raise X_syntax_error)
  | Pair(first_vs, rest_vs) -> (match _Expressions with 
                              | Pair (first_Expr, rest_Exprs) -> Pair(Pair(Symbol "set!", Pair(first_vs, Pair(first_Expr, Nil))), (matching_sets3 rest_vs rest_Exprs exprs))
                              | _ -> raise X_syntax_error)
  | _ ->  raise X_syntax_error;;
  
let macro_mit_define name args exprs =
  Pair(Symbol("define"), Pair(name, Pair(Pair(Symbol("lambda"), Pair(args, exprs)), Nil)));;

let rec macro_quasiquote sexpr = match sexpr with
                            | Nil -> Pair(Symbol("quote"), Pair(Nil, Nil))
                            | Symbol(x) -> Pair(Symbol("quote"), Pair(Symbol(x), Nil))
                            | Pair(Symbol("unquote"), Pair(x, Nil)) -> x
                            | Pair(Symbol("unquote-splicing"), Pair(x, Nil)) -> raise X_syntax_error
                            | Pair(car, cdr) -> (match (car, cdr) with
                                                | (Pair(Symbol("unquote-splicing"), Pair(x, Nil)), cdr) -> Pair(Symbol("append"), Pair(x, Pair(macro_quasiquote cdr, Nil)))
                                                | (car, Pair(Symbol("unquote-splicing"), Pair(x, Nil))) -> Pair(Symbol("cons"), Pair(macro_quasiquote car, Pair(x, Nil)))
                                                | _ -> (Pair(Symbol("cons"), Pair((macro_quasiquote car), Pair((macro_quasiquote cdr), Nil)))))
                            | _ -> sexpr;; 
                        
let rec macro_cond ribs = match ribs with
                          | Nil -> Nil
                          | Pair(Pair(test, Pair(Symbol("=>"), dit)), Nil) -> let lambda_expr = Pair(Symbol("lambda"), Pair(Nil, dit)) in
                                                                              let args = Pair(Pair(Symbol("value"), Pair(test, Nil)), Pair(Pair(Symbol("f"), Pair(lambda_expr, Nil)), Nil)) in
                                                                              let if_expr = Pair(Symbol("if"), Pair(Symbol("value"), Pair(Pair(Pair(Symbol("f"), Nil), Pair(Symbol("value"), Nil)), Nil))) in
                                                                              Pair(Symbol("let"), Pair(args, Pair(if_expr, Nil)))
                          | Pair(Pair(test, Pair(Symbol("=>"), dit)), rest) -> let result = macro_cond rest in
                                                                               let ribs = match result with
                                                                                          | Nil -> Nil
                                                                                          | _ -> Pair(result, Nil) in
                                                                               let rest = Pair(Symbol("lambda"), Pair(Nil, ribs)) in
                                                                               let lambda_expr = Pair(Symbol("lambda"), Pair(Nil, dit)) in
                                                                               let args = Pair(Pair(Symbol("value"), Pair(test, Nil)), Pair(Pair(Symbol("f"), Pair(lambda_expr, Nil)), Pair(Pair(Symbol("rest"), Pair(rest, Nil)), Nil))) in
                                                                               let if_expr = Pair(Symbol("if"), Pair(Symbol("value"), Pair(Pair(Pair(Symbol("f"), Nil), Pair(Symbol("value"), Nil)), Pair(Pair(Symbol("rest"), Nil), Nil)))) in
                                                                               Pair(Symbol("let"), Pair(args, Pair(if_expr, Nil)))
                          | Pair(Pair(Symbol("else"), x), Nil) -> Pair(Symbol("begin"), x)
                          | Pair(Pair(test, dit), rest) -> let result = macro_cond rest in
                                                           let ribs = match result with
                                                                      | Nil -> Nil
                                                                      | _ -> Pair(result, Nil) in
                                                           Pair(Symbol("if"), Pair(test, Pair(Pair(Symbol("begin"), dit), ribs)))
                          | _ -> raise X_syntax_error;;                                                

let macro_and sexpr = match sexpr with
| Nil -> Bool(true)
| Pair(car, Nil) -> car
| Pair(car, cdr) -> Pair(Symbol ("if"), Pair(car, Pair(Pair(Symbol("and"), cdr), Pair(Bool(false), Nil))))
| _ -> raise X_syntax_error;;

let macro_expansion_Let let_exp_rest =
  match let_exp_rest with
  | Pair (pairs_vs_Expressions, exprs) -> 
    if pairs_vs_Expressions = Nil then Pair( Pair(Symbol "lambda", Pair(Nil, exprs)), Nil) else
      let (vs, _Expressions) = (separating_vs_Expressions pairs_vs_Expressions) in
      Pair( Pair (Symbol "lambda", Pair( vs, exprs)), _Expressions)
  | _ -> raise X_syntax_error;;

let macro_expansion_let_star let_star_rest =
  match let_star_rest with
  | Pair (pairs_vs_Expressions, exprs) ->
    if pairs_vs_Expressions = Nil then 
    Pair(Symbol "let", Pair( Nil, exprs)) else
    (match pairs_vs_Expressions with
    | Pair (first_duo, rest_duoes) -> (match rest_duoes with 
                                      |Nil -> Pair(Symbol "let", Pair(Pair(first_duo, Nil), exprs))
                                      |Pair(x, y) ->  Pair(Symbol "let",Pair (Pair(first_duo, Nil), Pair(Pair(Symbol "let*",Pair(rest_duoes, exprs)), Nil)))
                                      |_ -> raise X_syntax_error)
    | _ -> raise X_syntax_error)
    | _ -> raise X_syntax_error;;

let macro_expansion_let_rec let_rec_rest =
  match let_rec_rest with 
  | Pair (pairs_vs_Expressions, exprs) ->
  let (vs, _Expressions) = (separating_vs_Expressions pairs_vs_Expressions) in
  let set_and_expr_ready= matching_sets3 vs _Expressions exprs in
  Pair(Symbol "let", Pair(vs_and_quotes vs,  set_and_expr_ready))
  | _ -> raise X_syntax_error;;

let  macro_expansion_pset pset_rest =
  let (args, vals) = (separating_vs_Expressions pset_rest) in
  Pair(Symbol "let", Pair( (matching_with_upper_case args vals) , (matching_with_set_with_apper_case args)));;


let rec parsing_sexp sexp =
  match sexp with 
  (*Const*)
  | Pair(Symbol("quote"), Pair(x, Nil)) -> Const(Sexpr(x))
  | Bool(x) -> Const (Sexpr(Bool(x)))
  | Char(x) -> Const (Sexpr(Char(x)))
  | Number(x) -> Const(Sexpr(Number(x)))
  | String(x) -> Const (Sexpr(String(x)))
  (*If*)
  | Pair(Symbol("if"), Pair(test, Pair(dit, Nil)))->If(parsing_sexp test, parsing_sexp dit, Const(Void))
  | Pair(Symbol("if"), Pair(test, Pair(dit, Pair(dif, Nil))))->If( parsing_sexp test, parsing_sexp dit, parsing_sexp dif)
  (*var*)
  | Symbol (x) -> if (List.mem x reserved_word_list) then raise X_no_match else Var(x)
  (*Or*)
  | Pair (Symbol "or", Nil) -> Const (Sexpr(Bool (false)))
  | Pair (Symbol "or", Pair(x, Nil)) -> (parsing_sexp x)
  | Pair (Symbol "or", rest) -> Or(list_to_exprlist rest)
  (*Sequence*)
  | Pair (Symbol "begin", Nil) -> Const (Void)
  | Pair (Symbol "begin", Pair(x, Nil)) -> (parsing_sexp x)
  | Pair (Symbol "begin", Pair(x, rest)) -> Seq(list_to_exprlist_for_seq(Pair(x, rest)) )
  (*Define reg*) 
  | Pair (Symbol "define" , Pair( Symbol name, Pair (exp, Nil))) -> Def ((parsing_sexp (Symbol name)), parsing_sexp exp)
  (*Define MIT*)
  | Pair(Symbol("define"), Pair(Pair(Symbol(name), args), exprs)) -> parsing_sexp (macro_mit_define (Symbol(name)) args exprs)

  (*Lambda*)
  | Pair (Symbol ("lambda") , Pair( args, expsPlus)) ->  if (is_proper_list args) then
                                                       LambdaSimple  (properList_ofSymbols_to_string_list args, parsing_sexp (Pair (Symbol "begin", expsPlus))) else
                                                       let (strList, str)= (make_lambdaOpt_args args) in
                                                       LambdaOpt (strList, str ,parsing_sexp (Pair (Symbol "begin", expsPlus)) )
  (*Assignments*)
  | Pair(Symbol("set!"), Pair(vari, Pair(valu, Nil))) -> Set(parsing_sexp vari, parsing_sexp valu)
  | Pair (Symbol "let", rest) -> parsing_sexp ( macro_expansion_Let rest)
  | Pair (Symbol "let*", rest) -> parsing_sexp ( macro_expansion_let_star rest)
  | Pair (Symbol "letrec", rest) -> parsing_sexp ( macro_expansion_let_rec rest)
  | Pair (Symbol "pset!", rest) -> parsing_sexp (macro_expansion_pset rest)
  (*Quasiquoted*)
  | Pair(Symbol("quasiquote"), Pair(sexpr, Nil)) -> parsing_sexp (macro_quasiquote sexpr)
  (*cond*)
  | Pair(Symbol("cond"), ribs) -> parsing_sexp (macro_cond ribs)
  (*and*)
  | Pair(Symbol("and"), sexpr) -> parsing_sexp (macro_and sexpr)
  (*Applications*)
  | Pair(app, args) -> if (is_proper_list args)
                          then (Applic (parsing_sexp app, tag_parse_list args))
                          else raise X_syntax_error
  | _ -> raise X_syntax_error
  

  and tag_parse_list sexpr_list = match sexpr_list with
    | Nil -> []
    | Symbol s -> [parsing_sexp (Symbol s) ]
    | Pair(car, cdr) -> parsing_sexp car :: tag_parse_list cdr
    | _ -> raise X_syntax_error

  and list_to_exprlist_for_seq lst=
    match lst with 
    | Nil -> []
    | Pair (Pair(Symbol "begin", nested_rest), rests) ->   (List.append (list_to_exprlist_for_seq nested_rest) (list_to_exprlist_for_seq rests))
    | Pair (x, rest)-> (match x with
                         |Nil -> []
                         |_ ->  let xExpr= (parsing_sexp x) in
                           if rest= Nil then xExpr:: [] else
                             xExpr :: (list_to_exprlist_for_seq rest))
    | _ -> raise X_syntax_error

  and list_to_exprlist lst=
     match lst with 
    | Pair (x, rest)->
    if x= Nil then [] else (*probably unnecessary*)  
      let xExpr= (parsing_sexp x) in
      if rest= Nil then xExpr:: [] else
        xExpr :: (list_to_exprlist rest)
    |_ -> raise X_syntax_error 

  and properList_ofSymbols_to_string_list = function
    | Nil -> []
    | Pair (Symbol x, rest) -> x :: (properList_ofSymbols_to_string_list rest)
    | _-> raise X_no_match

  and make_lambdaOpt_args = function
    | Pair (Symbol x, Symbol y) -> ([x], y ) (*lambdaOpt_args_optional Pair (x,y)*)
    | Pair (Symbol x, rest) -> let (a, b) = (make_lambdaOpt_args rest) in ( x::a, b)
    | Symbol x -> ([], x)
    | _-> raise X_syntax_error
  
  and is_proper_list args = match args with
                            | Nil -> true
                            | Pair(car, cdr) -> (is_proper_list cdr)
                            | _ -> false;;

  
let tag_parse_expressions sexpr = 
  List.map parsing_sexp sexpr;;

  
end;; (* struct Tag_Parser *)

