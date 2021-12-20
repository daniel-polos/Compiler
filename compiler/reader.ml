
#use "pc.ml";;
open PC;;
exception X_not_yet_implemented;;
exception X_this_should_not_happen;;
  
type number =
  | Fraction of int * int
  | Float of float;;
  
type sexpr =
  | Bool of bool
  | Nil
  | Number of number
  | Char of char
  | String of string
  | Symbol of string
  | Pair of sexpr * sexpr;;



  

(*more general funcs*)
(*let nt_whitespaces = star( char ' '  );;*)
let nt_whitespaces = star(disj (char '\n') (char ' '  ));;
let make_paired nt_left nt_right nt=
  let nt = caten nt_left nt in 
  let nt = pack nt (function(_, e) -> e) in 
  let nt = caten nt nt_right in
  let nt = pack nt (function(e, _) -> e) in
  nt;;

  (*let make_spaced nt=
    make_paired nt_whitespaces nt_whitespaces nt;;*)

  (*let tok_lparen = make_spaced ( char '(');;

  let tok_rparen = make_spaced ( char ')');;*)



 let letter_comment s = pack (const (fun ch -> ch!=char_of_int 10))
        (fun ch -> char ch)
        s;;

let line_comment s = pack (caten (const (fun ch -> ch=';'))
                        (caten (star letter_comment)
                               (disj (word "\n")
                                     (nt_end_of_input))))
                 (fun _ -> [' '])
                 s;;

let false_bool s =
            PC.pack (PC.caten(PC.const (fun ch-> ch='#') ) (PC.const (fun ch-> lowercase_ascii(ch)='f')))
            (fun (hashtag, (f)) -> Bool(false))
            s;;
let true_bool s =
              PC.pack (PC.caten(PC.const (fun ch-> ch='#') ) (PC.const (fun ch-> lowercase_ascii(ch)='t')))
              (fun (hashtag, (t)) -> Bool(true))
              s;;
let bool_  =
        disj (true_bool) (false_bool);;

let nt_forFINAL s= 
  if s= [] then (Nil, [' '; ' ']) else raise X_no_match;;
(*Natural*)
let digit = range (char_of_int 48) (char_of_int 57);;
let natural = plus digit;;
let zeroes = (star (const (fun ch -> ch='0')));;

(*Integer*)
let plus_sign = const (fun ch -> ch='+');;
let minus_sign = const (fun ch -> ch='-');;
let sign1 = disj plus_sign minus_sign;;
let sign2 = disj (const (fun ch -> ch='+'))
                 (const (fun ch -> ch='-'));;

let integer_list = pack (caten (maybe sign1) natural)
                 (fun (l, r) -> match l with
                                | Some '+' -> '+'::r
                                | Some '-' -> '-'::r
                                | None -> r
                                | _ -> raise X_no_match);;

let integer = 
  let foo = fun num -> Number(Fraction(int_of_string(list_to_string num), 1)) in
  pack integer_list foo;;
    
(*Float*)
let float_list = pack (caten_list [integer_list; word "."; natural])
                      (fun l -> List.concat l);; 
let float =
  (*let float_list = pack (caten_list [integer_list; word "."; natural])
                        (fun l -> List.concat l) in*)
  let foo = fun num -> Number(Float (float_of_string(list_to_string num))) in
  pack float_list foo;;

(*Scientific Notation*)
let scientific_notation =
  let sci_prefix = disj float_list integer_list in
  let sci_list = pack (caten_list [sci_prefix; word_ci "e"; integer_list])
                      (fun l -> List.concat l) in
  let foo = fun num -> Number(Float (float_of_string(list_to_string num))) in
  pack sci_list foo;;

(*Fraction*)
let rec gcd a b =
  if b = 0 then a else gcd b (a mod b);;
let fraction_list = pack (caten_list [integer_list; word "/"; natural])
                         (fun l -> List.concat l);;
let fraction s =
  let foo = pack integer_list (fun num -> num) in
  let ((a, b), rest) = (pack fraction_list foo s) in
  let (c, d) = (char '/' b) in
  let numer = int_of_string(list_to_string a) in
  let denom = int_of_string(list_to_string d) in
  let div = gcd numer denom in
  let div = if (div < 0) then (div * -1) else div in
  (Number(Fraction(numer/div, denom/div)), rest);;

(*Symbol*)
let a_z_char =  range (char_of_int 97) (char_of_int 122);;
let a_z_char_from_A_Z= pack (range (char_of_int 65) (char_of_int 90))
                      (fun ch-> lowercase_ascii(ch));;
let special_symbols_char= disj_list [char '!'; char '$'; char '^'; char '*'; char '-'; char '_'; char '='; char '+'; char '<';char '>'; char '/'; char '?'; char '.'; char ':'];;
let general_symbol_char= disj_list [digit; a_z_char; a_z_char_from_A_Z; special_symbols_char];;
let _symbol_ s =
  let (a,b) = (plus general_symbol_char) s in
    let str = list_to_string(a) in
    if( (String.length str) =1 && str=".")
    then raise X_no_match
    else (Symbol(list_to_string(a)), b);;

(*Number*)
let number = pack (not_followed_by (disj_list [scientific_notation; fraction; float; integer]) _symbol_)
    (fun num -> num);;



(*String*)

let string_char = const (fun ch -> (ch!= char_of_int 92 && ch!='"'));;

let string_return = pack (word "\\r") (fun e -> char_of_int 13);;
let string_newLine = pack (word "\\n") (fun e -> char_of_int 10);;
let string_tab = pack (word "\\t") (fun e -> char_of_int 9);;
let string_page = pack (word "\\f") (fun e -> char_of_int 12);;
let string_backSlash = pack (word "\\\\") (fun e -> char_of_int 92);;
let string_doubleQote = pack (word "\\\"") (fun e -> char_of_int 34);;

let string_begin_end = (word "\"");;

let string_clean_begin s=
  let (a,b) =(string_begin_end s) in
  b;;

let string2_ s =
  let b= (string_clean_begin s) in
  b;;
  let string3_ s= 
    let b = (string_clean_begin s) in
    (pack (star (disj_list[string_char; string_return; string_newLine;
    string_tab; string_page; string_backSlash; string_doubleQote;] ))
    (fun c-> String(list_to_string (c))) b);;
  let string4_ s=
  let (a,b)= (string3_ s) in
   (*let (e::es) = b in*)
   (a, List.tl b);;
   
   
   (*CharPrefix*)
    let char_prefix = word "#\\";;
   (*Named chars*)
   let named_chars =
     let nc_nul = pack (word_ci "nul") (fun ch -> char_of_int 0) in
     let nc_newline = pack (word_ci "newline") (fun ch -> char_of_int 10) in
     let nc_return = pack (word_ci "return") (fun ch -> char_of_int 13) in
     let nc_tab = pack (word_ci "tab") (fun ch -> char_of_int 9) in
     let nc_page = pack (word_ci "page") (fun ch -> char_of_int 12) in
     let nc_space = pack (word_ci "space") (fun ch -> char_of_int 32) in
     disj_list [nc_nul; nc_newline; nc_return; nc_tab; nc_page; nc_space];;
     (*Visible chars*)
     let visible_chars = const (fun ch -> ch>char_of_int 32);;
     
     (*Char*)
     let _char_ =
       let category = disj_list [named_chars; visible_chars] in
       pack (caten char_prefix category) (fun (a, b) -> Char (b));;

  

(*list*)
let rec general_sexp_reader s =
  if s=[] then [] else
  if s= [ ' ';] then [] else
  let (a, rest) = (general_parser_cleanWhites s) in
  if (a=Nil && rest= [ '\n';]) then [] else
  a:: (general_sexp_reader rest)

  and general_parser_cleanWhites s = 
    let (whites, rest) = (nt_Whitespaces s) in
    if (whites!=[] && rest=[]) then (Nil, [ '\n';]) else
    if (rest= []) then (Nil, [ ' ';])
      else (disj_list [bool_ ;_char_; number; string4_; _symbol_; _list_;_dotted_list_; quoted; quasi_quoted; unquoted; unquoted_spliced]  rest)

  (*  and general_parser_cleanWhites s = 
    let (whites, rest) = (nt_Whitespaces s) in
    if (rest= []) then (Nil, [ ' ';])
      else (disj_list [bool_ ;_char_; number; string4_; _symbol_; _list_;_dotted_list_; quoted; quasi_quoted; unquoted; unquoted_spliced]  rest)*)
      
  and _list_ s=
    let (sexpList, rest) =  (make_paired (char '(') (make_spaced (char ')')) (star general_parser_cleanWhites) s) in
    ((fun listA-> List.fold_right (fun curr acc -> Pair(curr, acc)) listA Nil) sexpList, rest)

  and _dotted_list_ s= 
    let (sexpList, restA) = (make_paired (char '(') (make_spaced (char '.' )) (star general_parser_cleanWhites) s) in
    let (final_sexp, restB) = (general_parser_cleanWhites restA) in
    let (whites, restC)= (nt_Whitespaces restB) in
    let (parenthes, restD)= (char ')' restC) in
    ((fun listA-> List.fold_right (fun curr acc -> Pair(curr, acc)) listA final_sexp) sexpList, restD)
  
  (*Quotelike Forms*)
  and quoted s = pack (caten (word "\'") general_parser_cleanWhites)
                      (fun (a, s) -> Pair(Symbol("quote"), Pair(s, Nil)))
                      s
  and quasi_quoted s = pack (caten (word "`") general_parser_cleanWhites)
                            (fun (a, s) -> Pair(Symbol("quasiquote"), Pair(s, Nil)))
                            s
  and unquoted s = pack (caten (word ",") general_parser_cleanWhites)
                        (fun (a, s) -> Pair(Symbol("unquote"), Pair(s, Nil)))
                        s
  and unquoted_spliced s = pack (caten (word ",@") general_parser_cleanWhites)
                                (fun (a, s) -> Pair(Symbol("unquote-splicing"), Pair(s, Nil)))
                                s
     
  and sexpr_comments s = pack (caten (word "#;") general_parser_cleanWhites)
                              (fun _ -> [' '])
                              s
  
  and nt_Whitespaces s = star (disj (disj line_comment sexpr_comments)
                                    (pack PC.nt_whitespace (fun x-> [' ';]) )) s
  and nt_Whitespaces2 s = pack (star (disj (disj line_comment sexpr_comments)
                                    (pack PC.nt_whitespace (fun x-> [' ';]) )))
                                    (fun x-> ' ') s
  and make_spaced nt=
            make_paired nt_Whitespaces2 nt_Whitespaces2 nt;;                  

  

let rec sexpr_eq s1 s2 =
  match s1, s2 with
  | Bool(b1), Bool(b2) -> b1 = b2
  | Nil, Nil -> true
  | Number(Float f1), Number(Float f2) -> abs_float(f1 -. f2) < 0.001
  | Number(Fraction (n1, d1)), Number(Fraction (n2, d2)) -> n1 = n2 && d1 = d2
  | Char(c1), Char(c2) -> c1 = c2
  | String(s1), String(s2) -> s1 = s2
  | Symbol(s1), Symbol(s2) -> s1 = s2
  | Pair(car1, cdr1), Pair(car2, cdr2) -> (sexpr_eq car1 car2) && (sexpr_eq cdr1 cdr2)
  | _ -> false;;

module Reader: sig
  val read_sexprs : string -> sexpr list
end
= struct
let normalize_scheme_symbol str =
  let s = string_to_list str in
  if (andmap
	(fun ch -> (ch = (lowercase_ascii ch)))
	s) then str
  else Printf.sprintf "|%s|" str;;


  let read_sexprs string = 
    general_sexp_reader (string_to_list string);;
  
  
end;; (* struct Reader *)
