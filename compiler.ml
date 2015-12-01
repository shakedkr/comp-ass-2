 
(* compiler.ml
 * A compiler from Scheme to CISC
 *
 * Programmer: Mayer Goldberg, 2015
 *)

#use "pc.ml";;

exception X_not_yet_implemented;;
exception X_this_should_not_happen;;
exception X_invalid_fraction;;
exception X_should_not_have_denominator_zero;;

let rec ormap f s =
  match s with
  | [] -> false
  | car :: cdr -> (f car) || (ormap f cdr);;

let rec andmap f s =
  match s with
  | [] -> true
  | car :: cdr -> (f car) && (andmap f cdr);;	  

let string_to_list str =
  let rec loop i limit =
    if i = limit then []
    else (String.get str i) :: (loop (i + 1) limit)
  in
  loop 0 (String.length str);;

let list_to_string s =
  let rec loop s n =
    match s with
    | [] -> String.make n '?'
    | car :: cdr ->
       let result = loop cdr (n + 1) in
       String.set result n car;
       result
  in
  loop s 0;;

type fraction = {numerator : int; denominator : int};;

type number =
  | Int of int
  | Fraction of fraction;;

type sexpr =
  | Void
  | Bool of bool
  | Nil
  | Number of number
  | Char of char
  | String of string
  | Symbol of string
  | Pair of sexpr * sexpr
  | Vector of sexpr list;;

module type SEXPR = sig
  val sexpr_to_string : sexpr -> string
end;; (* signature SEXPR *)
open PC;;
module Sexpr : SEXPR = struct
  
exception X_invalid_fraction of fraction;;

let normalize_scheme_symbol str =
  let s = string_to_list str in
  if (andmap
	(fun ch -> (ch = (Char.lowercase ch)))
	s) then str
  else Printf.sprintf "|%s|" str;;

(***********3.3 test the code*******)
let bool_to_string s = 
  match s with
  |true -> "#t"
  |false -> "#f"
  |_-> raise X_this_should_not_happen ;;

let number_to_string s =
  match s with
  |Int num -> string_of_int num
  |Fraction frac -> match frac with
		    | {numerator = a; denominator = b} -> (string_of_int a) ^"/"^ (string_of_int b)
  |_ -> raise X_syntax_error;;

    

let rec sexpr_to_string sexpr = 
  match sexpr with
  | Bool s -> bool_to_string s
  | Number s -> number_to_string s
  | Symbol s -> s
  | String s -> s
  | Char s -> (Char.escaped s)
  | Nil -> "()"
  | Pair (a,b) -> "("^ pair_to_string (a,b)^")"
  | Vector v -> vector_to_string v
  |_-> raise X_this_should_not_happen

and vector_to_string v = 
  let ans_begin =  "#(" in
  let ans_continune = String.concat " " (List.map sexpr_to_string v) in
  let ans_end =  ")" in
  let ans = ans_begin ^ ans_continune ^ ans_end in
ans

and pair_to_string (a,b) =
  let first_part = (sexpr_to_string a) in
  let rest_part = first_part ^ match b with
			      |Nil -> ""
			      |Pair (c,d) -> " "^(pair_to_string (c,d))
			      |_ -> ". " ^ (sexpr_to_string b)
in rest_part
;;
  





end;; (* struct Sexpr *)

module type PARSER = sig
(*  val read_sexpr : string -> sexpr
  val read_sexprs : string -> sexpr list *)
end;;

module Parser(* : PARSER*) = struct


 
(*
let nt_any_with_spaces = 
let nt = caten (star nt_whitespace) nt_any in
let nt = caten nt (star nt_whitespace) in
nt;;
 *)



(************ 3.2.1 ********)
let nt_bool =
let nt = char '#' in
let nt = caten nt (char 't') in
let nt = pack nt (fun _->true) in
let nt' = char '#' in
let nt' = caten nt' (char 'T') in
let nt' = pack nt' (fun _->true) in
let nt'' = char '#' in
let nt'' = caten nt'' (char 'f') in
let nt'' = pack nt'' (fun _->false) in
let nt''' = char '#' in
let nt''' = caten nt''' (char 'F') in
let nt''' = pack nt''' (fun _->false) in
let nt = disj nt (disj nt' (disj nt'' nt''')) in
let nt = pack nt (fun a -> Bool a) in 
nt ;;


(************ 3.2.2 - Numbers ********)

  
let make_char_value base_char displacement =
  let base_char_value = Char.code base_char in
  fun ch -> (Char.code ch) - base_char_value + displacement;;

let nt_digit_0_9 = pack (range '0' '9') (make_char_value '0' 0);;
  
let nt_digit_1_9 = pack (range '0' '9') (make_char_value '0' 0);;
  
let nt_digit_a_f = pack (range 'a' 'f') (make_char_value 'W' 0);;

let nt_digit_A_F = pack (range 'A' 'F') (make_char_value '7' 0);;

let nt_hexa_digit = disj nt_digit_0_9  (disj nt_digit_a_f nt_digit_A_F);;

let nt_nat =
  let nt = range '1' '9' in
  let nt = pack nt (make_char_value '0' 0) in
  let nt' = range '0' '9' in
  let nt' = pack nt' (make_char_value '0' 0) in
  let nt' = star nt' in
  let nt = caten nt nt' in
  let nt = pack nt (fun (d, ds) -> (d :: ds)) in
  let nt = pack nt (fun s -> List.fold_left (fun a b -> a * 10 + b) 0 s) in
  let nt' = char '0' in
  let nt'' = char '0' in
  let nt''' = range '0' '9' in
  let nt'' = caten nt'' nt''' in
  let nt' = diff nt' nt'' in
  let nt' = pack nt' (fun e -> 0) in
  let nt = disj nt nt' in
  nt;;

let nt_dec =
  let nt = char '-' in
  let nt = pack nt (fun e -> -1) in
  let nt' = char '+' in
  let nt' = pack nt' (fun e -> 1) in
  let nt = disj nt nt' in
  let nt = maybe nt in
  let nt = pack nt (function | None -> 1 | Some(mult) -> mult) in

 let nt' = range '0' '9' in
  let nt' = pack nt' (make_char_value '0' 0) in
  let nt' = plus nt' in
  let nt' = pack nt' (fun s -> List.fold_left (fun a b -> a * 10 + b) 0 s) in
  let nt = caten nt nt' in
  let nt = pack nt (fun (mult, n) -> (mult * n)) in
  nt;;



let nt_hexa_prefix = 
  let nt = word_ci "0x" in 
  let nt = pack nt (fun a-> 1) in
  let nt' = word_ci "+0x" in
  let nt' = pack nt' (fun a-> 1) in
  let nt'' = word_ci "-0x" in
  let nt'' = pack nt'' (fun a-> -1) in
  let nt = disj nt'' (disj nt' nt) in
  nt;;


let nt_hexa=
  let nt = caten nt_hexa_prefix (plus nt_hexa_digit) in
  let nt = pack nt (fun(p,s)-> p *List.fold_left (fun a b -> a*16  +b) 0 s) in
  let nt = pack nt (fun a ->  a) in
  nt;;
  

let nt_int = disj nt_hexa nt_dec ;;

let rec gcd a b = 
  if b=0 then a
  else gcd b (a mod b);;

let nt_first_frac frac =
  match frac with
  |Fraction({numerator =a; denominator =c}) ->a
  |Int _->raise X_invalid_fraction ;;

let nt_second_frac frac =
  match frac with
  |Fraction({numerator =a; denominator =c}) ->c
  |Int _->raise X_invalid_fraction;;


let nt_reduction frac =
  let a = nt_first_frac frac in
  let b = nt_second_frac frac in
  let g = gcd a b in
  if b==0 then 
    raise X_should_not_have_denominator_zero
  else if g==a && g==b then 
    Int 1
  else if g==b then
    Int (a/b)
  else
    Fraction({numerator =a/g; denominator =b/g}) 
 ;;
    
                               
let nt_fraction =
let nt = caten nt_int (char '/') in
let nt = caten nt nt_int in
let nt =pack nt (fun ((a,b),c) -> nt_reduction ( Fraction({numerator =a; denominator =c})) ) in 
nt;;

let nt_int = disj nt_hexa nt_dec ;;

let nt_number  =
  let nt = nt_int in
  let nt = pack nt (fun a -> Int a) in
  let nt = disj nt_fraction  nt in 
  let nt = pack nt (fun a-> Number a) in
  nt ;;


  
(******3.2.3 Symbol****)
let nt_symbol = 

  let nt_low_case = (range 'a' 'z') in
  let nt_digits = (range '0' '9') in
  let nt_up_case = (range 'A' 'Z')  in
     let nt_up_case = pack nt_up_case (fun ch -> Char.lowercase ch) in

  let nt_punc = (range '<' '?') in
  let nt_punc = disj nt_punc (range '*' '+') in
  let nt_punc = disj nt_punc (range '^' '_') in
  let nt_punc = disj nt_punc  (char '!') in
  let nt_punc = disj nt_punc (char '$') in
  let nt_punc = disj nt_punc (char '/') in
  let nt_punc = disj nt_punc (char '-') in
  let nt = disj_list [nt_low_case; nt_digits; nt_up_case; nt_punc] in
  let nt = plus nt in
  let nt = pack nt (fun ch-> Symbol (list_to_string ch)) in
  nt;;




(***** 3.2.4 String ******)
let nt_meta_char_for_string =
  let nt_newline = (word "\\n") in
  let nt_newline = pack nt_newline (fun _-> '\n') in
  let nt_return =  (word "\\r") in
  let nt_return = pack nt_return (fun _-> '\r') in
  let nt_tab =  (word "\\t") in
  let nt_tab = pack nt_tab (fun _-> '\t') in
  let nt_page =  (word "\\f") in
  let nt_page = pack nt_page (fun _-> '\012') in
  let nt_backslash = (word "\\\\") in
  let nt_backslash = pack nt_backslash (fun _->'\\') in
  let nt_2_quote =  (word "\\\"") in
  let nt_2_quote = pack nt_2_quote (fun _-> '\"') in
  let nt = disj_list [nt_newline; nt_return; nt_tab; nt_page; nt_backslash; nt_2_quote] in
nt;;

let nt_string =
  let nt_q = (char '"') in
  let anything = diff nt_any (char '"') in
  let nt_words = disj nt_meta_char_for_string anything in
  let nt_words = star nt_words in
  let nt = caten nt_q (caten nt_words nt_q) in
  let nt = pack nt (fun (_,(words,_))-> String (list_to_string words)) in
nt;;
  

  
(*****3.2.5 char******)

let nt_meta_char_for_char =
  let nt_newline_char = (word_ci "#\\newline") in
  let nt_newline_char = pack nt_newline_char (fun _-> '\n') in
  let nt_return_char = (word_ci "#\\return") in
  let nt_return_char = pack nt_return_char (fun _-> '\r') in
  let nt_tab_char = (word_ci "#\\tab") in
  let nt_tab_char = pack nt_tab_char (fun _-> '\t') in
  let nt_formfeed = (word_ci "#\\page") in
  let nt_formfeed = pack nt_formfeed (fun _-> '\012') in
  let nt_space = (word_ci "#\\space") in
  let nt_space = pack nt_space (fun _-> ' ') in
  let nt = disj_list [nt_newline_char; nt_return_char; nt_tab_char; nt_formfeed; nt_space] in
nt;;

let nt_char =
  let nt_begin_char = caten (char '#') (char '\\') in
  let visible_char = (range '!' '~') in
  let nt_chars = caten nt_begin_char visible_char in
  let nt_chars = pack nt_chars (fun ((_,_),c) -> c) in
  let nt = disj nt_meta_char_for_char nt_chars in
  let nt = pack nt ( fun c -> Char c ) in
nt;;



(*********3.2.7 Pair**********)

let rec nt_pair s= 
  let nt =caten (star nt_comment) (char '(') in
  let nt' = (star nt_sexpr) in
  let nt = caten nt nt' in
  let nt = pack nt (fun ((_,_),c)-> c ) in
 

 (* let nt_nil = char ')' in *)
  let nt_nil = caten (star nt_comment) (char ')') in
  let nt_nil = pack nt_nil (fun _ -> Nil) in



  let nt'' =char '.' in
  let nt'' = caten nt'' nt_sexpr in
  let nt'' = caten nt'' (char ')') in
  let nt'' = pack nt'' (fun ((_,b),_)->b) in

(*
  let nt'' = char '.' in
  let nt''' = char ')' in
  let nt'' = caten nt'' (caten nt_sexpr nt''') in
  let nt'' = caten nt'' (star nt_comment) in
  let nt'' = pack nt'' (fun ((a,(b,c)),_)->b)  in 
 *)

  let nt' = disj nt_nil nt'' in

  let nt = caten nt nt' in
  let nt = caten nt (star nt_comment) in
  let nt = pack nt (fun ((a,b),_)-> (a,b)) in




  let nt= pack nt (fun (left, right) ->
		    List.fold_right 
		      (fun left right ->Pair (left,right))
		      left 
		      right) in
  nt s

and nt_sexpr s=
  disj_list [ add_comment nt_bool; add_comment nt_number; add_comment nt_string ;add_comment nt_symbol ;add_comment nt_char
	      ; add_comment nt_vector  ;add_comment nt_pair ] s



and nt_line_comment = 
  let nt= char ';' in
  let nt' = diff nt_any (char '\n') in
  let nt' = star nt' in
  let nt= caten nt nt' in
  let nt = pack nt (fun _-> true) in 
  nt;

and nt_sexpr_comment s =
  let nt = word_ci "#;" in
  let nt = caten nt nt_sexpr in
  let nt = pack nt (fun _ -> true ) in
  nt s

and nt_comment s = 
  let nt = nt_whitespace in
  let nt= pack nt (fun _ ->true) in
  let nt' = nt_line_comment in
  let nt'' =  nt_sexpr_comment in
  let nt =disj_list [nt ; nt'; nt''] s in
  nt

and add_comment nt s = 
  let nt = caten (star nt_comment) nt in
  let nt = caten nt (star nt_comment) in
  let nt = pack nt (fun((_,a),_)->a) in
  nt s 


(******** 3.2.8 Vector *****)

(*
and  nt_vector s= 
  let nt_begin = caten (star nt_comment) (word "#(") in
  let nt_continune = caten nt_begin (star nt_sexpr) in
  let nt_continune = caten nt_continune (char ')') in
  let nt_continune = caten nt_continune (star nt_comment) in
*)

and  nt_vector s= 
  let nt_begin = caten (star nt_comment) (word "#(") in
  let nt_begin = caten nt_begin (star nt_comment) in
  let nt_continune = caten nt_begin (star nt_sexpr) in
  let nt_continune = caten nt_continune (char ')') in
  let nt_continune = caten nt_continune (star nt_comment) in






  let nt = pack nt_continune (fun (((((_,_),_),v),_),_) ->
			       Vector ( List.fold_right 
					  (fun left right -> left::right)
					  v 
					  [])) in
 nt s;;
 
 
 (******3.2.9 Quote-like forms *****)

let nt_quote_types = 
  let nt_q1 = (word "'") in
  let nt_q1 = pack nt_q1 (fun _-> "quote") in
  let nt_q2 = (word "`") in
  let nt_q2 = pack nt_q2 (fun _-> "quasiquote") in
  let nt_q3 = (word ",@") in
  let nt_q3 = pack nt_q3 (fun _-> "unquote-splicing") in
  let nt_q4 = (word ",") in
  let nt_q4 = pack nt_q4 (fun _-> "unquote") in
  let nt = disj_list [nt_q1; nt_q2; nt_q3; nt_q4] in
nt;;

let nt_quote = 
  let nt = caten nt_quote_types nt_sexpr in
  let nt = pack nt (fun (a,b)-> Pair (Symbol a, Pair (b, Nil))) in
nt;;


let rec read s =
  let nt = disj_list [add_comment nt_bool;add_comment nt_number;add_comment nt_string;add_comment nt_char;add_comment nt_symbol ; 
		      add_comment nt_pair;add_comment nt_vector ] in
  let nt = nt s in
  if ((snd nt) = [] )
       then [(fst nt)]
	      else 
		(fst nt)::(read (snd nt)) ;;
 

let read_sexpr string=  
  let s = string_to_list string in
  let nt = disj_list [add_comment nt_quote; add_comment nt_bool;add_comment nt_number; add_comment nt_string ;add_comment nt_char;add_comment nt_symbol;
		      add_comment nt_pair;add_comment nt_vector ] in
  let nt = nt s in
  let nt =  fst nt in      
  nt;;
 
let read_sexprs string = 
  let s = string_to_list string in
  let s = read s in
  s;;
     

end;; (* struct Parser *)

(* work on the tag parser starts here *)

type expr =
  | Const of sexpr
  | Var of string
  | VarFree of string
  | VarParam of string * int
  | VarBound of string * int * int
  | If of expr * expr * expr
  | Seq of expr list
  | Set of expr * expr
  | Def of expr * expr
  | Or of expr list
  | LambdaSimple of string list * expr
  | LambdaOpt of string list * string * expr
  | Applic of expr * (expr list)
  | ApplicTP of expr * (expr list);;

exception X_syntax_error;;

module type TAG_PARSER = sig
  val read_expression : string -> expr
  val read_expressions : string -> expr list
  val expression_to_string : expr -> string
end;; (* signature TAG_PARSER *)

module Tag_Parser : TAG_PARSER = struct

let reserved_word_list =
  ["and"; "begin"; "cond"; "define"; "do"; "else";
   "if"; "lambda"; "let"; "let*"; "letrec"; "or";
   "quasiquote"; "quote"; "set!"; "unquote";
   "unquote-splicing"];;  

let rec process_scheme_list s ret_nil ret_one ret_several =
  match s with
  | Nil -> ret_nil ()
  | (Pair(sexpr, sexprs)) ->
     process_scheme_list sexprs
			 (fun () -> ret_one sexpr)
			 (fun sexpr' -> ret_several [sexpr; sexpr'])
			 (fun sexprs -> ret_several (sexpr :: sexprs))
  | _ -> raise X_syntax_error;;
  
let scheme_list_to_ocaml_list args = 
  process_scheme_list args
		      (fun () -> [])
		      (fun sexpr -> [sexpr])
		      (fun sexprs -> sexprs);;
    
let expand_let_star ribs sexprs =
  let ribs = scheme_list_to_ocaml_list ribs in
  let params = List.map (function
			  | (Pair(name, (Pair(expr, Nil)))) -> name
			  | _ -> raise X_this_should_not_happen) ribs in
  let args = List.map
	       (function
		 | (Pair(name, (Pair(expr, Nil)))) -> expr
		 | _ -> raise X_this_should_not_happen) ribs in
  let params_set = List.fold_right
		     (fun a s ->
		      if (ormap
			    (fun b ->
			     (match (a, b) with
			      | (Symbol a, Symbol b) -> a = b
			      | _ -> raise X_this_should_not_happen))
			    s)
		      then s else a :: s)
		     params
		     [] in
  let place_holders = List.fold_right
			(fun a s -> Pair(a, s))
			(List.map
			   (fun var -> (Pair(var, (Pair((Bool false), Nil)))))
			   params_set)
			Nil in
  let assignments = List.map2
		      (fun var expr ->
		       (Pair((Symbol("set!")),
			     (Pair(var, (Pair(expr, Nil)))))))
		      params args in
  let body = List.fold_right
	       (fun a s -> Pair(a, s))
	       assignments
	       sexprs in
  (Pair((Symbol("let")), (Pair(place_holders, body))));;

let expand_letrec ribs sexprs =
  let ribs = scheme_list_to_ocaml_list ribs in
  let params = List.map (function
			  | (Pair(name, (Pair(expr, Nil)))) -> name
			  | _ -> raise X_this_should_not_happen) ribs in
  let args = List.map
	       (function
		 | (Pair(name, (Pair(expr, Nil)))) -> expr
		 | _ -> raise X_this_should_not_happen) ribs in
  let ribs = List.map
	       (function
		 | (Pair(name, (Pair(expr, Nil)))) ->
		    (Pair(name, (Pair(Bool false, Nil))))
		 | _ -> raise X_this_should_not_happen)
	       ribs in
  let body = List.fold_right
	       (fun a s -> Pair(a, s))
	       (List.map2
		  (fun var expr ->
		   (Pair((Symbol("set!")),
			 (Pair(var, (Pair(expr, Nil)))))))
		  params args)
	       sexprs in
  let ribs = List.fold_right
	       (fun a s -> Pair(a, s))
	       ribs
	       Nil in
  (Pair((Symbol("let")), (Pair(ribs, body))));;

exception X_unquote_splicing_here_makes_no_sense;;

let rec expand_qq sexpr = match sexpr with
  | (Pair((Symbol("unquote")), (Pair(sexpr, Nil)))) -> sexpr
  | (Pair((Symbol("unquote-splicing")), (Pair(sexpr, Nil)))) ->
     raise X_unquote_splicing_here_makes_no_sense
  | (Pair(a, b)) ->
     (match (a, b) with
      | ((Pair((Symbol("unquote-splicing")), (Pair(a, Nil)))), b) ->
	 let b = expand_qq b in
	 (Pair((Symbol("append")),
	       (Pair(a, (Pair(b, Nil))))))
      | (a, (Pair((Symbol("unquote-splicing")), (Pair(b, Nil))))) ->
	 let a = expand_qq a in
	 (Pair((Symbol("cons")), (Pair(a, (Pair(b, Nil))))))
      | (a, b) ->
	 let a = expand_qq a in
	 let b = expand_qq b in
	 (Pair((Symbol("cons")), (Pair(a, (Pair(b, Nil)))))))
  | (Vector(sexprs)) ->
     let s = expand_qq (List.fold_right (fun a b -> Pair(a, b)) sexprs Nil) in
     (Pair((Symbol("list->vector")), (Pair(s, Nil))))
  | Nil | Symbol _ -> (Pair((Symbol("quote")), (Pair(sexpr, Nil))))
  | expr -> expr;;



let rec tag_parse_rec sexpr =
  match sexpr with
  |Bool _ | Char _ | Number _ | String _ |Nil |Void  -> Const sexpr
  |Pair (Symbol "if", Pair (alt1, Pair (alt2,Nil) ))-> 
    If (tag_parse_rec alt1, tag_parse_rec alt2 ,tag_parse_rec Void)
  |Pair (Symbol "if", Pair (alt1,Nil))->
    tag_parse_rec (Pair (Symbol "if" , Pair (alt1,Pair (Void,Nil))))
 (*) |Pair (Symbol "cond", cont) *)
  | _ -> raise X_syntax_error




let tag_parse sexpr = tag_parse_rec sexpr;;


(*)
type expr =
  | Const of sexpr
  | Var of string
  | VarFree of string
  | VarParam of string * int
  | VarBound of string * int * int
  | If of expr * expr * expr
  | Seq of expr list
  | Set of expr * expr
  | Def of expr * expr
  | Or of expr list
  | LambdaSimple of string list * expr
  | LambdaOpt of string list * string * expr
  | Applic of expr * (expr list)
  | ApplicTP of expr * (expr list);;
*)




let read_expression string = tag_parse (Parser.read_sexpr string);;

let read_expressions string = List.map tag_parse (Parser.read_sexprs string);;

let expression_to_string expr = raise X_not_yet_implemented;;
  
end;; (* struct Tag_Parser *)

let test_parser string =
  let expr = Tag_Parser.read_expression string in
  let string' = (Tag_Parser.expression_to_string expr) in
  Printf.printf "%s\n" string';;
