
open Ast
open Format

(* Exception levée pour signaler une erreur pendant l'interprétation *)
exception Error of string
let error s = raise (Error s)

(* Les valeurs de Mini-Python

   - une différence notable avec Python : on
     utilise ici le type int alors que les entiers de Python sont de
     précision arbitraire ; on pourrait utiliser le module Big_int d'OCaml
     mais on choisit la facilité
   - ce que Python appelle une liste est en réalité un tableau
     redimensionnable ; dans le fragment considéré ici, il n'y a pas
     de possibilité d'en modifier la longueur, donc un simple tableau OCaml
     convient *)
type value =
  | Vnone
  | Vbool of bool
  | Vint of int
  | Vstring of string
  | Vlist of value array

(* Affichage d'une valeur sur la sortie standard *)
let rec print_value = function
  | Vnone -> printf "None"
  | Vbool true -> printf "True"
  | Vbool false -> printf "False"
  | Vint n -> printf "%d" n
  | Vstring s -> printf "%s" s
  | Vlist a ->
    let n = Array.length a in
    printf "[";
    for i = 0 to n-1 do print_value a.(i); if i < n-1 then printf ", " done;
    printf "]"

(* Interprétation booléenne d'une valeur

   En Python, toute valeur peut être utilisée comme un booléen : None,
   la liste vide, la chaîne vide et l'entier 0 sont considérés comme
   False et toute autre valeurs comme True *)

let is_false = function
    | Vnone | Vbool false | Vint 0 | Vstring "" -> true
    | Vlist l when (Array.length l == 0) -> true
    | _ -> false

let is_true v =
    not (is_false v)

(* Les fonctions sont ici uniquement globales *)

let functions = (Hashtbl.create 16 : (string, ident list * stmt) Hashtbl.t)

(* L'instruction 'return' de Python est interprétée à l'aide d'une exception *)

exception Return of value

(* Les variables locales (paramètres de fonctions et variables introduites
   par des affectations) sont stockées dans une table de hachage passée en
   arguments aux fonctions suivantes sous le nom 'ctx' *)

type ctx = (string, value) Hashtbl.t

(* Interprétation d'une expression (renvoie une valeur) *)

let rec expr (ctx: ctx) = function
  | Ecst Cnone ->
      Vnone
  | Ecst (Cstring s) ->
      Vstring s
  (* arithmétique *)
  | Ecst (Cint n) ->
      Vint n
  | Ebinop (Badd | Bsub | Bmul | Bdiv | Bmod |
            Beq | Bneq | Blt | Ble | Bgt | Bge as op, e1, e2) ->
      let v1 = expr ctx e1 in
      let v2 = expr ctx e2 in
      begin match op, v1, v2 with
        | Badd, Vint n1, Vint n2 ->
            Vint (n1 + n2)
        | Bsub, Vint n1, Vint n2 ->
            Vint (n1 - n2)
        | Bmul, Vint n1, Vint n2 ->
            Vint (n1 * n2)
        | Bdiv, Vint n1, Vint n2 ->
            if n2 != 0 then
                Vint (n1 / n2)
            else
                error "Division by zero"
        | Bmod, Vint n1, Vint n2 ->
            if n2 != 0 then
                Vint (n1 mod n2)
            else
                error "Modulo operation by zero"
        | Beq, _, _  ->
            Vbool (v1 == v2)
        | Bneq, _, _ ->
            Vbool (v1 != v2)
        | Blt, _, _  ->
            Vbool (v1 < v2)
        | Ble, _, _  ->
            Vbool (v1 <= v2)
        | Bgt, _, _  ->
            Vbool (v1 > v2)
        | Bge, _, _  ->
            Vbool (v1 >= v2)
        | Badd, Vstring s1, Vstring s2 ->
            Vstring (s1 ^ s2)
        | Badd, Vlist l1, Vlist l2 ->
            assert false (* à compléter (question 5) *)
        | _ -> error "unsupported operand types"
      end
  | Eunop (Uneg, e1) ->
        let v1 = expr ctx e1 in
        begin match v1 with
        | Vint n ->
            Vint (-n)
        | _ -> error "Invalid operation Uneg"
        end
  (* booléens *)
  | Ecst (Cbool b) ->
      Vbool b
  | Ebinop (Band, e1, e2) ->
      Vbool (is_true (expr ctx e1) && is_true (expr ctx e2))
  | Ebinop (Bor, e1, e2) ->
      Vbool (is_true (expr ctx e1) || is_true (expr ctx e2))
  | Eunop (Unot, e1) ->
      let v1 = expr ctx e1 in
      Vbool (is_false v1)
  | Eident id ->
      if Hashtbl.mem ctx id then
        Hashtbl.find ctx id
      else
        error ("Variable " ^ id ^ " was not declared before.")
      (* appel de fonction *)
  | Ecall ("len", [e1]) ->
      assert false (* à compléter (question 5) *)
  | Ecall ("list", [Ecall ("range", [e1])]) ->
      assert false (* à compléter (question 5) *)
  | Ecall ((f: ident), (el: expr list)) ->
      if Hashtbl.mem functions f then
        let (id_list, body) = Hashtbl.find functions f in
        let ctx_fun = Hashtbl.copy ctx in
        if (List.length id_list) == (List.length el) then
            let assign_argument id e =
                let v = expr ctx_fun e in
                Hashtbl.add ctx_fun id v
            in
            List.iter2 assign_argument id_list el;
            begin try
                stmt ctx_fun body;
                Vnone
            with
                Return v -> v
            end
        else
            error ("Invalid arguments in function " ^ f ^ ".")
      else
        error ("Function " ^ f ^ " was not defined before.")
  | Elist el ->
      assert false (* à compléter (question 5) *)
  | Eget (e1, e2) ->
      assert false (* à compléter (question 5) *)

(* interprétation d'une instruction ; ne renvoie rien *)

and stmt (ctx: ctx) = function
  | Seval e ->
      ignore (expr ctx e)
  | Sprint e ->
      print_value (expr ctx e); printf "@."
  | Sblock bl ->
      block ctx bl
  | Sif (e, s1, s2) ->
      let v = expr ctx e in
      if is_true v then
        stmt ctx s1
      else
        stmt ctx s2
  | Sassign (id, e) ->
      let v = expr ctx e in
      Hashtbl.add ctx id v
  | Sreturn e ->
      raise (Return (expr ctx e))
  | Sfor (x, e, s) ->
      assert false (* à compléter (question 5) *)
  | Sset (e1, e2, e3) ->
      assert false (* à compléter (question 5) *)

(* interprétation d'un bloc i.e. d'une séquence d'instructions *)

and block ctx = function
  | [] -> ()
  | s :: sl -> stmt ctx s; block ctx sl

(* interprétation d'un fichier
   - dl est une liste de définitions de fonction (cf Ast.def)
   - s est une instruction, qui représente les instructions globales
 *)

let def_fun (id, id_list, s) =
    Hashtbl.add functions id (id_list, s)

let file (dl, s) =
  (* à compléter (question 4) *)
  List.iter def_fun dl;
  stmt (Hashtbl.create 16) s



