(* Parse OCaml syntax: comments and strings cannot trigger these checks. *)
open Parsetree
open Ast_iterator
let failed = ref false
let problem file loc message =
  failed := true;
  Printf.eprintf "%s:%d: %s\n" file loc.Location.loc_start.Lexing.pos_lnum message
let rec parts = function
  | Longident.Lident s -> [s]
  | Longident.Ldot (p,s) -> parts p @ [s]
  | Longident.Lapply (a,b) -> parts a @ parts b
let native t = match parts t with ["int"] | ["Stdlib";"int"] | ["Pervasives";"int"] | ["Int";"t"] | ["Stdlib";"Int";"t"] | ["Pervasives";"Int";"t"] -> true | _ -> false
let legacy t = match parts t with "Orchestration"::_ -> true | _ -> false
let inspect mode file =
  let ch = open_in file in
  let lex = Lexing.from_channel ch in Location.init lex file;
  let iter = { default_iterator with
    typ=(fun self t ->
      (match t.ptyp_desc with Ptyp_constr (id,_) ->
        if mode="interface" && native id.txt then problem file t.ptyp_loc "prohibited native integer in extracted interface";
        if mode="wrapper" && legacy id.txt then problem file t.ptyp_loc "historical Orchestration dependency"
      | _ -> ()); default_iterator.typ self t);
    expr=(fun self e -> (match e.pexp_desc with Pexp_ident id when mode="wrapper" && legacy id.txt -> problem file e.pexp_loc "historical Orchestration dependency" | _ -> ());default_iterator.expr self e);
    module_expr=(fun self m -> (match m.pmod_desc with Pmod_ident id when mode="wrapper" && legacy id.txt -> problem file m.pmod_loc "historical Orchestration dependency" | _ -> ());default_iterator.module_expr self m);
    module_type=(fun self m -> (match m.pmty_desc with Pmty_ident id | Pmty_alias id when mode="wrapper" && legacy id.txt -> problem file m.pmty_loc "historical Orchestration dependency" | _ -> ());default_iterator.module_type self m) }
  in
  (try if mode="interface" then iter.signature iter (Parse.interface lex)
   else if mode="wrapper" then iter.structure iter (Parse.implementation lex)
   else failwith "unknown inspection mode"
   with exn -> close_in_noerr ch; raise exn);
  close_in ch
let () =
  try
    if Array.length Sys.argv < 3 || Array.length Sys.argv mod 2 <> 1 then failwith "expected MODE FILE pairs";
    for i=0 to (Array.length Sys.argv-3)/2 do inspect Sys.argv.(1+2*i) Sys.argv.(2+2*i) done;
    if !failed then exit 1
  with exn -> Location.report_exception Format.err_formatter exn; exit 1
