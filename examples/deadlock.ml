(* This program is translated from its corresponding murphi version *)

open Core.Std
open Utils
open Paramecium
open Loach
open Formula
open InvFinder
open Cmdline

let _I = strc "I"
let _T = strc "T"
let _C = strc "C"
let _E = strc "E"
let _True = boolc true
let _False = boolc false

let types = [
  enum "state" [_I; _T; _C; _E];
  enum "client" (int_consts [1; 2]);
  enum "boolean" [_True; _False];
]



let vardefs = List.concat [
  [arrdef [("n", [paramdef "i0" "client"])] "state"];
  [arrdef [("x", [])] "boolean"]
]

let init = (parallel [(forStatement (assign (arr [("n", [paramref "i"])]) (const _I)) [paramdef "i" "client"]); (assign (global "x") (const (boolc true)))])



let rules = []

let n_deadlock =
  let name = "n_deadlock" in
  let params = [] in
  let formula = (orList [(orList [(orList [(existFormula [paramdef "i" "client"] (eqn (var (arr [("n", [paramref "i"])])) (const _I))); (existFormula [paramdef "i" "client"] (eqn (var (arr [("n", [paramref "i"])])) (const _E)))]); (existFormula [paramdef "i" "client"] (eqn (var (arr [("n", [paramref "i"])])) (const _C)))]); (existFormula [paramdef "i" "client"] (andList [(eqn (var (arr [("n", [paramref "i"])])) (const _T)); (eqn (var (global "x")) (const (boolc true)))]))]) in
  prop name params formula

let properties = [n_deadlock]


let protocol = {
  name = "n_deadlock";
  types;
  vardefs;
  init;
  rules;
  properties;
}

let () = run_with_cmdline (fun () ->
  let protocol = preprocess_rule_guard ~loach:protocol in
  let cinvs_with_varnames, relations = find protocol
    ~murphi:(In_channel.read_all "n_deadlock.m")
  in
  Isabelle.protocol_act protocol cinvs_with_varnames relations ();
  let ()=print_endline(Dafny1.protocol_act' protocol cinvs_with_varnames relations) in
()
)

