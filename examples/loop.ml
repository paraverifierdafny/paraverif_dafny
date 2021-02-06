open Core.Std
open Utils
open Paramecium
open Loach
open Formula
open InvFinder
open Cmdline
let types = [
    enum "val" (int_consts [1;2;3;4;5;6;7;8;9;10;11;12;13;14;15;16;17;18;19;20;21;22;23;24;25;26;27;28]);
]
let vardefs = List.concat [ 
    [arrdef [("c", [])] "val"];
    [arrdef [("n", [])] "val"];
    [arrdef [("k", [])] "val"];
    [arrdef [("m", [])] "val"];
    [arrdef [("N", [])] "val"];
]
let init = Parallel [assign  (global "c") (Const (intc 0));assign (global "n") (Const (intc 0));assign (global "k") (Const (intc 1));assign (global "m") (Const (intc 6));assign (global "m") (Const (intc 15))]

let n1 = 
    let name = "n1" in 
    let params = [] in 
    let formula= (uif "<" [var (global "c");var (global "N")]) in
    let statement = (parallel [assign (global "c") (uif "+" [Var (global "c");Var (global "k")]);assign (global "k") (uif "+" [ Var (global "k");Var (global "m")]);assign (global "m") (uif "+" [Var (global "c");Const (intc 6)]);assign (global "n") (uif "+" [Var (global "n");Var (global "1")])]);
    rule name params formula statement

let rules = [n1]

let invariant = 
    let name = "invariant" in
    let params = [] in 
    let formula = (andList [uip "<=" [var (global "c");var (global "N")];
    eqn (var (global "c")) (uif "*" [uif "*" [var (global "n");var (global "n")];var (global "n")]);
    eqn (var (global "k")) (uif "+" [uif "+" [uif "*" [(uif "*" [Const (intc 3);var (global "n")]);var (global "n")];(uif "*" [Const (intc 3);var (global "n")])];Const (intc 1)]);
    eqn (var (global "m")) (uif "+" [uif "*" [Const (intc 6);var(global "n")];Const (intc 6)])]) in
    prop name params formula

let properties = [invariant]

let protocol = {
    name = "n_cube"
    types;
    vardes;
    init;
    rules;
    properties;
}
let () = run_with_cmdline (fun () ->
  let protocol = preprocess_rule_guard ~loach:protocol in
  let cinvs_with_varnames, relations = find  protocol in
  Isabelle.protocol_act protocol cinvs_with_varnames relations ()
)
