open Core.Std
open Utils
open Paramecium
open Loach
open Formula
open InvFinder
open Cmdline 
 let types = [
    enum "val" (int_consts [1;2;3;4;5;6;7;8;9;10;11;12;13;14;15;16;17;18;19;20;21;22;23;24;25;26;27;28;29;30;31;32;33;34;35;36;37;38;39;40;41;42;43;44;45;46;47;48;49;50;51;52;53;54;55;56;57;58;59;60;61;62;63;64;65;66;67;68;69;70;71;72;73;74;75;76;77;78;79;80;81;82;83;84;85;86;87;88;89;90;91;92;93;94;95;96;97;98;99
]);
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
    let formula= (uip "<" [var (global "c");var (global "N")]) in
    let statement = (parallel [
    assign (global "c") (uif "+" [var (global "c");var (global "k")]);
    assign (global "k") (uif "+" [var (global "k");var (global "m")]);
    assign (global "m") (uif "+" [var (global "c");Const (intc 6)]);
    assign (global "n") (uif "+" [var (global "n");var (global "1")])
    ]) in
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
    name = "n_cube";
    types;
    vardefs;
    init;
    rules;
    properties;
} 

let () = run_with_cmdline (fun () ->
  let protocol = preprocess_rule_guard ~loach:protocol in
  let cinvs_with_varnames, relations = find protocol in
  Isabelle.protocol_act protocol cinvs_with_varnames relations ()
)