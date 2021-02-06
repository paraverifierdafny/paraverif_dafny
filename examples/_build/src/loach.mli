(** Language for cache coherence protocols
*)

(*------------------------------ Types ---------------------------------*)

open Paramecium
open Core.Std

(** Unexhausted instantiation
    This exception should never be raised. Once raised, There should be a bug in this tool.
*)
exception Unexhausted_inst

(** Global variable *)
val global : string -> var

(** Record definition *)
val record_def : string -> paramdef list-> vardef list -> vardef list

(** Record *)
val record : var list -> var

type exp =
  | Const of const
  | Var of var
  | Param of paramref
  | Ite of formula * exp * exp
  | UIF of string * exp list
and formula =
  | Chaos
  | Miracle
  | UIP of string * exp list
  | Eqn of exp * exp
  | Neg of formula
  | AndList of formula list
  | OrList of formula list
  | Imply of formula * formula
  | ForallFormula of paramdef list * formula
  | ExistFormula of paramdef list * formula
with sexp

val const : const -> exp
val var : var -> exp
val param : paramref -> exp
val ite : formula -> exp -> exp -> exp
val uif : string -> exp list -> exp

val chaos : formula
val miracle : formula
val uip : string -> exp list -> formula
val eqn : exp -> exp -> formula
val neg : formula -> formula
val andList : formula list -> formula
val orList : formula list -> formula
val imply : formula -> formula -> formula

(** Forall formula *)
val forallFormula : paramdef list -> formula -> formula

(** Exist formula *)
val existFormula : paramdef list -> formula -> formula

(** Assignment statements *)
type statement =
  | Assign of var * exp
  | Parallel of statement list
  | IfStatement of formula * statement
  | IfelseStatement of formula * statement * statement
  | ForStatement of statement * paramdef list
with sexp

val assign : var -> exp -> statement
val parallel : statement list -> statement
val ifStatement : formula -> statement -> statement
val ifelseStatement : formula -> statement -> statement -> statement
val forStatement : statement -> paramdef list -> statement

val write : vardef -> exp -> exp -> typedef list -> statement
val read : vardef -> exp -> typedef list -> exp

type prop =
  | Prop of string * paramdef list * formula
with sexp

val prop : string -> paramdef list -> formula -> prop

type rule = 
  | Rule of string * paramdef list * formula * statement
with sexp

val rule : string -> paramdef list -> formula -> statement -> rule

(** Represents the whole protocol *)
type protocol = {
  name: string;
  types: typedef list;
  vardefs: vardef list;
  init: statement;
  rules: rule list;
  properties: prop list;
}
with sexp

(*----------------------------- Exceptions ----------------------------------*)

(*----------------------------- Functions ----------------------------------*)
(*\beta substitution *)
val apply_exp : exp -> p:Paramecium.paramref list -> exp
val apply_form : formula -> p:Paramecium.paramref list -> formula
val apply_statement : statement -> p:Paramecium.paramref list -> types:Paramecium.typedef list -> 
      statement
val eliminate_for : statement -> types:Paramecium.typedef list -> statement
val apply_rule : rule -> p:Paramecium.paramref list -> types:Paramecium.typedef list -> rule
val rule_to_insts : rule -> types:Paramecium.typedef list -> rule list
val analyze_if : statement -> formula -> types:Paramecium.typedef list -> 
      (Paramecium.var * (formula * exp) list) list


val balance_ifstatement : statement -> statement list
val eliminate_ifelse : statement -> statement

val preprocess_rule_guard : loach:protocol -> protocol

module VarNamesWithParam :sig
	val of_statement: types:Paramecium.typedef list -> statement-> String.Set.t
	val of_statement_left: types:Paramecium.typedef list -> statement-> String.Set.t
	val of_form: types:Paramecium.typedef list -> formula-> String.Set.t
	val of_var_ref:  (var ->String.Set.t) ref

end

(*----------------------------- Translate module ---------------------------------*)

(** Translate language of this level to the next lower level *)
module Trans : sig

  exception Unexhausted_flatten

  (** Translate language of Loach to Paramecium

      @param loach cache coherence protocol written in Loach
      @return the protocol in Paramecium
  *)
  val act : loach:protocol -> Paramecium.protocol
  val trans_formula:    types:Paramecium.typedef list ->  formula -> Paramecium.formula
  val trans_statement:    types:Paramecium.typedef list ->  statement -> Paramecium.statement
  val invTrans_formula:  Paramecium.formula->formula
end


module ToSmv : sig
  val protocol_act : ?limit_param:bool -> protocol -> string
end



module PartParam : sig
  val apply_protocol : string list -> protocol -> protocol
end

module CMP: sig
	val cmpStrengthRule : formula list -> types:Paramecium.typedef list -> Paramecium.paramref -> rule -> rule 
end	
