{
open Core.Std
open Lexing
open SmtRetparser

exception SyntaxError of string

let next_line lexbuf =
  let pos = lexbuf.lex_curr_p in
  lexbuf.lex_curr_p <-
    { pos with pos_bol = lexbuf.lex_curr_pos;
               pos_lnum = pos.pos_lnum + 1
    }
}

(* part 1 *)
let int = '-'? ['0'-'9'] ['0'-'9']*

(* part 2 *)
let digit =['0'-'9']
let integer=digit+ 
let frac = '.' digit*
let exp = ['e' 'E'] ['-' '+']? digit+
let float = digit* frac? exp?

(* part 3 *)
let white = [' ' '\t']+
let newline = '\r' | '\n' | "\r\n"
let id = ['a'-'z' 'A'-'Z' '_'] ['a'-'z' 'A'-'Z' '0'-'9' '_' '!' '.']*
let str = "'" id "'"

(* part 4 
ule read =
  parse
  | white    { read lexbuf }
  | newline  { next_line lexbuf; read lexbuf }
  | intger   { INT (int_of_string (Lexing.lexeme lexbuf)) }
  | "!"		   { return( NOT ); }
  | "!="		 { return(NEQ); }  
  | "->"		 { return( IMPLIES ); }
  | '&'      {return（AND）;} 
  | '='      {return（EQ）;}
  | '('      {return（LEFTBRACE）;}
  | ')'      {return（RIGHTBRACE）;}
  | '['      {return（ LEFTMIDBRACK); }
  | ']'      {return（ RIGHTMIDBRACK); }
  | '.'       {return (DOT)}
  | ','       {return (COLON)}
  | ';'       {return (SEMICOLON)}
  | ':'       {return (COMMA)}
  | eof      { EOF }
*)
rule read =
  parse
  | white    { read lexbuf  }
  | newline  { next_line lexbuf; read lexbuf }
  | '"'      { read_string (Buffer.create 17) lexbuf }
	| "="      {EQ}
  | '('      { LEFT_BRACE }
  | ')'      { RIGHT_BRACE } 
  | '['      { LEFT_MIDBRACE}
  | ']'      { RIGHT_MIDBRACE} 
  | ','      { COMMA } 
  | "->"     { SENDTO}   
	|"else"    {ELSE}
  | id {  ID(Lexing.lexeme lexbuf) }	
  | integer   {  INTEGER(Lexing.lexeme lexbuf) }
  | eof      { EOF }

(* part 5 
and read_string buf =
  parse
  | '"'       { STRING (Buffer.contents buf) }
  | '\\' '/'  { Buffer.add_char buf '/'; read_string buf lexbuf }
  | '\\' '\\' { Buffer.add_char buf '\\'; read_string buf lexbuf }
  | '\\' 'b'  { Buffer.add_char buf '\b'; read_string buf lexbuf }
  | '\\' 'f'  { Buffer.add_char buf '\012'; read_string buf lexbuf }
  | '\\' 'n'  { Buffer.add_char buf '\n'; read_string buf lexbuf }
  | '\\' 'r'  { Buffer.add_char buf '\r'; read_string buf lexbuf }
  | '\\' 't'  { Buffer.add_char buf '\t'; read_string buf lexbuf }
  | [^ '"' '\\']+
    { Buffer.add_string buf (Lexing.lexeme lexbuf);
      read_string buf lexbuf
    }
  | _ { raise (SyntaxError ("Illegal string character: " ^ Lexing.lexeme lexbuf)) }
  | eof { raise (SyntaxError ("String is not terminated")) }*)

and read_string buf =
  parse 
  | '\\' '/'  { Buffer.add_char buf '/'; read_string buf lexbuf }
  | '\\' '\\' { Buffer.add_char buf '\\'; read_string buf lexbuf }
  | '\\' 'b'  { Buffer.add_char buf '\b'; read_string buf lexbuf }
  | '\\' 'f'  { Buffer.add_char buf '\012'; read_string buf lexbuf }
  | '\\' 'n'  { Buffer.add_char buf '\n'; read_string buf lexbuf }
  | '\\' 'r'  { Buffer.add_char buf '\r'; read_string buf lexbuf }
  | '\\' 't'  { Buffer.add_char buf '\t'; read_string buf lexbuf }
  | [^ '"' '\\']+
    { Buffer.add_string buf (Lexing.lexeme lexbuf);
      read_string buf lexbuf
    }
  | _ { raise (SyntaxError ("Illegal string character: " ^ Lexing.lexeme lexbuf)) }
  | eof { raise (SyntaxError ("String is not terminated")) }
