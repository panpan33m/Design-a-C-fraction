(*  COMP 321 Homework 3:  Lexer and parser for a fragment of C.
*
*   ml-ulex specification.
*   
*   N. Danner
*   Fall 2016
*)

%name CPPLexer ;

(*  Using - for negation is a challenge in the lexer (why?)  So take
*   SML's "solution," and use ~ for negative numbers.
*)
%let digit = [0-9] ;
%let intnum = "~"?{digit}+ ;
%let dblnum = "~"?{digit}+\.{digit}+(e{intnum})? ;
%let alpha = [a-zA-Z] ;
%let id = {alpha}({alpha} | {digit} | _)* ;
%let ws = [\n\t\ ] ;
%let eolcomment = "//"[^\n]*\n ;
%let blockcomment = "/*" ~(.*"*/".*) "*/" ;
%let cppdirective = "#"[^\n]*\n ;
%let any = . ;
%let dquote_str = \"([^"] | "\\\"")*\" ;

%defs (
  structure T = CPPGrmTokens
  type lex_result = T.token
  fun eof() = T.EOF
  exception lex_error of string

  fun trimFirstLast (s : string) : string =
    String.substring(s, 1, String.size s - 2)

) ;


"!"       => ( T.BANG ) ;
"!="      => ( T.NE ) ;
"%"       => ( T.MOD ) ;
"&&"      => ( T.AND ) ;
"("       => ( T.LP ) ;
")"       => ( T.RP ) ;
"*"       => ( T.TIMES ) ;
"+"       => ( T.PLUS ) ;
"++"      => ( T.INCR ) ;
(*
"+="      => ( T.INCASSN ) ;
*)
","       => ( T.SEP ) ;
"-"       => ( T.MINUS ) ;
"--"      => ( T.DECR ) ;
"/"       => ( T.DIV ) ;
":"       => ( T.COLON ) ;
";"       => ( T.TERM ) ;
"<"       => ( T.LT ) ;
"<="      => ( T.LE ) ;
"="       => ( T.ASSN ) ;
"=="      => ( T.EQ ) ;
">"       => ( T.GT ) ;
">="      => ( T.GE ) ;
"?"       => ( T.QUESTION ) ;
"["       => ( T.LBRACK ) ;
"]"       => ( T.RBRACK ) ;
"{"       => ( T.LB ) ;
"||"      => ( T.OR ) ;
"}"       => ( T.RB ) ;

"bool"    => ( T.TBOOL ) ;
"do"      => ( T.DO ) ;
"double"  => ( T.TDBL ) ;
"else"    => ( T.ELSE ) ;
"false"   => ( T.FALSE ) ;
"for"     => ( T.FOR ) ;
"if"      => ( T.IF ) ;
"int"     => ( T.TINT ) ;
"return"  => ( T.RETURN ) ;
"string"  => ( T.TSTRING ) ;
"true"    => ( T.TRUE ) ;
"void"    => ( T.TVOID ) ;
"while"   => ( T.WHILE ) ;

{blockcomment}  => ( skip() ) ;
{cppdirective} => ( skip() ) ;
{dblnum}  => ( T.DBL (valOf (Real.fromString yytext)) ) ;
{dquote_str}  => ( T.STR (trimFirstLast yytext) ) ;
{eolcomment}  => ( skip() ) ;
{id}      => ( T.ID yytext ) ;
{intnum}  => ( T.INT (valOf (Int.fromString yytext))  ) ;
{ws}      => ( skip() ) ;

{any}     => ( raise Fail ("Unexpected char: " ^ yytext) ) ;

