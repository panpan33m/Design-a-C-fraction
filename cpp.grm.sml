structure 
CPPGrmTokens = struct

    datatype token = EOF
      | ELSE
      | IF
      | FOR
      | WHILE
      | DO
      | RETURN
      | BANG
      | DECR
      | INCR
      | DIV
      | MOD
      | TIMES
      | MINUS
      | PLUS
      | LE
      | GE
      | LT
      | GT
      | NE
      | EQ
      | AND
      | OR
      | ASSN
      | COLON
      | QUESTION
      | TERM
      | SEP
      | RBRACK
      | LBRACK
      | RB
      | LB
      | RP
      | LP
      | FALSE
      | TRUE
      | STR of string
      | DBL of real
      | INT of int
      | ID of Ast.id
      | TVOID
      | TSTRING
      | TBOOL
      | TDBL
      | TINT

    val allToks = [EOF, ELSE, IF, FOR, WHILE, DO, RETURN, BANG, DECR, INCR, DIV, MOD, TIMES, MINUS, PLUS, LE, GE, LT, GT, NE, EQ, AND, OR, ASSN, COLON, QUESTION, TERM, SEP, RBRACK, LBRACK, RB, LB, RP, LP, FALSE, TRUE, TVOID, TSTRING, TBOOL, TDBL, TINT]

    fun toString tok =
(case (tok)
 of (EOF) => "EOF"
  | (ELSE) => "ELSE"
  | (IF) => "IF"
  | (FOR) => "FOR"
  | (WHILE) => "WHILE"
  | (DO) => "DO"
  | (RETURN) => "RETURN"
  | (BANG) => "BANG"
  | (DECR) => "DECR"
  | (INCR) => "INCR"
  | (DIV) => "DIV"
  | (MOD) => "MOD"
  | (TIMES) => "TIMES"
  | (MINUS) => "MINUS"
  | (PLUS) => "PLUS"
  | (LE) => "LE"
  | (GE) => "GE"
  | (LT) => "LT"
  | (GT) => "GT"
  | (NE) => "NE"
  | (EQ) => "EQ"
  | (AND) => "AND"
  | (OR) => "OR"
  | (ASSN) => "ASSN"
  | (COLON) => "COLON"
  | (QUESTION) => "QUESTION"
  | (TERM) => "TERM"
  | (SEP) => "SEP"
  | (RBRACK) => "RBRACK"
  | (LBRACK) => "LBRACK"
  | (RB) => "RB"
  | (LB) => "LB"
  | (RP) => "RP"
  | (LP) => "LP"
  | (FALSE) => "FALSE"
  | (TRUE) => "TRUE"
  | (STR(_)) => "STR"
  | (DBL(_)) => "DBL"
  | (INT(_)) => "INT"
  | (ID(_)) => "ID"
  | (TVOID) => "TVOID"
  | (TSTRING) => "TSTRING"
  | (TBOOL) => "TBOOL"
  | (TDBL) => "TDBL"
  | (TINT) => "TINT"
(* end case *))
    fun isKW tok =
(case (tok)
 of (EOF) => false
  | (ELSE) => false
  | (IF) => false
  | (FOR) => false
  | (WHILE) => false
  | (DO) => false
  | (RETURN) => false
  | (BANG) => false
  | (DECR) => false
  | (INCR) => false
  | (DIV) => false
  | (MOD) => false
  | (TIMES) => false
  | (MINUS) => false
  | (PLUS) => false
  | (LE) => false
  | (GE) => false
  | (LT) => false
  | (GT) => false
  | (NE) => false
  | (EQ) => false
  | (AND) => false
  | (OR) => false
  | (ASSN) => false
  | (COLON) => false
  | (QUESTION) => false
  | (TERM) => false
  | (SEP) => false
  | (RBRACK) => false
  | (LBRACK) => false
  | (RB) => false
  | (LB) => false
  | (RP) => false
  | (LP) => false
  | (FALSE) => false
  | (TRUE) => false
  | (STR(_)) => false
  | (DBL(_)) => false
  | (INT(_)) => false
  | (ID(_)) => false
  | (TVOID) => false
  | (TSTRING) => false
  | (TBOOL) => false
  | (TDBL) => false
  | (TINT) => false
(* end case *))

  fun isEOF EOF = true
    | isEOF _ = false

end

functor CPPGrmParseFn(Lex : ANTLR_LEXER) = struct

  local
    structure Tok = 
CPPGrmTokens
    structure UserCode =
      struct

  open Ast

  datatype RatorsAndRands = Un of (exp -> exp)
                          | Bin of (exp*exp-> exp)*exp
                          | BinList of (exp*(exp list) -> exp)*(exp list)
                          | Tern of (exp*exp*exp -> exp)*exp*exp

  fun leftAssoc e randrs =
    case randrs of
         [] => e
       | Un(rator) :: randrs => leftAssoc (rator e) randrs
       | Bin(rator, e') :: randrs => leftAssoc (rator(e, e')) randrs
       | BinList(rator, es') :: randrs => leftAssoc (rator(e, es')) randrs

  fun rightAssoc e randrs =
    case randrs of
         [] => e
       | Un(rator) :: randrs => rator (rightAssoc e randrs)
       | Bin(rator, e') :: randrs => rator (e, rightAssoc e' randrs)
       | Tern(rator, e0, e1) :: randrs => rator(e, e0, rightAssoc e1 randrs)

fun pgm_PROD_1_ACT (EOF, defn, EOF_SPAN : (Lex.pos * Lex.pos), defn_SPAN : (Lex.pos * Lex.pos), FULL_SPAN : (Lex.pos * Lex.pos)) = 
  (PDefs defn)
fun defn_PROD_1_SUBRULE_1_PROD_1_ACT (ID, LB, LP, RB, RP, stm, typ, ID_SPAN : (Lex.pos * Lex.pos), LB_SPAN : (Lex.pos * Lex.pos), LP_SPAN : (Lex.pos * Lex.pos), RB_SPAN : (Lex.pos * Lex.pos), RP_SPAN : (Lex.pos * Lex.pos), stm_SPAN : (Lex.pos * Lex.pos), typ_SPAN : (Lex.pos * Lex.pos), FULL_SPAN : (Lex.pos * Lex.pos)) = 
  (DFun(typ, ID, [], stm))
fun defn_PROD_1_SUBRULE_1_PROD_2_ACT (ID, LP, RP, typ, TERM, ID_SPAN : (Lex.pos * Lex.pos), LP_SPAN : (Lex.pos * Lex.pos), RP_SPAN : (Lex.pos * Lex.pos), typ_SPAN : (Lex.pos * Lex.pos), TERM_SPAN : (Lex.pos * Lex.pos), FULL_SPAN : (Lex.pos * Lex.pos)) = 
  (DFunProt(typ, ID, []))
fun defn_PROD_1_SUBRULE_1_PROD_3_SUBRULE_1_PROD_1_ACT (ID, LB, RB, stm, typ, paramlist, ID_SPAN : (Lex.pos * Lex.pos), LB_SPAN : (Lex.pos * Lex.pos), RB_SPAN : (Lex.pos * Lex.pos), stm_SPAN : (Lex.pos * Lex.pos), typ_SPAN : (Lex.pos * Lex.pos), paramlist_SPAN : (Lex.pos * Lex.pos), FULL_SPAN : (Lex.pos * Lex.pos)) = 
  (SOME stm)
fun defn_PROD_1_SUBRULE_1_PROD_3_SUBRULE_1_PROD_2_ACT (ID, typ, TERM, paramlist, ID_SPAN : (Lex.pos * Lex.pos), typ_SPAN : (Lex.pos * Lex.pos), TERM_SPAN : (Lex.pos * Lex.pos), paramlist_SPAN : (Lex.pos * Lex.pos), FULL_SPAN : (Lex.pos * Lex.pos)) = 
  (NONE)
fun defn_PROD_1_SUBRULE_1_PROD_3_ACT (ID, SR, typ, paramlist, ID_SPAN : (Lex.pos * Lex.pos), SR_SPAN : (Lex.pos * Lex.pos), typ_SPAN : (Lex.pos * Lex.pos), paramlist_SPAN : (Lex.pos * Lex.pos), FULL_SPAN : (Lex.pos * Lex.pos)) = 
  (case SR of NONE => DFunProt(typ, ID, map #1 paramlist)
                    | SOME stms => DFun(typ, ID, paramlist, stms))
fun defn_PROD_1_SUBRULE_1_PROD_4_ACT (ID, typ, TERM, protolist, ID_SPAN : (Lex.pos * Lex.pos), typ_SPAN : (Lex.pos * Lex.pos), TERM_SPAN : (Lex.pos * Lex.pos), protolist_SPAN : (Lex.pos * Lex.pos), FULL_SPAN : (Lex.pos * Lex.pos)) = 
  (DFunProt(typ, ID, protolist))
fun defn_PROD_1_ACT (ID, SR, typ, ID_SPAN : (Lex.pos * Lex.pos), SR_SPAN : (Lex.pos * Lex.pos), typ_SPAN : (Lex.pos * Lex.pos), FULL_SPAN : (Lex.pos * Lex.pos)) = 
  (SR)
fun paramlist_PROD_1_ACT (ID, LP, RP, SR, typ, ID_SPAN : (Lex.pos * Lex.pos), LP_SPAN : (Lex.pos * Lex.pos), RP_SPAN : (Lex.pos * Lex.pos), SR_SPAN : (Lex.pos * Lex.pos), typ_SPAN : (Lex.pos * Lex.pos), FULL_SPAN : (Lex.pos * Lex.pos)) = 
  ((typ, ID) :: SR)
fun protolist_PROD_1_ACT (LP, RP, SR, typ, LP_SPAN : (Lex.pos * Lex.pos), RP_SPAN : (Lex.pos * Lex.pos), SR_SPAN : (Lex.pos * Lex.pos), typ_SPAN : (Lex.pos * Lex.pos), FULL_SPAN : (Lex.pos * Lex.pos)) = 
  (typ :: SR)
fun stm_PROD_1_SUBRULE_1_PROD_1_SUBRULE_1_PROD_1_ACT (ID, SR, typ, ID_SPAN : (Lex.pos * Lex.pos), SR_SPAN : (Lex.pos * Lex.pos), typ_SPAN : (Lex.pos * Lex.pos), FULL_SPAN : (Lex.pos * Lex.pos)) = 
  (ID :: SR)
fun stm_PROD_1_SUBRULE_1_PROD_1_ACT (SR, typ, SR_SPAN : (Lex.pos * Lex.pos), typ_SPAN : (Lex.pos * Lex.pos), FULL_SPAN : (Lex.pos * Lex.pos)) = 
  (case SR of NONE => [] | SOME ids => ids)
fun stm_PROD_1_ACT (SR, typ, TERM, SR_SPAN : (Lex.pos * Lex.pos), typ_SPAN : (Lex.pos * Lex.pos), TERM_SPAN : (Lex.pos * Lex.pos), FULL_SPAN : (Lex.pos * Lex.pos)) = 
  (SDecl(typ, SR))
fun stm_PROD_2_SUBRULE_1_PROD_1_ACT (ID, SR, exp, typ, ASSN, ID_SPAN : (Lex.pos * Lex.pos), SR_SPAN : (Lex.pos * Lex.pos), exp_SPAN : (Lex.pos * Lex.pos), typ_SPAN : (Lex.pos * Lex.pos), ASSN_SPAN : (Lex.pos * Lex.pos), FULL_SPAN : (Lex.pos * Lex.pos)) = 
  ((ID, exp) :: SR)
fun stm_PROD_2_ACT (SR, typ, TERM, SR_SPAN : (Lex.pos * Lex.pos), typ_SPAN : (Lex.pos * Lex.pos), TERM_SPAN : (Lex.pos * Lex.pos), FULL_SPAN : (Lex.pos * Lex.pos)) = 
  (SInit(typ, SR))
fun stm_PROD_3_ACT (exp, TERM, exp_SPAN : (Lex.pos * Lex.pos), TERM_SPAN : (Lex.pos * Lex.pos), FULL_SPAN : (Lex.pos * Lex.pos)) = 
  (SExp exp)
fun stm_PROD_4_ACT (exp, TERM, RETURN, exp_SPAN : (Lex.pos * Lex.pos), TERM_SPAN : (Lex.pos * Lex.pos), RETURN_SPAN : (Lex.pos * Lex.pos), FULL_SPAN : (Lex.pos * Lex.pos)) = 
  (SReturn(exp))
fun stm_PROD_5_ACT (TERM, RETURN, TERM_SPAN : (Lex.pos * Lex.pos), RETURN_SPAN : (Lex.pos * Lex.pos), FULL_SPAN : (Lex.pos * Lex.pos)) = 
  (SVReturn)
fun stm_PROD_6_ACT (DO, LP, RP, exp, stm, TERM, WHILE, DO_SPAN : (Lex.pos * Lex.pos), LP_SPAN : (Lex.pos * Lex.pos), RP_SPAN : (Lex.pos * Lex.pos), exp_SPAN : (Lex.pos * Lex.pos), stm_SPAN : (Lex.pos * Lex.pos), TERM_SPAN : (Lex.pos * Lex.pos), WHILE_SPAN : (Lex.pos * Lex.pos), FULL_SPAN : (Lex.pos * Lex.pos)) = 
  (SDoWhile(stm, exp))
fun stm_PROD_7_ACT (LP, RP, exp, stm, WHILE, LP_SPAN : (Lex.pos * Lex.pos), RP_SPAN : (Lex.pos * Lex.pos), exp_SPAN : (Lex.pos * Lex.pos), stm_SPAN : (Lex.pos * Lex.pos), WHILE_SPAN : (Lex.pos * Lex.pos), FULL_SPAN : (Lex.pos * Lex.pos)) = 
  (SWhile(exp, stm))
fun stm_PROD_8_ACT (ID, LP, RP, FOR, stm, typ, ASSN, exp1, exp2, exp3, TERM1, TERM2, ID_SPAN : (Lex.pos * Lex.pos), LP_SPAN : (Lex.pos * Lex.pos), RP_SPAN : (Lex.pos * Lex.pos), FOR_SPAN : (Lex.pos * Lex.pos), stm_SPAN : (Lex.pos * Lex.pos), typ_SPAN : (Lex.pos * Lex.pos), ASSN_SPAN : (Lex.pos * Lex.pos), exp1_SPAN : (Lex.pos * Lex.pos), exp2_SPAN : (Lex.pos * Lex.pos), exp3_SPAN : (Lex.pos * Lex.pos), TERM1_SPAN : (Lex.pos * Lex.pos), TERM2_SPAN : (Lex.pos * Lex.pos), FULL_SPAN : (Lex.pos * Lex.pos)) = 
  (SFor((typ, ID, exp1), exp2, exp3, stm))
fun stm_PROD_9_ACT (cond_stm, cond_stm_SPAN : (Lex.pos * Lex.pos), FULL_SPAN : (Lex.pos * Lex.pos)) = 
  (cond_stm)
fun stm_PROD_10_ACT (LB, RB, stm, LB_SPAN : (Lex.pos * Lex.pos), RB_SPAN : (Lex.pos * Lex.pos), stm_SPAN : (Lex.pos * Lex.pos), FULL_SPAN : (Lex.pos * Lex.pos)) = 
  (SBlock stm)
fun cond_stm_PROD_1_SUBRULE_1_PROD_1_ACT (IF, LP, RP, exp, stm, ELSE, IF_SPAN : (Lex.pos * Lex.pos), LP_SPAN : (Lex.pos * Lex.pos), RP_SPAN : (Lex.pos * Lex.pos), exp_SPAN : (Lex.pos * Lex.pos), stm_SPAN : (Lex.pos * Lex.pos), ELSE_SPAN : (Lex.pos * Lex.pos), FULL_SPAN : (Lex.pos * Lex.pos)) = 
  (SOME stm)
fun cond_stm_PROD_1_SUBRULE_1_PROD_2_ACT (IF, LP, RP, exp, stm, IF_SPAN : (Lex.pos * Lex.pos), LP_SPAN : (Lex.pos * Lex.pos), RP_SPAN : (Lex.pos * Lex.pos), exp_SPAN : (Lex.pos * Lex.pos), stm_SPAN : (Lex.pos * Lex.pos), FULL_SPAN : (Lex.pos * Lex.pos)) = 
  (NONE)
fun cond_stm_PROD_1_ACT (IF, LP, RP, SR, exp, stm, IF_SPAN : (Lex.pos * Lex.pos), LP_SPAN : (Lex.pos * Lex.pos), RP_SPAN : (Lex.pos * Lex.pos), SR_SPAN : (Lex.pos * Lex.pos), exp_SPAN : (Lex.pos * Lex.pos), stm_SPAN : (Lex.pos * Lex.pos), FULL_SPAN : (Lex.pos * Lex.pos)) = 
  (case SR of NONE => SIf(exp, stm) | SOME s => SIfElse(exp, stm, s))
fun asst_exp_PROD_1_ACT (ID, ASSN, asst_exp, ID_SPAN : (Lex.pos * Lex.pos), ASSN_SPAN : (Lex.pos * Lex.pos), asst_exp_SPAN : (Lex.pos * Lex.pos), FULL_SPAN : (Lex.pos * Lex.pos)) = 
  (EAsst(ID, asst_exp))
fun cond_exp_PROD_1_SUBRULE_1_PROD_1_ACT (QUESTION, or_exp1, or_exp2, COLON, or_exp, QUESTION_SPAN : (Lex.pos * Lex.pos), or_exp1_SPAN : (Lex.pos * Lex.pos), or_exp2_SPAN : (Lex.pos * Lex.pos), COLON_SPAN : (Lex.pos * Lex.pos), or_exp_SPAN : (Lex.pos * Lex.pos), FULL_SPAN : (Lex.pos * Lex.pos)) = 
  (Tern(ECond, or_exp1, or_exp2))
fun cond_exp_PROD_1_ACT (SR, or_exp, SR_SPAN : (Lex.pos * Lex.pos), or_exp_SPAN : (Lex.pos * Lex.pos), FULL_SPAN : (Lex.pos * Lex.pos)) = 
  (rightAssoc or_exp SR)
fun or_exp_PROD_1_SUBRULE_1_PROD_1_ACT (OR, and_exp, OR_SPAN : (Lex.pos * Lex.pos), and_exp_SPAN : (Lex.pos * Lex.pos), FULL_SPAN : (Lex.pos * Lex.pos)) = 
  (Bin(EOr, and_exp))
fun or_exp_PROD_1_ACT (SR, and_exp, SR_SPAN : (Lex.pos * Lex.pos), and_exp_SPAN : (Lex.pos * Lex.pos), FULL_SPAN : (Lex.pos * Lex.pos)) = 
  (leftAssoc and_exp SR)
fun and_exp_PROD_1_SUBRULE_1_PROD_1_ACT (AND, eq_ne_exp, AND_SPAN : (Lex.pos * Lex.pos), eq_ne_exp_SPAN : (Lex.pos * Lex.pos), FULL_SPAN : (Lex.pos * Lex.pos)) = 
  (Bin(EAnd, eq_ne_exp))
fun and_exp_PROD_1_ACT (SR, eq_ne_exp, SR_SPAN : (Lex.pos * Lex.pos), eq_ne_exp_SPAN : (Lex.pos * Lex.pos), FULL_SPAN : (Lex.pos * Lex.pos)) = 
  (leftAssoc eq_ne_exp SR)
fun eq_ne_exp_PROD_1_SUBRULE_1_PROD_1_SUBRULE_1_PROD_1_ACT (EQ, comp_exp, EQ_SPAN : (Lex.pos * Lex.pos), comp_exp_SPAN : (Lex.pos * Lex.pos), FULL_SPAN : (Lex.pos * Lex.pos)) = 
  (EEq)
fun eq_ne_exp_PROD_1_SUBRULE_1_PROD_1_SUBRULE_1_PROD_2_ACT (NE, comp_exp, NE_SPAN : (Lex.pos * Lex.pos), comp_exp_SPAN : (Lex.pos * Lex.pos), FULL_SPAN : (Lex.pos * Lex.pos)) = 
  (ENeq)
fun eq_ne_exp_PROD_1_SUBRULE_1_PROD_1_ACT (SR, comp_exp, SR_SPAN : (Lex.pos * Lex.pos), comp_exp_SPAN : (Lex.pos * Lex.pos), FULL_SPAN : (Lex.pos * Lex.pos)) = 
  (Bin(SR, comp_exp))
fun eq_ne_exp_PROD_1_ACT (SR, comp_exp, SR_SPAN : (Lex.pos * Lex.pos), comp_exp_SPAN : (Lex.pos * Lex.pos), FULL_SPAN : (Lex.pos * Lex.pos)) = 
  (leftAssoc comp_exp SR)
fun comp_exp_PROD_1_SUBRULE_1_PROD_1_SUBRULE_1_PROD_1_ACT (LT, plus_minus_exp, LT_SPAN : (Lex.pos * Lex.pos), plus_minus_exp_SPAN : (Lex.pos * Lex.pos), FULL_SPAN : (Lex.pos * Lex.pos)) = 
  (ELt)
fun comp_exp_PROD_1_SUBRULE_1_PROD_1_SUBRULE_1_PROD_2_ACT (LE, plus_minus_exp, LE_SPAN : (Lex.pos * Lex.pos), plus_minus_exp_SPAN : (Lex.pos * Lex.pos), FULL_SPAN : (Lex.pos * Lex.pos)) = 
  (ELe)
fun comp_exp_PROD_1_SUBRULE_1_PROD_1_SUBRULE_1_PROD_3_ACT (GT, plus_minus_exp, GT_SPAN : (Lex.pos * Lex.pos), plus_minus_exp_SPAN : (Lex.pos * Lex.pos), FULL_SPAN : (Lex.pos * Lex.pos)) = 
  (EGt)
fun comp_exp_PROD_1_SUBRULE_1_PROD_1_SUBRULE_1_PROD_4_ACT (GE, plus_minus_exp, GE_SPAN : (Lex.pos * Lex.pos), plus_minus_exp_SPAN : (Lex.pos * Lex.pos), FULL_SPAN : (Lex.pos * Lex.pos)) = 
  (EGe)
fun comp_exp_PROD_1_SUBRULE_1_PROD_1_ACT (SR, plus_minus_exp, SR_SPAN : (Lex.pos * Lex.pos), plus_minus_exp_SPAN : (Lex.pos * Lex.pos), FULL_SPAN : (Lex.pos * Lex.pos)) = 
  (Bin(SR, plus_minus_exp))
fun comp_exp_PROD_1_ACT (SR, plus_minus_exp, SR_SPAN : (Lex.pos * Lex.pos), plus_minus_exp_SPAN : (Lex.pos * Lex.pos), FULL_SPAN : (Lex.pos * Lex.pos)) = 
  (leftAssoc plus_minus_exp SR)
fun plus_minus_exp_PROD_1_SUBRULE_1_PROD_1_SUBRULE_1_PROD_1_ACT (PLUS, times_div_mod_exp, PLUS_SPAN : (Lex.pos * Lex.pos), times_div_mod_exp_SPAN : (Lex.pos * Lex.pos), FULL_SPAN : (Lex.pos * Lex.pos)) = 
  (EAdd)
fun plus_minus_exp_PROD_1_SUBRULE_1_PROD_1_SUBRULE_1_PROD_2_ACT (times_div_mod_exp, MINUS, times_div_mod_exp_SPAN : (Lex.pos * Lex.pos), MINUS_SPAN : (Lex.pos * Lex.pos), FULL_SPAN : (Lex.pos * Lex.pos)) = 
  (ESub)
fun plus_minus_exp_PROD_1_SUBRULE_1_PROD_1_ACT (SR, times_div_mod_exp, SR_SPAN : (Lex.pos * Lex.pos), times_div_mod_exp_SPAN : (Lex.pos * Lex.pos), FULL_SPAN : (Lex.pos * Lex.pos)) = 
  (Bin(SR, times_div_mod_exp))
fun plus_minus_exp_PROD_1_ACT (SR, times_div_mod_exp, SR_SPAN : (Lex.pos * Lex.pos), times_div_mod_exp_SPAN : (Lex.pos * Lex.pos), FULL_SPAN : (Lex.pos * Lex.pos)) = 
  (leftAssoc times_div_mod_exp SR)
fun times_div_mod_exp_PROD_1_SUBRULE_1_PROD_1_SUBRULE_1_PROD_1_ACT (TIMES, pre_incr_decr_exp, TIMES_SPAN : (Lex.pos * Lex.pos), pre_incr_decr_exp_SPAN : (Lex.pos * Lex.pos), FULL_SPAN : (Lex.pos * Lex.pos)) = 
  (EMul)
fun times_div_mod_exp_PROD_1_SUBRULE_1_PROD_1_SUBRULE_1_PROD_2_ACT (DIV, pre_incr_decr_exp, DIV_SPAN : (Lex.pos * Lex.pos), pre_incr_decr_exp_SPAN : (Lex.pos * Lex.pos), FULL_SPAN : (Lex.pos * Lex.pos)) = 
  (EDiv)
fun times_div_mod_exp_PROD_1_SUBRULE_1_PROD_1_SUBRULE_1_PROD_3_ACT (MOD, pre_incr_decr_exp, MOD_SPAN : (Lex.pos * Lex.pos), pre_incr_decr_exp_SPAN : (Lex.pos * Lex.pos), FULL_SPAN : (Lex.pos * Lex.pos)) = 
  (EMod)
fun times_div_mod_exp_PROD_1_SUBRULE_1_PROD_1_ACT (SR, pre_incr_decr_exp, SR_SPAN : (Lex.pos * Lex.pos), pre_incr_decr_exp_SPAN : (Lex.pos * Lex.pos), FULL_SPAN : (Lex.pos * Lex.pos)) = 
  (Bin(SR, pre_incr_decr_exp))
fun times_div_mod_exp_PROD_1_ACT (SR, pre_incr_decr_exp, SR_SPAN : (Lex.pos * Lex.pos), pre_incr_decr_exp_SPAN : (Lex.pos * Lex.pos), FULL_SPAN : (Lex.pos * Lex.pos)) = 
  (leftAssoc pre_incr_decr_exp SR)
fun pre_incr_decr_exp_PROD_1_ACT (ID, INCR, ID_SPAN : (Lex.pos * Lex.pos), INCR_SPAN : (Lex.pos * Lex.pos), FULL_SPAN : (Lex.pos * Lex.pos)) = 
  (EPreIncr ID)
fun pre_incr_decr_exp_PROD_2_ACT (ID, DECR, ID_SPAN : (Lex.pos * Lex.pos), DECR_SPAN : (Lex.pos * Lex.pos), FULL_SPAN : (Lex.pos * Lex.pos)) = 
  (EPreDecr ID)
fun pre_incr_decr_exp_PROD_3_ACT (e, BANG, e_SPAN : (Lex.pos * Lex.pos), BANG_SPAN : (Lex.pos * Lex.pos), FULL_SPAN : (Lex.pos * Lex.pos)) = 
  (rightAssoc e (List.tabulate(length BANG, fn _ => Un ENot)))
fun post_incr_decr_call_exp_PROD_1_ACT (ID, INCR, ID_SPAN : (Lex.pos * Lex.pos), INCR_SPAN : (Lex.pos * Lex.pos), FULL_SPAN : (Lex.pos * Lex.pos)) = 
  (EPostIncr ID)
fun post_incr_decr_call_exp_PROD_2_ACT (ID, DECR, ID_SPAN : (Lex.pos * Lex.pos), DECR_SPAN : (Lex.pos * Lex.pos), FULL_SPAN : (Lex.pos * Lex.pos)) = 
  (EPostDecr ID)
fun post_incr_decr_call_exp_PROD_3_ACT (ID, LP, RP, ID_SPAN : (Lex.pos * Lex.pos), LP_SPAN : (Lex.pos * Lex.pos), RP_SPAN : (Lex.pos * Lex.pos), FULL_SPAN : (Lex.pos * Lex.pos)) = 
  (ECall(ID, []))
fun post_incr_decr_call_exp_PROD_4_SUBRULE_1_PROD_1_ACT (ID, LP, SR, exp, ID_SPAN : (Lex.pos * Lex.pos), LP_SPAN : (Lex.pos * Lex.pos), SR_SPAN : (Lex.pos * Lex.pos), exp_SPAN : (Lex.pos * Lex.pos), FULL_SPAN : (Lex.pos * Lex.pos)) = 
  (exp :: SR)
fun post_incr_decr_call_exp_PROD_4_ACT (ID, LP, RP, SR, ID_SPAN : (Lex.pos * Lex.pos), LP_SPAN : (Lex.pos * Lex.pos), RP_SPAN : (Lex.pos * Lex.pos), SR_SPAN : (Lex.pos * Lex.pos), FULL_SPAN : (Lex.pos * Lex.pos)) = 
  (ECall(ID, SR))
fun lit_id_exp_PROD_1_ACT (ID, ID_SPAN : (Lex.pos * Lex.pos), FULL_SPAN : (Lex.pos * Lex.pos)) = 
  (EId ID)
fun lit_id_exp_PROD_2_ACT (ID, EOF, ID_SPAN : (Lex.pos * Lex.pos), EOF_SPAN : (Lex.pos * Lex.pos), FULL_SPAN : (Lex.pos * Lex.pos)) = 
  (EId ID)
fun lit_id_exp_PROD_3_ACT (INT, INT_SPAN : (Lex.pos * Lex.pos), FULL_SPAN : (Lex.pos * Lex.pos)) = 
  (EInt INT)
fun lit_id_exp_PROD_4_ACT (DBL, DBL_SPAN : (Lex.pos * Lex.pos), FULL_SPAN : (Lex.pos * Lex.pos)) = 
  (EDouble DBL)
fun lit_id_exp_PROD_5_ACT (STR, STR_SPAN : (Lex.pos * Lex.pos), FULL_SPAN : (Lex.pos * Lex.pos)) = 
  (EString (String.concat STR))
fun lit_id_exp_PROD_6_ACT (TRUE, TRUE_SPAN : (Lex.pos * Lex.pos), FULL_SPAN : (Lex.pos * Lex.pos)) = 
  (ETrue)
fun lit_id_exp_PROD_7_ACT (FALSE, FALSE_SPAN : (Lex.pos * Lex.pos), FULL_SPAN : (Lex.pos * Lex.pos)) = 
  (EFalse)
fun lit_id_exp_PROD_8_ACT (LP, RP, exp, LP_SPAN : (Lex.pos * Lex.pos), RP_SPAN : (Lex.pos * Lex.pos), exp_SPAN : (Lex.pos * Lex.pos), FULL_SPAN : (Lex.pos * Lex.pos)) = 
  (exp)
fun typ_PROD_1_ACT (TINT, TINT_SPAN : (Lex.pos * Lex.pos), FULL_SPAN : (Lex.pos * Lex.pos)) = 
  ( Tint )
fun typ_PROD_2_ACT (TDBL, TDBL_SPAN : (Lex.pos * Lex.pos), FULL_SPAN : (Lex.pos * Lex.pos)) = 
  (Tdouble)
fun typ_PROD_3_ACT (TBOOL, TBOOL_SPAN : (Lex.pos * Lex.pos), FULL_SPAN : (Lex.pos * Lex.pos)) = 
  (Tbool)
fun typ_PROD_4_ACT (TVOID, TVOID_SPAN : (Lex.pos * Lex.pos), FULL_SPAN : (Lex.pos * Lex.pos)) = 
  (Tvoid)
fun typ_PROD_5_ACT (TSTRING, TSTRING_SPAN : (Lex.pos * Lex.pos), FULL_SPAN : (Lex.pos * Lex.pos)) = 
  (Tstring)
      end (* UserCode *)

    structure Err = AntlrErrHandler(
      structure Tok = Tok
      structure Lex = Lex)

(* replace functor with inline structure for better optimization
    structure EBNF = AntlrEBNF(
      struct
	type strm = Err.wstream
	val getSpan = Err.getSpan
      end)
*)
    structure EBNF =
      struct
	fun optional (pred, parse, strm) = 
	      if pred strm
		then let
		  val (y, span, strm') = parse strm
		  in 
		    (SOME y, span, strm')
		  end
		else (NONE, Err.getSpan strm, strm)

	fun closure (pred, parse, strm) = let
	      fun iter (strm, (left, right), ys) = 
		    if pred strm
		      then let
			val (y, (_, right'), strm') = parse strm
			in iter (strm', (left, right'), y::ys)
			end
		      else (List.rev ys, (left, right), strm)
	      in
		iter (strm, Err.getSpan strm, [])
	      end

	fun posclos (pred, parse, strm) = let
	      val (y, (left, _), strm') = parse strm
	      val (ys, (_, right), strm'') = closure (pred, parse, strm')
	      in
		(y::ys, (left, right), strm'')
	      end
      end

    fun mk lexFn = let
fun getS() = {}
fun putS{} = ()
fun unwrap (ret, strm, repairs) = (ret, strm, repairs)
        val (eh, lex) = Err.mkErrHandler {get = getS, put = putS}
	fun fail() = Err.failure eh
	fun tryProds (strm, prods) = let
	  fun try [] = fail()
	    | try (prod :: prods) = 
	        (Err.whileDisabled eh (fn() => prod strm)) 
		handle Err.ParseError => try (prods)
          in try prods end
fun matchEOF strm = (case (lex(strm))
 of (Tok.EOF, span, strm') => ((), span, strm')
  | _ => fail()
(* end case *))
fun matchELSE strm = (case (lex(strm))
 of (Tok.ELSE, span, strm') => ((), span, strm')
  | _ => fail()
(* end case *))
fun matchIF strm = (case (lex(strm))
 of (Tok.IF, span, strm') => ((), span, strm')
  | _ => fail()
(* end case *))
fun matchFOR strm = (case (lex(strm))
 of (Tok.FOR, span, strm') => ((), span, strm')
  | _ => fail()
(* end case *))
fun matchWHILE strm = (case (lex(strm))
 of (Tok.WHILE, span, strm') => ((), span, strm')
  | _ => fail()
(* end case *))
fun matchDO strm = (case (lex(strm))
 of (Tok.DO, span, strm') => ((), span, strm')
  | _ => fail()
(* end case *))
fun matchRETURN strm = (case (lex(strm))
 of (Tok.RETURN, span, strm') => ((), span, strm')
  | _ => fail()
(* end case *))
fun matchBANG strm = (case (lex(strm))
 of (Tok.BANG, span, strm') => ((), span, strm')
  | _ => fail()
(* end case *))
fun matchDECR strm = (case (lex(strm))
 of (Tok.DECR, span, strm') => ((), span, strm')
  | _ => fail()
(* end case *))
fun matchINCR strm = (case (lex(strm))
 of (Tok.INCR, span, strm') => ((), span, strm')
  | _ => fail()
(* end case *))
fun matchDIV strm = (case (lex(strm))
 of (Tok.DIV, span, strm') => ((), span, strm')
  | _ => fail()
(* end case *))
fun matchMOD strm = (case (lex(strm))
 of (Tok.MOD, span, strm') => ((), span, strm')
  | _ => fail()
(* end case *))
fun matchTIMES strm = (case (lex(strm))
 of (Tok.TIMES, span, strm') => ((), span, strm')
  | _ => fail()
(* end case *))
fun matchMINUS strm = (case (lex(strm))
 of (Tok.MINUS, span, strm') => ((), span, strm')
  | _ => fail()
(* end case *))
fun matchPLUS strm = (case (lex(strm))
 of (Tok.PLUS, span, strm') => ((), span, strm')
  | _ => fail()
(* end case *))
fun matchLE strm = (case (lex(strm))
 of (Tok.LE, span, strm') => ((), span, strm')
  | _ => fail()
(* end case *))
fun matchGE strm = (case (lex(strm))
 of (Tok.GE, span, strm') => ((), span, strm')
  | _ => fail()
(* end case *))
fun matchLT strm = (case (lex(strm))
 of (Tok.LT, span, strm') => ((), span, strm')
  | _ => fail()
(* end case *))
fun matchGT strm = (case (lex(strm))
 of (Tok.GT, span, strm') => ((), span, strm')
  | _ => fail()
(* end case *))
fun matchNE strm = (case (lex(strm))
 of (Tok.NE, span, strm') => ((), span, strm')
  | _ => fail()
(* end case *))
fun matchEQ strm = (case (lex(strm))
 of (Tok.EQ, span, strm') => ((), span, strm')
  | _ => fail()
(* end case *))
fun matchAND strm = (case (lex(strm))
 of (Tok.AND, span, strm') => ((), span, strm')
  | _ => fail()
(* end case *))
fun matchOR strm = (case (lex(strm))
 of (Tok.OR, span, strm') => ((), span, strm')
  | _ => fail()
(* end case *))
fun matchASSN strm = (case (lex(strm))
 of (Tok.ASSN, span, strm') => ((), span, strm')
  | _ => fail()
(* end case *))
fun matchCOLON strm = (case (lex(strm))
 of (Tok.COLON, span, strm') => ((), span, strm')
  | _ => fail()
(* end case *))
fun matchQUESTION strm = (case (lex(strm))
 of (Tok.QUESTION, span, strm') => ((), span, strm')
  | _ => fail()
(* end case *))
fun matchTERM strm = (case (lex(strm))
 of (Tok.TERM, span, strm') => ((), span, strm')
  | _ => fail()
(* end case *))
fun matchSEP strm = (case (lex(strm))
 of (Tok.SEP, span, strm') => ((), span, strm')
  | _ => fail()
(* end case *))
fun matchRBRACK strm = (case (lex(strm))
 of (Tok.RBRACK, span, strm') => ((), span, strm')
  | _ => fail()
(* end case *))
fun matchLBRACK strm = (case (lex(strm))
 of (Tok.LBRACK, span, strm') => ((), span, strm')
  | _ => fail()
(* end case *))
fun matchRB strm = (case (lex(strm))
 of (Tok.RB, span, strm') => ((), span, strm')
  | _ => fail()
(* end case *))
fun matchLB strm = (case (lex(strm))
 of (Tok.LB, span, strm') => ((), span, strm')
  | _ => fail()
(* end case *))
fun matchRP strm = (case (lex(strm))
 of (Tok.RP, span, strm') => ((), span, strm')
  | _ => fail()
(* end case *))
fun matchLP strm = (case (lex(strm))
 of (Tok.LP, span, strm') => ((), span, strm')
  | _ => fail()
(* end case *))
fun matchFALSE strm = (case (lex(strm))
 of (Tok.FALSE, span, strm') => ((), span, strm')
  | _ => fail()
(* end case *))
fun matchTRUE strm = (case (lex(strm))
 of (Tok.TRUE, span, strm') => ((), span, strm')
  | _ => fail()
(* end case *))
fun matchSTR strm = (case (lex(strm))
 of (Tok.STR(x), span, strm') => (x, span, strm')
  | _ => fail()
(* end case *))
fun matchDBL strm = (case (lex(strm))
 of (Tok.DBL(x), span, strm') => (x, span, strm')
  | _ => fail()
(* end case *))
fun matchINT strm = (case (lex(strm))
 of (Tok.INT(x), span, strm') => (x, span, strm')
  | _ => fail()
(* end case *))
fun matchID strm = (case (lex(strm))
 of (Tok.ID(x), span, strm') => (x, span, strm')
  | _ => fail()
(* end case *))
fun matchTVOID strm = (case (lex(strm))
 of (Tok.TVOID, span, strm') => ((), span, strm')
  | _ => fail()
(* end case *))
fun matchTSTRING strm = (case (lex(strm))
 of (Tok.TSTRING, span, strm') => ((), span, strm')
  | _ => fail()
(* end case *))
fun matchTBOOL strm = (case (lex(strm))
 of (Tok.TBOOL, span, strm') => ((), span, strm')
  | _ => fail()
(* end case *))
fun matchTDBL strm = (case (lex(strm))
 of (Tok.TDBL, span, strm') => ((), span, strm')
  | _ => fail()
(* end case *))
fun matchTINT strm = (case (lex(strm))
 of (Tok.TINT, span, strm') => ((), span, strm')
  | _ => fail()
(* end case *))

val (pgm_NT, exp_NT) = 
let
fun exp_NT (strm) = let
      val (asst_exp_RES, asst_exp_SPAN, strm') = asst_exp_NT(strm)
      val FULL_SPAN = (#1(asst_exp_SPAN), #2(asst_exp_SPAN))
      in
        ((asst_exp_RES), FULL_SPAN, strm')
      end
and asst_exp_NT (strm) = let
      fun asst_exp_PROD_1 (strm) = let
            val (ID_RES, ID_SPAN, strm') = matchID(strm)
            val (ASSN_RES, ASSN_SPAN, strm') = matchASSN(strm')
            val (asst_exp_RES, asst_exp_SPAN, strm') = asst_exp_NT(strm')
            val FULL_SPAN = (#1(ID_SPAN), #2(asst_exp_SPAN))
            in
              (UserCode.asst_exp_PROD_1_ACT (ID_RES, ASSN_RES, asst_exp_RES, ID_SPAN : (Lex.pos * Lex.pos), ASSN_SPAN : (Lex.pos * Lex.pos), asst_exp_SPAN : (Lex.pos * Lex.pos), FULL_SPAN : (Lex.pos * Lex.pos)),
                FULL_SPAN, strm')
            end
      fun asst_exp_PROD_2 (strm) = let
            val (cond_exp_RES, cond_exp_SPAN, strm') = cond_exp_NT(strm)
            val FULL_SPAN = (#1(cond_exp_SPAN), #2(cond_exp_SPAN))
            in
              ((cond_exp_RES), FULL_SPAN, strm')
            end
      in
        (case (lex(strm))
         of (Tok.INT(_), _, strm') => asst_exp_PROD_2(strm)
          | (Tok.DBL(_), _, strm') => asst_exp_PROD_2(strm)
          | (Tok.STR(_), _, strm') => asst_exp_PROD_2(strm)
          | (Tok.TRUE, _, strm') => asst_exp_PROD_2(strm)
          | (Tok.FALSE, _, strm') => asst_exp_PROD_2(strm)
          | (Tok.LP, _, strm') => asst_exp_PROD_2(strm)
          | (Tok.INCR, _, strm') => asst_exp_PROD_2(strm)
          | (Tok.DECR, _, strm') => asst_exp_PROD_2(strm)
          | (Tok.BANG, _, strm') => asst_exp_PROD_2(strm)
          | (Tok.ID(_), _, strm') =>
              (case (lex(strm'))
               of (Tok.ASSN, _, strm') => asst_exp_PROD_1(strm)
                | (Tok.LP, _, strm') => asst_exp_PROD_2(strm)
                | (Tok.RP, _, strm') => asst_exp_PROD_2(strm)
                | (Tok.SEP, _, strm') => asst_exp_PROD_2(strm)
                | (Tok.TERM, _, strm') => asst_exp_PROD_2(strm)
                | (Tok.QUESTION, _, strm') => asst_exp_PROD_2(strm)
                | (Tok.OR, _, strm') => asst_exp_PROD_2(strm)
                | (Tok.AND, _, strm') => asst_exp_PROD_2(strm)
                | (Tok.EQ, _, strm') => asst_exp_PROD_2(strm)
                | (Tok.NE, _, strm') => asst_exp_PROD_2(strm)
                | (Tok.GT, _, strm') => asst_exp_PROD_2(strm)
                | (Tok.LT, _, strm') => asst_exp_PROD_2(strm)
                | (Tok.GE, _, strm') => asst_exp_PROD_2(strm)
                | (Tok.LE, _, strm') => asst_exp_PROD_2(strm)
                | (Tok.PLUS, _, strm') => asst_exp_PROD_2(strm)
                | (Tok.MINUS, _, strm') => asst_exp_PROD_2(strm)
                | (Tok.TIMES, _, strm') => asst_exp_PROD_2(strm)
                | (Tok.MOD, _, strm') => asst_exp_PROD_2(strm)
                | (Tok.DIV, _, strm') => asst_exp_PROD_2(strm)
                | (Tok.INCR, _, strm') => asst_exp_PROD_2(strm)
                | (Tok.DECR, _, strm') => asst_exp_PROD_2(strm)
                | (Tok.EOF, _, strm') => asst_exp_PROD_2(strm)
                | _ => fail()
              (* end case *))
          | _ => fail()
        (* end case *))
      end
and cond_exp_NT (strm) = let
      val (or_exp_RES, or_exp_SPAN, strm') = or_exp_NT(strm)
      fun cond_exp_PROD_1_SUBRULE_1_NT (strm) = let
            val (QUESTION_RES, QUESTION_SPAN, strm') = matchQUESTION(strm)
            val (or_exp1_RES, or_exp1_SPAN, strm') = or_exp_NT(strm')
            val (COLON_RES, COLON_SPAN, strm') = matchCOLON(strm')
            val (or_exp2_RES, or_exp2_SPAN, strm') = or_exp_NT(strm')
            val FULL_SPAN = (#1(QUESTION_SPAN), #2(or_exp2_SPAN))
            in
              (UserCode.cond_exp_PROD_1_SUBRULE_1_PROD_1_ACT (QUESTION_RES, or_exp1_RES, or_exp2_RES, COLON_RES, or_exp_RES, QUESTION_SPAN : (Lex.pos * Lex.pos), or_exp1_SPAN : (Lex.pos * Lex.pos), or_exp2_SPAN : (Lex.pos * Lex.pos), COLON_SPAN : (Lex.pos * Lex.pos), or_exp_SPAN : (Lex.pos * Lex.pos), FULL_SPAN : (Lex.pos * Lex.pos)),
                FULL_SPAN, strm')
            end
      fun cond_exp_PROD_1_SUBRULE_1_PRED (strm) = (case (lex(strm))
             of (Tok.QUESTION, _, strm') => true
              | _ => false
            (* end case *))
      val (SR_RES, SR_SPAN, strm') = EBNF.closure(cond_exp_PROD_1_SUBRULE_1_PRED, cond_exp_PROD_1_SUBRULE_1_NT, strm')
      val FULL_SPAN = (#1(or_exp_SPAN), #2(SR_SPAN))
      in
        (UserCode.cond_exp_PROD_1_ACT (SR_RES, or_exp_RES, SR_SPAN : (Lex.pos * Lex.pos), or_exp_SPAN : (Lex.pos * Lex.pos), FULL_SPAN : (Lex.pos * Lex.pos)),
          FULL_SPAN, strm')
      end
and or_exp_NT (strm) = let
      val (and_exp_RES, and_exp_SPAN, strm') = and_exp_NT(strm)
      fun or_exp_PROD_1_SUBRULE_1_NT (strm) = let
            val (OR_RES, OR_SPAN, strm') = matchOR(strm)
            val (and_exp_RES, and_exp_SPAN, strm') = and_exp_NT(strm')
            val FULL_SPAN = (#1(OR_SPAN), #2(and_exp_SPAN))
            in
              (UserCode.or_exp_PROD_1_SUBRULE_1_PROD_1_ACT (OR_RES, and_exp_RES, OR_SPAN : (Lex.pos * Lex.pos), and_exp_SPAN : (Lex.pos * Lex.pos), FULL_SPAN : (Lex.pos * Lex.pos)),
                FULL_SPAN, strm')
            end
      fun or_exp_PROD_1_SUBRULE_1_PRED (strm) = (case (lex(strm))
             of (Tok.OR, _, strm') => true
              | _ => false
            (* end case *))
      val (SR_RES, SR_SPAN, strm') = EBNF.closure(or_exp_PROD_1_SUBRULE_1_PRED, or_exp_PROD_1_SUBRULE_1_NT, strm')
      val FULL_SPAN = (#1(and_exp_SPAN), #2(SR_SPAN))
      in
        (UserCode.or_exp_PROD_1_ACT (SR_RES, and_exp_RES, SR_SPAN : (Lex.pos * Lex.pos), and_exp_SPAN : (Lex.pos * Lex.pos), FULL_SPAN : (Lex.pos * Lex.pos)),
          FULL_SPAN, strm')
      end
and and_exp_NT (strm) = let
      val (eq_ne_exp_RES, eq_ne_exp_SPAN, strm') = eq_ne_exp_NT(strm)
      fun and_exp_PROD_1_SUBRULE_1_NT (strm) = let
            val (AND_RES, AND_SPAN, strm') = matchAND(strm)
            val (eq_ne_exp_RES, eq_ne_exp_SPAN, strm') = eq_ne_exp_NT(strm')
            val FULL_SPAN = (#1(AND_SPAN), #2(eq_ne_exp_SPAN))
            in
              (UserCode.and_exp_PROD_1_SUBRULE_1_PROD_1_ACT (AND_RES, eq_ne_exp_RES, AND_SPAN : (Lex.pos * Lex.pos), eq_ne_exp_SPAN : (Lex.pos * Lex.pos), FULL_SPAN : (Lex.pos * Lex.pos)),
                FULL_SPAN, strm')
            end
      fun and_exp_PROD_1_SUBRULE_1_PRED (strm) = (case (lex(strm))
             of (Tok.AND, _, strm') => true
              | _ => false
            (* end case *))
      val (SR_RES, SR_SPAN, strm') = EBNF.closure(and_exp_PROD_1_SUBRULE_1_PRED, and_exp_PROD_1_SUBRULE_1_NT, strm')
      val FULL_SPAN = (#1(eq_ne_exp_SPAN), #2(SR_SPAN))
      in
        (UserCode.and_exp_PROD_1_ACT (SR_RES, eq_ne_exp_RES, SR_SPAN : (Lex.pos * Lex.pos), eq_ne_exp_SPAN : (Lex.pos * Lex.pos), FULL_SPAN : (Lex.pos * Lex.pos)),
          FULL_SPAN, strm')
      end
and eq_ne_exp_NT (strm) = let
      val (comp_exp_RES, comp_exp_SPAN, strm') = comp_exp_NT(strm)
      fun eq_ne_exp_PROD_1_SUBRULE_1_NT (strm) = let
            val (SR_RES, SR_SPAN, strm') = let
            fun eq_ne_exp_PROD_1_SUBRULE_1_PROD_1_SUBRULE_1_NT (strm) = let
                  fun eq_ne_exp_PROD_1_SUBRULE_1_PROD_1_SUBRULE_1_PROD_1 (strm) = let
                        val (EQ_RES, EQ_SPAN, strm') = matchEQ(strm)
                        val FULL_SPAN = (#1(EQ_SPAN), #2(EQ_SPAN))
                        in
                          (UserCode.eq_ne_exp_PROD_1_SUBRULE_1_PROD_1_SUBRULE_1_PROD_1_ACT (EQ_RES, comp_exp_RES, EQ_SPAN : (Lex.pos * Lex.pos), comp_exp_SPAN : (Lex.pos * Lex.pos), FULL_SPAN : (Lex.pos * Lex.pos)),
                            FULL_SPAN, strm')
                        end
                  fun eq_ne_exp_PROD_1_SUBRULE_1_PROD_1_SUBRULE_1_PROD_2 (strm) = let
                        val (NE_RES, NE_SPAN, strm') = matchNE(strm)
                        val FULL_SPAN = (#1(NE_SPAN), #2(NE_SPAN))
                        in
                          (UserCode.eq_ne_exp_PROD_1_SUBRULE_1_PROD_1_SUBRULE_1_PROD_2_ACT (NE_RES, comp_exp_RES, NE_SPAN : (Lex.pos * Lex.pos), comp_exp_SPAN : (Lex.pos * Lex.pos), FULL_SPAN : (Lex.pos * Lex.pos)),
                            FULL_SPAN, strm')
                        end
                  in
                    (case (lex(strm))
                     of (Tok.NE, _, strm') =>
                          eq_ne_exp_PROD_1_SUBRULE_1_PROD_1_SUBRULE_1_PROD_2(strm)
                      | (Tok.EQ, _, strm') =>
                          eq_ne_exp_PROD_1_SUBRULE_1_PROD_1_SUBRULE_1_PROD_1(strm)
                      | _ => fail()
                    (* end case *))
                  end
            in
              eq_ne_exp_PROD_1_SUBRULE_1_PROD_1_SUBRULE_1_NT(strm)
            end
            val (comp_exp_RES, comp_exp_SPAN, strm') = comp_exp_NT(strm')
            val FULL_SPAN = (#1(SR_SPAN), #2(comp_exp_SPAN))
            in
              (UserCode.eq_ne_exp_PROD_1_SUBRULE_1_PROD_1_ACT (SR_RES, comp_exp_RES, SR_SPAN : (Lex.pos * Lex.pos), comp_exp_SPAN : (Lex.pos * Lex.pos), FULL_SPAN : (Lex.pos * Lex.pos)),
                FULL_SPAN, strm')
            end
      fun eq_ne_exp_PROD_1_SUBRULE_1_PRED (strm) = (case (lex(strm))
             of (Tok.EQ, _, strm') => true
              | (Tok.NE, _, strm') => true
              | _ => false
            (* end case *))
      val (SR_RES, SR_SPAN, strm') = EBNF.closure(eq_ne_exp_PROD_1_SUBRULE_1_PRED, eq_ne_exp_PROD_1_SUBRULE_1_NT, strm')
      val FULL_SPAN = (#1(comp_exp_SPAN), #2(SR_SPAN))
      in
        (UserCode.eq_ne_exp_PROD_1_ACT (SR_RES, comp_exp_RES, SR_SPAN : (Lex.pos * Lex.pos), comp_exp_SPAN : (Lex.pos * Lex.pos), FULL_SPAN : (Lex.pos * Lex.pos)),
          FULL_SPAN, strm')
      end
and comp_exp_NT (strm) = let
      val (plus_minus_exp_RES, plus_minus_exp_SPAN, strm') = plus_minus_exp_NT(strm)
      fun comp_exp_PROD_1_SUBRULE_1_NT (strm) = let
            val (SR_RES, SR_SPAN, strm') = let
            fun comp_exp_PROD_1_SUBRULE_1_PROD_1_SUBRULE_1_NT (strm) = let
                  fun comp_exp_PROD_1_SUBRULE_1_PROD_1_SUBRULE_1_PROD_1 (strm) = let
                        val (LT_RES, LT_SPAN, strm') = matchLT(strm)
                        val FULL_SPAN = (#1(LT_SPAN), #2(LT_SPAN))
                        in
                          (UserCode.comp_exp_PROD_1_SUBRULE_1_PROD_1_SUBRULE_1_PROD_1_ACT (LT_RES, plus_minus_exp_RES, LT_SPAN : (Lex.pos * Lex.pos), plus_minus_exp_SPAN : (Lex.pos * Lex.pos), FULL_SPAN : (Lex.pos * Lex.pos)),
                            FULL_SPAN, strm')
                        end
                  fun comp_exp_PROD_1_SUBRULE_1_PROD_1_SUBRULE_1_PROD_2 (strm) = let
                        val (LE_RES, LE_SPAN, strm') = matchLE(strm)
                        val FULL_SPAN = (#1(LE_SPAN), #2(LE_SPAN))
                        in
                          (UserCode.comp_exp_PROD_1_SUBRULE_1_PROD_1_SUBRULE_1_PROD_2_ACT (LE_RES, plus_minus_exp_RES, LE_SPAN : (Lex.pos * Lex.pos), plus_minus_exp_SPAN : (Lex.pos * Lex.pos), FULL_SPAN : (Lex.pos * Lex.pos)),
                            FULL_SPAN, strm')
                        end
                  fun comp_exp_PROD_1_SUBRULE_1_PROD_1_SUBRULE_1_PROD_3 (strm) = let
                        val (GT_RES, GT_SPAN, strm') = matchGT(strm)
                        val FULL_SPAN = (#1(GT_SPAN), #2(GT_SPAN))
                        in
                          (UserCode.comp_exp_PROD_1_SUBRULE_1_PROD_1_SUBRULE_1_PROD_3_ACT (GT_RES, plus_minus_exp_RES, GT_SPAN : (Lex.pos * Lex.pos), plus_minus_exp_SPAN : (Lex.pos * Lex.pos), FULL_SPAN : (Lex.pos * Lex.pos)),
                            FULL_SPAN, strm')
                        end
                  fun comp_exp_PROD_1_SUBRULE_1_PROD_1_SUBRULE_1_PROD_4 (strm) = let
                        val (GE_RES, GE_SPAN, strm') = matchGE(strm)
                        val FULL_SPAN = (#1(GE_SPAN), #2(GE_SPAN))
                        in
                          (UserCode.comp_exp_PROD_1_SUBRULE_1_PROD_1_SUBRULE_1_PROD_4_ACT (GE_RES, plus_minus_exp_RES, GE_SPAN : (Lex.pos * Lex.pos), plus_minus_exp_SPAN : (Lex.pos * Lex.pos), FULL_SPAN : (Lex.pos * Lex.pos)),
                            FULL_SPAN, strm')
                        end
                  in
                    (case (lex(strm))
                     of (Tok.GE, _, strm') =>
                          comp_exp_PROD_1_SUBRULE_1_PROD_1_SUBRULE_1_PROD_4(strm)
                      | (Tok.LE, _, strm') =>
                          comp_exp_PROD_1_SUBRULE_1_PROD_1_SUBRULE_1_PROD_2(strm)
                      | (Tok.LT, _, strm') =>
                          comp_exp_PROD_1_SUBRULE_1_PROD_1_SUBRULE_1_PROD_1(strm)
                      | (Tok.GT, _, strm') =>
                          comp_exp_PROD_1_SUBRULE_1_PROD_1_SUBRULE_1_PROD_3(strm)
                      | _ => fail()
                    (* end case *))
                  end
            in
              comp_exp_PROD_1_SUBRULE_1_PROD_1_SUBRULE_1_NT(strm)
            end
            val (plus_minus_exp_RES, plus_minus_exp_SPAN, strm') = plus_minus_exp_NT(strm')
            val FULL_SPAN = (#1(SR_SPAN), #2(plus_minus_exp_SPAN))
            in
              (UserCode.comp_exp_PROD_1_SUBRULE_1_PROD_1_ACT (SR_RES, plus_minus_exp_RES, SR_SPAN : (Lex.pos * Lex.pos), plus_minus_exp_SPAN : (Lex.pos * Lex.pos), FULL_SPAN : (Lex.pos * Lex.pos)),
                FULL_SPAN, strm')
            end
      fun comp_exp_PROD_1_SUBRULE_1_PRED (strm) = (case (lex(strm))
             of (Tok.GT, _, strm') => true
              | (Tok.LT, _, strm') => true
              | (Tok.GE, _, strm') => true
              | (Tok.LE, _, strm') => true
              | _ => false
            (* end case *))
      val (SR_RES, SR_SPAN, strm') = EBNF.closure(comp_exp_PROD_1_SUBRULE_1_PRED, comp_exp_PROD_1_SUBRULE_1_NT, strm')
      val FULL_SPAN = (#1(plus_minus_exp_SPAN), #2(SR_SPAN))
      in
        (UserCode.comp_exp_PROD_1_ACT (SR_RES, plus_minus_exp_RES, SR_SPAN : (Lex.pos * Lex.pos), plus_minus_exp_SPAN : (Lex.pos * Lex.pos), FULL_SPAN : (Lex.pos * Lex.pos)),
          FULL_SPAN, strm')
      end
and plus_minus_exp_NT (strm) = let
      val (times_div_mod_exp_RES, times_div_mod_exp_SPAN, strm') = times_div_mod_exp_NT(strm)
      fun plus_minus_exp_PROD_1_SUBRULE_1_NT (strm) = let
            val (SR_RES, SR_SPAN, strm') = let
            fun plus_minus_exp_PROD_1_SUBRULE_1_PROD_1_SUBRULE_1_NT (strm) = let
                  fun plus_minus_exp_PROD_1_SUBRULE_1_PROD_1_SUBRULE_1_PROD_1 (strm) = let
                        val (PLUS_RES, PLUS_SPAN, strm') = matchPLUS(strm)
                        val FULL_SPAN = (#1(PLUS_SPAN), #2(PLUS_SPAN))
                        in
                          (UserCode.plus_minus_exp_PROD_1_SUBRULE_1_PROD_1_SUBRULE_1_PROD_1_ACT (PLUS_RES, times_div_mod_exp_RES, PLUS_SPAN : (Lex.pos * Lex.pos), times_div_mod_exp_SPAN : (Lex.pos * Lex.pos), FULL_SPAN : (Lex.pos * Lex.pos)),
                            FULL_SPAN, strm')
                        end
                  fun plus_minus_exp_PROD_1_SUBRULE_1_PROD_1_SUBRULE_1_PROD_2 (strm) = let
                        val (MINUS_RES, MINUS_SPAN, strm') = matchMINUS(strm)
                        val FULL_SPAN = (#1(MINUS_SPAN), #2(MINUS_SPAN))
                        in
                          (UserCode.plus_minus_exp_PROD_1_SUBRULE_1_PROD_1_SUBRULE_1_PROD_2_ACT (times_div_mod_exp_RES, MINUS_RES, times_div_mod_exp_SPAN : (Lex.pos * Lex.pos), MINUS_SPAN : (Lex.pos * Lex.pos), FULL_SPAN : (Lex.pos * Lex.pos)),
                            FULL_SPAN, strm')
                        end
                  in
                    (case (lex(strm))
                     of (Tok.MINUS, _, strm') =>
                          plus_minus_exp_PROD_1_SUBRULE_1_PROD_1_SUBRULE_1_PROD_2(strm)
                      | (Tok.PLUS, _, strm') =>
                          plus_minus_exp_PROD_1_SUBRULE_1_PROD_1_SUBRULE_1_PROD_1(strm)
                      | _ => fail()
                    (* end case *))
                  end
            in
              plus_minus_exp_PROD_1_SUBRULE_1_PROD_1_SUBRULE_1_NT(strm)
            end
            val (times_div_mod_exp_RES, times_div_mod_exp_SPAN, strm') = times_div_mod_exp_NT(strm')
            val FULL_SPAN = (#1(SR_SPAN), #2(times_div_mod_exp_SPAN))
            in
              (UserCode.plus_minus_exp_PROD_1_SUBRULE_1_PROD_1_ACT (SR_RES, times_div_mod_exp_RES, SR_SPAN : (Lex.pos * Lex.pos), times_div_mod_exp_SPAN : (Lex.pos * Lex.pos), FULL_SPAN : (Lex.pos * Lex.pos)),
                FULL_SPAN, strm')
            end
      fun plus_minus_exp_PROD_1_SUBRULE_1_PRED (strm) = (case (lex(strm))
             of (Tok.PLUS, _, strm') => true
              | (Tok.MINUS, _, strm') => true
              | _ => false
            (* end case *))
      val (SR_RES, SR_SPAN, strm') = EBNF.closure(plus_minus_exp_PROD_1_SUBRULE_1_PRED, plus_minus_exp_PROD_1_SUBRULE_1_NT, strm')
      val FULL_SPAN = (#1(times_div_mod_exp_SPAN), #2(SR_SPAN))
      in
        (UserCode.plus_minus_exp_PROD_1_ACT (SR_RES, times_div_mod_exp_RES, SR_SPAN : (Lex.pos * Lex.pos), times_div_mod_exp_SPAN : (Lex.pos * Lex.pos), FULL_SPAN : (Lex.pos * Lex.pos)),
          FULL_SPAN, strm')
      end
and times_div_mod_exp_NT (strm) = let
      val (pre_incr_decr_exp_RES, pre_incr_decr_exp_SPAN, strm') = pre_incr_decr_exp_NT(strm)
      fun times_div_mod_exp_PROD_1_SUBRULE_1_NT (strm) = let
            val (SR_RES, SR_SPAN, strm') = let
            fun times_div_mod_exp_PROD_1_SUBRULE_1_PROD_1_SUBRULE_1_NT (strm) = let
                  fun times_div_mod_exp_PROD_1_SUBRULE_1_PROD_1_SUBRULE_1_PROD_1 (strm) = let
                        val (TIMES_RES, TIMES_SPAN, strm') = matchTIMES(strm)
                        val FULL_SPAN = (#1(TIMES_SPAN), #2(TIMES_SPAN))
                        in
                          (UserCode.times_div_mod_exp_PROD_1_SUBRULE_1_PROD_1_SUBRULE_1_PROD_1_ACT (TIMES_RES, pre_incr_decr_exp_RES, TIMES_SPAN : (Lex.pos * Lex.pos), pre_incr_decr_exp_SPAN : (Lex.pos * Lex.pos), FULL_SPAN : (Lex.pos * Lex.pos)),
                            FULL_SPAN, strm')
                        end
                  fun times_div_mod_exp_PROD_1_SUBRULE_1_PROD_1_SUBRULE_1_PROD_2 (strm) = let
                        val (DIV_RES, DIV_SPAN, strm') = matchDIV(strm)
                        val FULL_SPAN = (#1(DIV_SPAN), #2(DIV_SPAN))
                        in
                          (UserCode.times_div_mod_exp_PROD_1_SUBRULE_1_PROD_1_SUBRULE_1_PROD_2_ACT (DIV_RES, pre_incr_decr_exp_RES, DIV_SPAN : (Lex.pos * Lex.pos), pre_incr_decr_exp_SPAN : (Lex.pos * Lex.pos), FULL_SPAN : (Lex.pos * Lex.pos)),
                            FULL_SPAN, strm')
                        end
                  fun times_div_mod_exp_PROD_1_SUBRULE_1_PROD_1_SUBRULE_1_PROD_3 (strm) = let
                        val (MOD_RES, MOD_SPAN, strm') = matchMOD(strm)
                        val FULL_SPAN = (#1(MOD_SPAN), #2(MOD_SPAN))
                        in
                          (UserCode.times_div_mod_exp_PROD_1_SUBRULE_1_PROD_1_SUBRULE_1_PROD_3_ACT (MOD_RES, pre_incr_decr_exp_RES, MOD_SPAN : (Lex.pos * Lex.pos), pre_incr_decr_exp_SPAN : (Lex.pos * Lex.pos), FULL_SPAN : (Lex.pos * Lex.pos)),
                            FULL_SPAN, strm')
                        end
                  in
                    (case (lex(strm))
                     of (Tok.MOD, _, strm') =>
                          times_div_mod_exp_PROD_1_SUBRULE_1_PROD_1_SUBRULE_1_PROD_3(strm)
                      | (Tok.TIMES, _, strm') =>
                          times_div_mod_exp_PROD_1_SUBRULE_1_PROD_1_SUBRULE_1_PROD_1(strm)
                      | (Tok.DIV, _, strm') =>
                          times_div_mod_exp_PROD_1_SUBRULE_1_PROD_1_SUBRULE_1_PROD_2(strm)
                      | _ => fail()
                    (* end case *))
                  end
            in
              times_div_mod_exp_PROD_1_SUBRULE_1_PROD_1_SUBRULE_1_NT(strm)
            end
            val (pre_incr_decr_exp_RES, pre_incr_decr_exp_SPAN, strm') = pre_incr_decr_exp_NT(strm')
            val FULL_SPAN = (#1(SR_SPAN), #2(pre_incr_decr_exp_SPAN))
            in
              (UserCode.times_div_mod_exp_PROD_1_SUBRULE_1_PROD_1_ACT (SR_RES, pre_incr_decr_exp_RES, SR_SPAN : (Lex.pos * Lex.pos), pre_incr_decr_exp_SPAN : (Lex.pos * Lex.pos), FULL_SPAN : (Lex.pos * Lex.pos)),
                FULL_SPAN, strm')
            end
      fun times_div_mod_exp_PROD_1_SUBRULE_1_PRED (strm) = (case (lex(strm))
             of (Tok.TIMES, _, strm') => true
              | (Tok.MOD, _, strm') => true
              | (Tok.DIV, _, strm') => true
              | _ => false
            (* end case *))
      val (SR_RES, SR_SPAN, strm') = EBNF.closure(times_div_mod_exp_PROD_1_SUBRULE_1_PRED, times_div_mod_exp_PROD_1_SUBRULE_1_NT, strm')
      val FULL_SPAN = (#1(pre_incr_decr_exp_SPAN), #2(SR_SPAN))
      in
        (UserCode.times_div_mod_exp_PROD_1_ACT (SR_RES, pre_incr_decr_exp_RES, SR_SPAN : (Lex.pos * Lex.pos), pre_incr_decr_exp_SPAN : (Lex.pos * Lex.pos), FULL_SPAN : (Lex.pos * Lex.pos)),
          FULL_SPAN, strm')
      end
and pre_incr_decr_exp_NT (strm) = let
      fun pre_incr_decr_exp_PROD_1 (strm) = let
            val (INCR_RES, INCR_SPAN, strm') = matchINCR(strm)
            val (ID_RES, ID_SPAN, strm') = matchID(strm')
            val FULL_SPAN = (#1(INCR_SPAN), #2(ID_SPAN))
            in
              (UserCode.pre_incr_decr_exp_PROD_1_ACT (ID_RES, INCR_RES, ID_SPAN : (Lex.pos * Lex.pos), INCR_SPAN : (Lex.pos * Lex.pos), FULL_SPAN : (Lex.pos * Lex.pos)),
                FULL_SPAN, strm')
            end
      fun pre_incr_decr_exp_PROD_2 (strm) = let
            val (DECR_RES, DECR_SPAN, strm') = matchDECR(strm)
            val (ID_RES, ID_SPAN, strm') = matchID(strm')
            val FULL_SPAN = (#1(DECR_SPAN), #2(ID_SPAN))
            in
              (UserCode.pre_incr_decr_exp_PROD_2_ACT (ID_RES, DECR_RES, ID_SPAN : (Lex.pos * Lex.pos), DECR_SPAN : (Lex.pos * Lex.pos), FULL_SPAN : (Lex.pos * Lex.pos)),
                FULL_SPAN, strm')
            end
      fun pre_incr_decr_exp_PROD_3 (strm) = let
            fun pre_incr_decr_exp_PROD_3_SUBRULE_1_NT (strm) = let
                  val (BANG_RES, BANG_SPAN, strm') = matchBANG(strm)
                  val FULL_SPAN = (#1(BANG_SPAN), #2(BANG_SPAN))
                  in
                    ((), FULL_SPAN, strm')
                  end
            fun pre_incr_decr_exp_PROD_3_SUBRULE_1_PRED (strm) = (case (lex(strm))
                   of (Tok.BANG, _, strm') => true
                    | _ => false
                  (* end case *))
            val (BANG_RES, BANG_SPAN, strm') = EBNF.closure(pre_incr_decr_exp_PROD_3_SUBRULE_1_PRED, pre_incr_decr_exp_PROD_3_SUBRULE_1_NT, strm)
            val (e_RES, e_SPAN, strm') = post_incr_decr_call_exp_NT(strm')
            val FULL_SPAN = (#1(BANG_SPAN), #2(e_SPAN))
            in
              (UserCode.pre_incr_decr_exp_PROD_3_ACT (e_RES, BANG_RES, e_SPAN : (Lex.pos * Lex.pos), BANG_SPAN : (Lex.pos * Lex.pos), FULL_SPAN : (Lex.pos * Lex.pos)),
                FULL_SPAN, strm')
            end
      in
        (case (lex(strm))
         of (Tok.ID(_), _, strm') => pre_incr_decr_exp_PROD_3(strm)
          | (Tok.INT(_), _, strm') => pre_incr_decr_exp_PROD_3(strm)
          | (Tok.DBL(_), _, strm') => pre_incr_decr_exp_PROD_3(strm)
          | (Tok.STR(_), _, strm') => pre_incr_decr_exp_PROD_3(strm)
          | (Tok.TRUE, _, strm') => pre_incr_decr_exp_PROD_3(strm)
          | (Tok.FALSE, _, strm') => pre_incr_decr_exp_PROD_3(strm)
          | (Tok.LP, _, strm') => pre_incr_decr_exp_PROD_3(strm)
          | (Tok.BANG, _, strm') => pre_incr_decr_exp_PROD_3(strm)
          | (Tok.INCR, _, strm') => pre_incr_decr_exp_PROD_1(strm)
          | (Tok.DECR, _, strm') => pre_incr_decr_exp_PROD_2(strm)
          | _ => fail()
        (* end case *))
      end
and post_incr_decr_call_exp_NT (strm) = let
      fun post_incr_decr_call_exp_PROD_1 (strm) = let
            val (ID_RES, ID_SPAN, strm') = matchID(strm)
            val (INCR_RES, INCR_SPAN, strm') = matchINCR(strm')
            val FULL_SPAN = (#1(ID_SPAN), #2(INCR_SPAN))
            in
              (UserCode.post_incr_decr_call_exp_PROD_1_ACT (ID_RES, INCR_RES, ID_SPAN : (Lex.pos * Lex.pos), INCR_SPAN : (Lex.pos * Lex.pos), FULL_SPAN : (Lex.pos * Lex.pos)),
                FULL_SPAN, strm')
            end
      fun post_incr_decr_call_exp_PROD_2 (strm) = let
            val (ID_RES, ID_SPAN, strm') = matchID(strm)
            val (DECR_RES, DECR_SPAN, strm') = matchDECR(strm')
            val FULL_SPAN = (#1(ID_SPAN), #2(DECR_SPAN))
            in
              (UserCode.post_incr_decr_call_exp_PROD_2_ACT (ID_RES, DECR_RES, ID_SPAN : (Lex.pos * Lex.pos), DECR_SPAN : (Lex.pos * Lex.pos), FULL_SPAN : (Lex.pos * Lex.pos)),
                FULL_SPAN, strm')
            end
      fun post_incr_decr_call_exp_PROD_3 (strm) = let
            val (ID_RES, ID_SPAN, strm') = matchID(strm)
            val (LP_RES, LP_SPAN, strm') = matchLP(strm')
            val (RP_RES, RP_SPAN, strm') = matchRP(strm')
            val FULL_SPAN = (#1(ID_SPAN), #2(RP_SPAN))
            in
              (UserCode.post_incr_decr_call_exp_PROD_3_ACT (ID_RES, LP_RES, RP_RES, ID_SPAN : (Lex.pos * Lex.pos), LP_SPAN : (Lex.pos * Lex.pos), RP_SPAN : (Lex.pos * Lex.pos), FULL_SPAN : (Lex.pos * Lex.pos)),
                FULL_SPAN, strm')
            end
      fun post_incr_decr_call_exp_PROD_4 (strm) = let
            val (ID_RES, ID_SPAN, strm') = matchID(strm)
            val (LP_RES, LP_SPAN, strm') = matchLP(strm')
            val (SR_RES, SR_SPAN, strm') = let
            fun post_incr_decr_call_exp_PROD_4_SUBRULE_1_NT (strm) = let
                  val (exp_RES, exp_SPAN, strm') = exp_NT(strm)
                  fun post_incr_decr_call_exp_PROD_4_SUBRULE_1_PROD_1_SUBRULE_1_NT (strm) = let
                        val (SEP_RES, SEP_SPAN, strm') = matchSEP(strm)
                        val (exp_RES, exp_SPAN, strm') = exp_NT(strm')
                        val FULL_SPAN = (#1(SEP_SPAN), #2(exp_SPAN))
                        in
                          ((exp_RES), FULL_SPAN, strm')
                        end
                  fun post_incr_decr_call_exp_PROD_4_SUBRULE_1_PROD_1_SUBRULE_1_PRED (strm) = (case (lex(strm))
                         of (Tok.SEP, _, strm') => true
                          | _ => false
                        (* end case *))
                  val (SR_RES, SR_SPAN, strm') = EBNF.closure(post_incr_decr_call_exp_PROD_4_SUBRULE_1_PROD_1_SUBRULE_1_PRED, post_incr_decr_call_exp_PROD_4_SUBRULE_1_PROD_1_SUBRULE_1_NT, strm')
                  val FULL_SPAN = (#1(exp_SPAN), #2(SR_SPAN))
                  in
                    (UserCode.post_incr_decr_call_exp_PROD_4_SUBRULE_1_PROD_1_ACT (ID_RES, LP_RES, SR_RES, exp_RES, ID_SPAN : (Lex.pos * Lex.pos), LP_SPAN : (Lex.pos * Lex.pos), SR_SPAN : (Lex.pos * Lex.pos), exp_SPAN : (Lex.pos * Lex.pos), FULL_SPAN : (Lex.pos * Lex.pos)),
                      FULL_SPAN, strm')
                  end
            in
              post_incr_decr_call_exp_PROD_4_SUBRULE_1_NT(strm')
            end
            val (RP_RES, RP_SPAN, strm') = matchRP(strm')
            val FULL_SPAN = (#1(ID_SPAN), #2(RP_SPAN))
            in
              (UserCode.post_incr_decr_call_exp_PROD_4_ACT (ID_RES, LP_RES, RP_RES, SR_RES, ID_SPAN : (Lex.pos * Lex.pos), LP_SPAN : (Lex.pos * Lex.pos), RP_SPAN : (Lex.pos * Lex.pos), SR_SPAN : (Lex.pos * Lex.pos), FULL_SPAN : (Lex.pos * Lex.pos)),
                FULL_SPAN, strm')
            end
      fun post_incr_decr_call_exp_PROD_5 (strm) = let
            val (lit_id_exp_RES, lit_id_exp_SPAN, strm') = lit_id_exp_NT(strm)
            val FULL_SPAN = (#1(lit_id_exp_SPAN), #2(lit_id_exp_SPAN))
            in
              ((lit_id_exp_RES), FULL_SPAN, strm')
            end
      in
        (case (lex(strm))
         of (Tok.INT(_), _, strm') => post_incr_decr_call_exp_PROD_5(strm)
          | (Tok.DBL(_), _, strm') => post_incr_decr_call_exp_PROD_5(strm)
          | (Tok.STR(_), _, strm') => post_incr_decr_call_exp_PROD_5(strm)
          | (Tok.TRUE, _, strm') => post_incr_decr_call_exp_PROD_5(strm)
          | (Tok.FALSE, _, strm') => post_incr_decr_call_exp_PROD_5(strm)
          | (Tok.LP, _, strm') => post_incr_decr_call_exp_PROD_5(strm)
          | (Tok.ID(_), _, strm') =>
              (case (lex(strm'))
               of (Tok.INCR, _, strm') => post_incr_decr_call_exp_PROD_1(strm)
                | (Tok.RP, _, strm') => post_incr_decr_call_exp_PROD_5(strm)
                | (Tok.SEP, _, strm') => post_incr_decr_call_exp_PROD_5(strm)
                | (Tok.TERM, _, strm') => post_incr_decr_call_exp_PROD_5(strm)
                | (Tok.QUESTION, _, strm') =>
                    post_incr_decr_call_exp_PROD_5(strm)
                | (Tok.COLON, _, strm') => post_incr_decr_call_exp_PROD_5(strm)
                | (Tok.OR, _, strm') => post_incr_decr_call_exp_PROD_5(strm)
                | (Tok.AND, _, strm') => post_incr_decr_call_exp_PROD_5(strm)
                | (Tok.EQ, _, strm') => post_incr_decr_call_exp_PROD_5(strm)
                | (Tok.NE, _, strm') => post_incr_decr_call_exp_PROD_5(strm)
                | (Tok.GT, _, strm') => post_incr_decr_call_exp_PROD_5(strm)
                | (Tok.LT, _, strm') => post_incr_decr_call_exp_PROD_5(strm)
                | (Tok.GE, _, strm') => post_incr_decr_call_exp_PROD_5(strm)
                | (Tok.LE, _, strm') => post_incr_decr_call_exp_PROD_5(strm)
                | (Tok.PLUS, _, strm') => post_incr_decr_call_exp_PROD_5(strm)
                | (Tok.MINUS, _, strm') => post_incr_decr_call_exp_PROD_5(strm)
                | (Tok.TIMES, _, strm') => post_incr_decr_call_exp_PROD_5(strm)
                | (Tok.MOD, _, strm') => post_incr_decr_call_exp_PROD_5(strm)
                | (Tok.DIV, _, strm') => post_incr_decr_call_exp_PROD_5(strm)
                | (Tok.EOF, _, strm') => post_incr_decr_call_exp_PROD_5(strm)
                | (Tok.LP, _, strm') =>
                    (case (lex(strm'))
                     of (Tok.ID(_), _, strm') =>
                          post_incr_decr_call_exp_PROD_4(strm)
                      | (Tok.INT(_), _, strm') =>
                          post_incr_decr_call_exp_PROD_4(strm)
                      | (Tok.DBL(_), _, strm') =>
                          post_incr_decr_call_exp_PROD_4(strm)
                      | (Tok.STR(_), _, strm') =>
                          post_incr_decr_call_exp_PROD_4(strm)
                      | (Tok.TRUE, _, strm') =>
                          post_incr_decr_call_exp_PROD_4(strm)
                      | (Tok.FALSE, _, strm') =>
                          post_incr_decr_call_exp_PROD_4(strm)
                      | (Tok.LP, _, strm') =>
                          post_incr_decr_call_exp_PROD_4(strm)
                      | (Tok.INCR, _, strm') =>
                          post_incr_decr_call_exp_PROD_4(strm)
                      | (Tok.DECR, _, strm') =>
                          post_incr_decr_call_exp_PROD_4(strm)
                      | (Tok.BANG, _, strm') =>
                          post_incr_decr_call_exp_PROD_4(strm)
                      | (Tok.RP, _, strm') =>
                          post_incr_decr_call_exp_PROD_3(strm)
                      | _ => fail()
                    (* end case *))
                | (Tok.DECR, _, strm') => post_incr_decr_call_exp_PROD_2(strm)
                | _ => fail()
              (* end case *))
          | _ => fail()
        (* end case *))
      end
and lit_id_exp_NT (strm) = let
      fun lit_id_exp_PROD_1 (strm) = let
            val (ID_RES, ID_SPAN, strm') = matchID(strm)
            val FULL_SPAN = (#1(ID_SPAN), #2(ID_SPAN))
            in
              (UserCode.lit_id_exp_PROD_1_ACT (ID_RES, ID_SPAN : (Lex.pos * Lex.pos), FULL_SPAN : (Lex.pos * Lex.pos)),
                FULL_SPAN, strm')
            end
      fun lit_id_exp_PROD_2 (strm) = let
            val (ID_RES, ID_SPAN, strm') = matchID(strm)
            val (EOF_RES, EOF_SPAN, strm') = matchEOF(strm')
            val FULL_SPAN = (#1(ID_SPAN), #2(EOF_SPAN))
            in
              (UserCode.lit_id_exp_PROD_2_ACT (ID_RES, EOF_RES, ID_SPAN : (Lex.pos * Lex.pos), EOF_SPAN : (Lex.pos * Lex.pos), FULL_SPAN : (Lex.pos * Lex.pos)),
                FULL_SPAN, strm')
            end
      fun lit_id_exp_PROD_3 (strm) = let
            val (INT_RES, INT_SPAN, strm') = matchINT(strm)
            val FULL_SPAN = (#1(INT_SPAN), #2(INT_SPAN))
            in
              (UserCode.lit_id_exp_PROD_3_ACT (INT_RES, INT_SPAN : (Lex.pos * Lex.pos), FULL_SPAN : (Lex.pos * Lex.pos)),
                FULL_SPAN, strm')
            end
      fun lit_id_exp_PROD_4 (strm) = let
            val (DBL_RES, DBL_SPAN, strm') = matchDBL(strm)
            val FULL_SPAN = (#1(DBL_SPAN), #2(DBL_SPAN))
            in
              (UserCode.lit_id_exp_PROD_4_ACT (DBL_RES, DBL_SPAN : (Lex.pos * Lex.pos), FULL_SPAN : (Lex.pos * Lex.pos)),
                FULL_SPAN, strm')
            end
      fun lit_id_exp_PROD_5 (strm) = let
            fun lit_id_exp_PROD_5_SUBRULE_1_NT (strm) = let
                  val (STR_RES, STR_SPAN, strm') = matchSTR(strm)
                  val FULL_SPAN = (#1(STR_SPAN), #2(STR_SPAN))
                  in
                    ((STR_RES), FULL_SPAN, strm')
                  end
            fun lit_id_exp_PROD_5_SUBRULE_1_PRED (strm) = (case (lex(strm))
                   of (Tok.STR(_), _, strm') => true
                    | _ => false
                  (* end case *))
            val (STR_RES, STR_SPAN, strm') = EBNF.posclos(lit_id_exp_PROD_5_SUBRULE_1_PRED, lit_id_exp_PROD_5_SUBRULE_1_NT, strm)
            val FULL_SPAN = (#1(STR_SPAN), #2(STR_SPAN))
            in
              (UserCode.lit_id_exp_PROD_5_ACT (STR_RES, STR_SPAN : (Lex.pos * Lex.pos), FULL_SPAN : (Lex.pos * Lex.pos)),
                FULL_SPAN, strm')
            end
      fun lit_id_exp_PROD_6 (strm) = let
            val (TRUE_RES, TRUE_SPAN, strm') = matchTRUE(strm)
            val FULL_SPAN = (#1(TRUE_SPAN), #2(TRUE_SPAN))
            in
              (UserCode.lit_id_exp_PROD_6_ACT (TRUE_RES, TRUE_SPAN : (Lex.pos * Lex.pos), FULL_SPAN : (Lex.pos * Lex.pos)),
                FULL_SPAN, strm')
            end
      fun lit_id_exp_PROD_7 (strm) = let
            val (FALSE_RES, FALSE_SPAN, strm') = matchFALSE(strm)
            val FULL_SPAN = (#1(FALSE_SPAN), #2(FALSE_SPAN))
            in
              (UserCode.lit_id_exp_PROD_7_ACT (FALSE_RES, FALSE_SPAN : (Lex.pos * Lex.pos), FULL_SPAN : (Lex.pos * Lex.pos)),
                FULL_SPAN, strm')
            end
      fun lit_id_exp_PROD_8 (strm) = let
            val (LP_RES, LP_SPAN, strm') = matchLP(strm)
            val (exp_RES, exp_SPAN, strm') = exp_NT(strm')
            val (RP_RES, RP_SPAN, strm') = matchRP(strm')
            val FULL_SPAN = (#1(LP_SPAN), #2(RP_SPAN))
            in
              (UserCode.lit_id_exp_PROD_8_ACT (LP_RES, RP_RES, exp_RES, LP_SPAN : (Lex.pos * Lex.pos), RP_SPAN : (Lex.pos * Lex.pos), exp_SPAN : (Lex.pos * Lex.pos), FULL_SPAN : (Lex.pos * Lex.pos)),
                FULL_SPAN, strm')
            end
      in
        (case (lex(strm))
         of (Tok.LP, _, strm') => lit_id_exp_PROD_8(strm)
          | (Tok.TRUE, _, strm') => lit_id_exp_PROD_6(strm)
          | (Tok.DBL(_), _, strm') => lit_id_exp_PROD_4(strm)
          | (Tok.ID(_), _, strm') =>
              (case (lex(strm'))
               of (Tok.RP, _, strm') => lit_id_exp_PROD_1(strm)
                | (Tok.SEP, _, strm') => lit_id_exp_PROD_1(strm)
                | (Tok.TERM, _, strm') => lit_id_exp_PROD_1(strm)
                | (Tok.QUESTION, _, strm') => lit_id_exp_PROD_1(strm)
                | (Tok.COLON, _, strm') => lit_id_exp_PROD_1(strm)
                | (Tok.OR, _, strm') => lit_id_exp_PROD_1(strm)
                | (Tok.AND, _, strm') => lit_id_exp_PROD_1(strm)
                | (Tok.EQ, _, strm') => lit_id_exp_PROD_1(strm)
                | (Tok.NE, _, strm') => lit_id_exp_PROD_1(strm)
                | (Tok.GT, _, strm') => lit_id_exp_PROD_1(strm)
                | (Tok.LT, _, strm') => lit_id_exp_PROD_1(strm)
                | (Tok.GE, _, strm') => lit_id_exp_PROD_1(strm)
                | (Tok.LE, _, strm') => lit_id_exp_PROD_1(strm)
                | (Tok.PLUS, _, strm') => lit_id_exp_PROD_1(strm)
                | (Tok.MINUS, _, strm') => lit_id_exp_PROD_1(strm)
                | (Tok.TIMES, _, strm') => lit_id_exp_PROD_1(strm)
                | (Tok.MOD, _, strm') => lit_id_exp_PROD_1(strm)
                | (Tok.DIV, _, strm') => lit_id_exp_PROD_1(strm)
                | (Tok.EOF, _, strm') => lit_id_exp_PROD_2(strm)
                | _ => fail()
              (* end case *))
          | (Tok.INT(_), _, strm') => lit_id_exp_PROD_3(strm)
          | (Tok.STR(_), _, strm') => lit_id_exp_PROD_5(strm)
          | (Tok.FALSE, _, strm') => lit_id_exp_PROD_7(strm)
          | _ => fail()
        (* end case *))
      end
fun typ_NT (strm) = let
      fun typ_PROD_1 (strm) = let
            val (TINT_RES, TINT_SPAN, strm') = matchTINT(strm)
            val FULL_SPAN = (#1(TINT_SPAN), #2(TINT_SPAN))
            in
              (UserCode.typ_PROD_1_ACT (TINT_RES, TINT_SPAN : (Lex.pos * Lex.pos), FULL_SPAN : (Lex.pos * Lex.pos)),
                FULL_SPAN, strm')
            end
      fun typ_PROD_2 (strm) = let
            val (TDBL_RES, TDBL_SPAN, strm') = matchTDBL(strm)
            val FULL_SPAN = (#1(TDBL_SPAN), #2(TDBL_SPAN))
            in
              (UserCode.typ_PROD_2_ACT (TDBL_RES, TDBL_SPAN : (Lex.pos * Lex.pos), FULL_SPAN : (Lex.pos * Lex.pos)),
                FULL_SPAN, strm')
            end
      fun typ_PROD_3 (strm) = let
            val (TBOOL_RES, TBOOL_SPAN, strm') = matchTBOOL(strm)
            val FULL_SPAN = (#1(TBOOL_SPAN), #2(TBOOL_SPAN))
            in
              (UserCode.typ_PROD_3_ACT (TBOOL_RES, TBOOL_SPAN : (Lex.pos * Lex.pos), FULL_SPAN : (Lex.pos * Lex.pos)),
                FULL_SPAN, strm')
            end
      fun typ_PROD_4 (strm) = let
            val (TVOID_RES, TVOID_SPAN, strm') = matchTVOID(strm)
            val FULL_SPAN = (#1(TVOID_SPAN), #2(TVOID_SPAN))
            in
              (UserCode.typ_PROD_4_ACT (TVOID_RES, TVOID_SPAN : (Lex.pos * Lex.pos), FULL_SPAN : (Lex.pos * Lex.pos)),
                FULL_SPAN, strm')
            end
      fun typ_PROD_5 (strm) = let
            val (TSTRING_RES, TSTRING_SPAN, strm') = matchTSTRING(strm)
            val FULL_SPAN = (#1(TSTRING_SPAN), #2(TSTRING_SPAN))
            in
              (UserCode.typ_PROD_5_ACT (TSTRING_RES, TSTRING_SPAN : (Lex.pos * Lex.pos), FULL_SPAN : (Lex.pos * Lex.pos)),
                FULL_SPAN, strm')
            end
      in
        (case (lex(strm))
         of (Tok.TSTRING, _, strm') => typ_PROD_5(strm)
          | (Tok.TBOOL, _, strm') => typ_PROD_3(strm)
          | (Tok.TINT, _, strm') => typ_PROD_1(strm)
          | (Tok.TDBL, _, strm') => typ_PROD_2(strm)
          | (Tok.TVOID, _, strm') => typ_PROD_4(strm)
          | _ => fail()
        (* end case *))
      end
fun protolist_NT (strm) = let
      val (LP_RES, LP_SPAN, strm') = matchLP(strm)
      val (typ_RES, typ_SPAN, strm') = typ_NT(strm')
      fun protolist_PROD_1_SUBRULE_1_NT (strm) = let
            val (SEP_RES, SEP_SPAN, strm') = matchSEP(strm)
            val (typ_RES, typ_SPAN, strm') = typ_NT(strm')
            val FULL_SPAN = (#1(SEP_SPAN), #2(typ_SPAN))
            in
              ((typ_RES), FULL_SPAN, strm')
            end
      fun protolist_PROD_1_SUBRULE_1_PRED (strm) = (case (lex(strm))
             of (Tok.SEP, _, strm') => true
              | _ => false
            (* end case *))
      val (SR_RES, SR_SPAN, strm') = EBNF.closure(protolist_PROD_1_SUBRULE_1_PRED, protolist_PROD_1_SUBRULE_1_NT, strm')
      val (RP_RES, RP_SPAN, strm') = matchRP(strm')
      val FULL_SPAN = (#1(LP_SPAN), #2(RP_SPAN))
      in
        (UserCode.protolist_PROD_1_ACT (LP_RES, RP_RES, SR_RES, typ_RES, LP_SPAN : (Lex.pos * Lex.pos), RP_SPAN : (Lex.pos * Lex.pos), SR_SPAN : (Lex.pos * Lex.pos), typ_SPAN : (Lex.pos * Lex.pos), FULL_SPAN : (Lex.pos * Lex.pos)),
          FULL_SPAN, strm')
      end
fun stm_NT (strm) = let
      fun stm_PROD_1 (strm) = let
            val (typ_RES, typ_SPAN, strm') = typ_NT(strm)
            val (SR_RES, SR_SPAN, strm') = let
            fun stm_PROD_1_SUBRULE_1_NT (strm) = let
                  fun stm_PROD_1_SUBRULE_1_PROD_1_SUBRULE_1_NT (strm) = let
                        val (ID_RES, ID_SPAN, strm') = matchID(strm)
                        fun stm_PROD_1_SUBRULE_1_PROD_1_SUBRULE_1_PROD_1_SUBRULE_1_NT (strm) = let
                              val (SEP_RES, SEP_SPAN, strm') = matchSEP(strm)
                              val (ID_RES, ID_SPAN, strm') = matchID(strm')
                              val FULL_SPAN = (#1(SEP_SPAN), #2(ID_SPAN))
                              in
                                ((ID_RES), FULL_SPAN, strm')
                              end
                        fun stm_PROD_1_SUBRULE_1_PROD_1_SUBRULE_1_PROD_1_SUBRULE_1_PRED (strm) = (case (lex(strm))
                               of (Tok.SEP, _, strm') => true
                                | _ => false
                              (* end case *))
                        val (SR_RES, SR_SPAN, strm') = EBNF.closure(stm_PROD_1_SUBRULE_1_PROD_1_SUBRULE_1_PROD_1_SUBRULE_1_PRED, stm_PROD_1_SUBRULE_1_PROD_1_SUBRULE_1_PROD_1_SUBRULE_1_NT, strm')
                        val FULL_SPAN = (#1(ID_SPAN), #2(SR_SPAN))
                        in
                          (UserCode.stm_PROD_1_SUBRULE_1_PROD_1_SUBRULE_1_PROD_1_ACT (ID_RES, SR_RES, typ_RES, ID_SPAN : (Lex.pos * Lex.pos), SR_SPAN : (Lex.pos * Lex.pos), typ_SPAN : (Lex.pos * Lex.pos), FULL_SPAN : (Lex.pos * Lex.pos)),
                            FULL_SPAN, strm')
                        end
                  fun stm_PROD_1_SUBRULE_1_PROD_1_SUBRULE_1_PRED (strm) = (case (lex(strm))
                         of (Tok.ID(_), _, strm') => true
                          | _ => false
                        (* end case *))
                  val (SR_RES, SR_SPAN, strm') = EBNF.optional(stm_PROD_1_SUBRULE_1_PROD_1_SUBRULE_1_PRED, stm_PROD_1_SUBRULE_1_PROD_1_SUBRULE_1_NT, strm)
                  val FULL_SPAN = (#1(SR_SPAN), #2(SR_SPAN))
                  in
                    (UserCode.stm_PROD_1_SUBRULE_1_PROD_1_ACT (SR_RES, typ_RES, SR_SPAN : (Lex.pos * Lex.pos), typ_SPAN : (Lex.pos * Lex.pos), FULL_SPAN : (Lex.pos * Lex.pos)),
                      FULL_SPAN, strm')
                  end
            in
              stm_PROD_1_SUBRULE_1_NT(strm')
            end
            val (TERM_RES, TERM_SPAN, strm') = matchTERM(strm')
            val FULL_SPAN = (#1(typ_SPAN), #2(TERM_SPAN))
            in
              (UserCode.stm_PROD_1_ACT (SR_RES, typ_RES, TERM_RES, SR_SPAN : (Lex.pos * Lex.pos), typ_SPAN : (Lex.pos * Lex.pos), TERM_SPAN : (Lex.pos * Lex.pos), FULL_SPAN : (Lex.pos * Lex.pos)),
                FULL_SPAN, strm')
            end
      fun stm_PROD_2 (strm) = let
            val (typ_RES, typ_SPAN, strm') = typ_NT(strm)
            val (SR_RES, SR_SPAN, strm') = let
            fun stm_PROD_2_SUBRULE_1_NT (strm) = let
                  val (ID_RES, ID_SPAN, strm') = matchID(strm)
                  val (ASSN_RES, ASSN_SPAN, strm') = matchASSN(strm')
                  val (exp_RES, exp_SPAN, strm') = exp_NT(strm')
                  fun stm_PROD_2_SUBRULE_1_PROD_1_SUBRULE_1_NT (strm) = let
                        val (SEP_RES, SEP_SPAN, strm') = matchSEP(strm)
                        val (ID_RES, ID_SPAN, strm') = matchID(strm')
                        val (ASSN_RES, ASSN_SPAN, strm') = matchASSN(strm')
                        val (exp_RES, exp_SPAN, strm') = exp_NT(strm')
                        val FULL_SPAN = (#1(SEP_SPAN), #2(exp_SPAN))
                        in
                          ((ID_RES, exp_RES), FULL_SPAN, strm')
                        end
                  fun stm_PROD_2_SUBRULE_1_PROD_1_SUBRULE_1_PRED (strm) = (case (lex(strm))
                         of (Tok.SEP, _, strm') => true
                          | _ => false
                        (* end case *))
                  val (SR_RES, SR_SPAN, strm') = EBNF.closure(stm_PROD_2_SUBRULE_1_PROD_1_SUBRULE_1_PRED, stm_PROD_2_SUBRULE_1_PROD_1_SUBRULE_1_NT, strm')
                  val FULL_SPAN = (#1(ID_SPAN), #2(SR_SPAN))
                  in
                    (UserCode.stm_PROD_2_SUBRULE_1_PROD_1_ACT (ID_RES, SR_RES, exp_RES, typ_RES, ASSN_RES, ID_SPAN : (Lex.pos * Lex.pos), SR_SPAN : (Lex.pos * Lex.pos), exp_SPAN : (Lex.pos * Lex.pos), typ_SPAN : (Lex.pos * Lex.pos), ASSN_SPAN : (Lex.pos * Lex.pos), FULL_SPAN : (Lex.pos * Lex.pos)),
                      FULL_SPAN, strm')
                  end
            in
              stm_PROD_2_SUBRULE_1_NT(strm')
            end
            val (TERM_RES, TERM_SPAN, strm') = matchTERM(strm')
            val FULL_SPAN = (#1(typ_SPAN), #2(TERM_SPAN))
            in
              (UserCode.stm_PROD_2_ACT (SR_RES, typ_RES, TERM_RES, SR_SPAN : (Lex.pos * Lex.pos), typ_SPAN : (Lex.pos * Lex.pos), TERM_SPAN : (Lex.pos * Lex.pos), FULL_SPAN : (Lex.pos * Lex.pos)),
                FULL_SPAN, strm')
            end
      fun stm_PROD_3 (strm) = let
            val (exp_RES, exp_SPAN, strm') = exp_NT(strm)
            val (TERM_RES, TERM_SPAN, strm') = matchTERM(strm')
            val FULL_SPAN = (#1(exp_SPAN), #2(TERM_SPAN))
            in
              (UserCode.stm_PROD_3_ACT (exp_RES, TERM_RES, exp_SPAN : (Lex.pos * Lex.pos), TERM_SPAN : (Lex.pos * Lex.pos), FULL_SPAN : (Lex.pos * Lex.pos)),
                FULL_SPAN, strm')
            end
      fun stm_PROD_4 (strm) = let
            val (RETURN_RES, RETURN_SPAN, strm') = matchRETURN(strm)
            val (exp_RES, exp_SPAN, strm') = exp_NT(strm')
            val (TERM_RES, TERM_SPAN, strm') = matchTERM(strm')
            val FULL_SPAN = (#1(RETURN_SPAN), #2(TERM_SPAN))
            in
              (UserCode.stm_PROD_4_ACT (exp_RES, TERM_RES, RETURN_RES, exp_SPAN : (Lex.pos * Lex.pos), TERM_SPAN : (Lex.pos * Lex.pos), RETURN_SPAN : (Lex.pos * Lex.pos), FULL_SPAN : (Lex.pos * Lex.pos)),
                FULL_SPAN, strm')
            end
      fun stm_PROD_5 (strm) = let
            val (RETURN_RES, RETURN_SPAN, strm') = matchRETURN(strm)
            val (TERM_RES, TERM_SPAN, strm') = matchTERM(strm')
            val FULL_SPAN = (#1(RETURN_SPAN), #2(TERM_SPAN))
            in
              (UserCode.stm_PROD_5_ACT (TERM_RES, RETURN_RES, TERM_SPAN : (Lex.pos * Lex.pos), RETURN_SPAN : (Lex.pos * Lex.pos), FULL_SPAN : (Lex.pos * Lex.pos)),
                FULL_SPAN, strm')
            end
      fun stm_PROD_6 (strm) = let
            val (DO_RES, DO_SPAN, strm') = matchDO(strm)
            val (stm_RES, stm_SPAN, strm') = stm_NT(strm')
            val (WHILE_RES, WHILE_SPAN, strm') = matchWHILE(strm')
            val (LP_RES, LP_SPAN, strm') = matchLP(strm')
            val (exp_RES, exp_SPAN, strm') = exp_NT(strm')
            val (RP_RES, RP_SPAN, strm') = matchRP(strm')
            val (TERM_RES, TERM_SPAN, strm') = matchTERM(strm')
            val FULL_SPAN = (#1(DO_SPAN), #2(TERM_SPAN))
            in
              (UserCode.stm_PROD_6_ACT (DO_RES, LP_RES, RP_RES, exp_RES, stm_RES, TERM_RES, WHILE_RES, DO_SPAN : (Lex.pos * Lex.pos), LP_SPAN : (Lex.pos * Lex.pos), RP_SPAN : (Lex.pos * Lex.pos), exp_SPAN : (Lex.pos * Lex.pos), stm_SPAN : (Lex.pos * Lex.pos), TERM_SPAN : (Lex.pos * Lex.pos), WHILE_SPAN : (Lex.pos * Lex.pos), FULL_SPAN : (Lex.pos * Lex.pos)),
                FULL_SPAN, strm')
            end
      fun stm_PROD_7 (strm) = let
            val (WHILE_RES, WHILE_SPAN, strm') = matchWHILE(strm)
            val (LP_RES, LP_SPAN, strm') = matchLP(strm')
            val (exp_RES, exp_SPAN, strm') = exp_NT(strm')
            val (RP_RES, RP_SPAN, strm') = matchRP(strm')
            val (stm_RES, stm_SPAN, strm') = stm_NT(strm')
            val FULL_SPAN = (#1(WHILE_SPAN), #2(stm_SPAN))
            in
              (UserCode.stm_PROD_7_ACT (LP_RES, RP_RES, exp_RES, stm_RES, WHILE_RES, LP_SPAN : (Lex.pos * Lex.pos), RP_SPAN : (Lex.pos * Lex.pos), exp_SPAN : (Lex.pos * Lex.pos), stm_SPAN : (Lex.pos * Lex.pos), WHILE_SPAN : (Lex.pos * Lex.pos), FULL_SPAN : (Lex.pos * Lex.pos)),
                FULL_SPAN, strm')
            end
      fun stm_PROD_8 (strm) = let
            val (FOR_RES, FOR_SPAN, strm') = matchFOR(strm)
            val (LP_RES, LP_SPAN, strm') = matchLP(strm')
            val (typ_RES, typ_SPAN, strm') = typ_NT(strm')
            val (ID_RES, ID_SPAN, strm') = matchID(strm')
            val (ASSN_RES, ASSN_SPAN, strm') = matchASSN(strm')
            val (exp1_RES, exp1_SPAN, strm') = exp_NT(strm')
            val (TERM1_RES, TERM1_SPAN, strm') = matchTERM(strm')
            val (exp2_RES, exp2_SPAN, strm') = exp_NT(strm')
            val (TERM2_RES, TERM2_SPAN, strm') = matchTERM(strm')
            val (exp3_RES, exp3_SPAN, strm') = exp_NT(strm')
            val (RP_RES, RP_SPAN, strm') = matchRP(strm')
            val (stm_RES, stm_SPAN, strm') = stm_NT(strm')
            val FULL_SPAN = (#1(FOR_SPAN), #2(stm_SPAN))
            in
              (UserCode.stm_PROD_8_ACT (ID_RES, LP_RES, RP_RES, FOR_RES, stm_RES, typ_RES, ASSN_RES, exp1_RES, exp2_RES, exp3_RES, TERM1_RES, TERM2_RES, ID_SPAN : (Lex.pos * Lex.pos), LP_SPAN : (Lex.pos * Lex.pos), RP_SPAN : (Lex.pos * Lex.pos), FOR_SPAN : (Lex.pos * Lex.pos), stm_SPAN : (Lex.pos * Lex.pos), typ_SPAN : (Lex.pos * Lex.pos), ASSN_SPAN : (Lex.pos * Lex.pos), exp1_SPAN : (Lex.pos * Lex.pos), exp2_SPAN : (Lex.pos * Lex.pos), exp3_SPAN : (Lex.pos * Lex.pos), TERM1_SPAN : (Lex.pos * Lex.pos), TERM2_SPAN : (Lex.pos * Lex.pos), FULL_SPAN : (Lex.pos * Lex.pos)),
                FULL_SPAN, strm')
            end
      fun stm_PROD_9 (strm) = let
            val (cond_stm_RES, cond_stm_SPAN, strm') = cond_stm_NT(strm)
            val FULL_SPAN = (#1(cond_stm_SPAN), #2(cond_stm_SPAN))
            in
              (UserCode.stm_PROD_9_ACT (cond_stm_RES, cond_stm_SPAN : (Lex.pos * Lex.pos), FULL_SPAN : (Lex.pos * Lex.pos)),
                FULL_SPAN, strm')
            end
      fun stm_PROD_10 (strm) = let
            val (LB_RES, LB_SPAN, strm') = matchLB(strm)
            fun stm_PROD_10_SUBRULE_1_NT (strm) = let
                  val (stm_RES, stm_SPAN, strm') = stm_NT(strm)
                  val FULL_SPAN = (#1(stm_SPAN), #2(stm_SPAN))
                  in
                    ((stm_RES), FULL_SPAN, strm')
                  end
            fun stm_PROD_10_SUBRULE_1_PRED (strm) = (case (lex(strm))
                   of (Tok.TINT, _, strm') => true
                    | (Tok.TDBL, _, strm') => true
                    | (Tok.TBOOL, _, strm') => true
                    | (Tok.TSTRING, _, strm') => true
                    | (Tok.TVOID, _, strm') => true
                    | (Tok.ID(_), _, strm') => true
                    | (Tok.INT(_), _, strm') => true
                    | (Tok.DBL(_), _, strm') => true
                    | (Tok.STR(_), _, strm') => true
                    | (Tok.TRUE, _, strm') => true
                    | (Tok.FALSE, _, strm') => true
                    | (Tok.LP, _, strm') => true
                    | (Tok.LB, _, strm') => true
                    | (Tok.INCR, _, strm') => true
                    | (Tok.DECR, _, strm') => true
                    | (Tok.BANG, _, strm') => true
                    | (Tok.RETURN, _, strm') => true
                    | (Tok.DO, _, strm') => true
                    | (Tok.WHILE, _, strm') => true
                    | (Tok.FOR, _, strm') => true
                    | (Tok.IF, _, strm') => true
                    | _ => false
                  (* end case *))
            val (stm_RES, stm_SPAN, strm') = EBNF.closure(stm_PROD_10_SUBRULE_1_PRED, stm_PROD_10_SUBRULE_1_NT, strm')
            val (RB_RES, RB_SPAN, strm') = matchRB(strm')
            val FULL_SPAN = (#1(LB_SPAN), #2(RB_SPAN))
            in
              (UserCode.stm_PROD_10_ACT (LB_RES, RB_RES, stm_RES, LB_SPAN : (Lex.pos * Lex.pos), RB_SPAN : (Lex.pos * Lex.pos), stm_SPAN : (Lex.pos * Lex.pos), FULL_SPAN : (Lex.pos * Lex.pos)),
                FULL_SPAN, strm')
            end
      in
        (case (lex(strm))
         of (Tok.LB, _, strm') => stm_PROD_10(strm)
          | (Tok.FOR, _, strm') => stm_PROD_8(strm)
          | (Tok.DO, _, strm') => stm_PROD_6(strm)
          | (Tok.RETURN, _, strm') =>
              (case (lex(strm'))
               of (Tok.ID(_), _, strm') => stm_PROD_4(strm)
                | (Tok.INT(_), _, strm') => stm_PROD_4(strm)
                | (Tok.DBL(_), _, strm') => stm_PROD_4(strm)
                | (Tok.STR(_), _, strm') => stm_PROD_4(strm)
                | (Tok.TRUE, _, strm') => stm_PROD_4(strm)
                | (Tok.FALSE, _, strm') => stm_PROD_4(strm)
                | (Tok.LP, _, strm') => stm_PROD_4(strm)
                | (Tok.INCR, _, strm') => stm_PROD_4(strm)
                | (Tok.DECR, _, strm') => stm_PROD_4(strm)
                | (Tok.BANG, _, strm') => stm_PROD_4(strm)
                | (Tok.TERM, _, strm') => stm_PROD_5(strm)
                | _ => fail()
              (* end case *))
          | (Tok.TINT, _, strm') =>
              (case (lex(strm'))
               of (Tok.TERM, _, strm') => stm_PROD_1(strm)
                | (Tok.ID(_), _, strm') =>
                    (case (lex(strm'))
                     of (Tok.ASSN, _, strm') => stm_PROD_2(strm)
                      | (Tok.SEP, _, strm') => stm_PROD_1(strm)
                      | (Tok.TERM, _, strm') => stm_PROD_1(strm)
                      | _ => fail()
                    (* end case *))
                | _ => fail()
              (* end case *))
          | (Tok.TDBL, _, strm') =>
              (case (lex(strm'))
               of (Tok.TERM, _, strm') => stm_PROD_1(strm)
                | (Tok.ID(_), _, strm') =>
                    (case (lex(strm'))
                     of (Tok.ASSN, _, strm') => stm_PROD_2(strm)
                      | (Tok.SEP, _, strm') => stm_PROD_1(strm)
                      | (Tok.TERM, _, strm') => stm_PROD_1(strm)
                      | _ => fail()
                    (* end case *))
                | _ => fail()
              (* end case *))
          | (Tok.TBOOL, _, strm') =>
              (case (lex(strm'))
               of (Tok.TERM, _, strm') => stm_PROD_1(strm)
                | (Tok.ID(_), _, strm') =>
                    (case (lex(strm'))
                     of (Tok.ASSN, _, strm') => stm_PROD_2(strm)
                      | (Tok.SEP, _, strm') => stm_PROD_1(strm)
                      | (Tok.TERM, _, strm') => stm_PROD_1(strm)
                      | _ => fail()
                    (* end case *))
                | _ => fail()
              (* end case *))
          | (Tok.TSTRING, _, strm') =>
              (case (lex(strm'))
               of (Tok.TERM, _, strm') => stm_PROD_1(strm)
                | (Tok.ID(_), _, strm') =>
                    (case (lex(strm'))
                     of (Tok.ASSN, _, strm') => stm_PROD_2(strm)
                      | (Tok.SEP, _, strm') => stm_PROD_1(strm)
                      | (Tok.TERM, _, strm') => stm_PROD_1(strm)
                      | _ => fail()
                    (* end case *))
                | _ => fail()
              (* end case *))
          | (Tok.TVOID, _, strm') =>
              (case (lex(strm'))
               of (Tok.TERM, _, strm') => stm_PROD_1(strm)
                | (Tok.ID(_), _, strm') =>
                    (case (lex(strm'))
                     of (Tok.ASSN, _, strm') => stm_PROD_2(strm)
                      | (Tok.SEP, _, strm') => stm_PROD_1(strm)
                      | (Tok.TERM, _, strm') => stm_PROD_1(strm)
                      | _ => fail()
                    (* end case *))
                | _ => fail()
              (* end case *))
          | (Tok.ID(_), _, strm') => stm_PROD_3(strm)
          | (Tok.INT(_), _, strm') => stm_PROD_3(strm)
          | (Tok.DBL(_), _, strm') => stm_PROD_3(strm)
          | (Tok.STR(_), _, strm') => stm_PROD_3(strm)
          | (Tok.TRUE, _, strm') => stm_PROD_3(strm)
          | (Tok.FALSE, _, strm') => stm_PROD_3(strm)
          | (Tok.LP, _, strm') => stm_PROD_3(strm)
          | (Tok.INCR, _, strm') => stm_PROD_3(strm)
          | (Tok.DECR, _, strm') => stm_PROD_3(strm)
          | (Tok.BANG, _, strm') => stm_PROD_3(strm)
          | (Tok.WHILE, _, strm') => stm_PROD_7(strm)
          | (Tok.IF, _, strm') => stm_PROD_9(strm)
          | _ => fail()
        (* end case *))
      end
and cond_stm_NT (strm) = let
      val (IF_RES, IF_SPAN, strm') = matchIF(strm)
      val (LP_RES, LP_SPAN, strm') = matchLP(strm')
      val (exp_RES, exp_SPAN, strm') = exp_NT(strm')
      val (RP_RES, RP_SPAN, strm') = matchRP(strm')
      val (stm_RES, stm_SPAN, strm') = stm_NT(strm')
      val (SR_RES, SR_SPAN, strm') = let
      fun cond_stm_PROD_1_SUBRULE_1_NT (strm) = let
            fun cond_stm_PROD_1_SUBRULE_1_PROD_1 (strm) = let
                  val (ELSE_RES, ELSE_SPAN, strm') = matchELSE(strm)
                  val (stm_RES, stm_SPAN, strm') = stm_NT(strm')
                  val FULL_SPAN = (#1(ELSE_SPAN), #2(stm_SPAN))
                  in
                    (UserCode.cond_stm_PROD_1_SUBRULE_1_PROD_1_ACT (IF_RES, LP_RES, RP_RES, exp_RES, stm_RES, ELSE_RES, IF_SPAN : (Lex.pos * Lex.pos), LP_SPAN : (Lex.pos * Lex.pos), RP_SPAN : (Lex.pos * Lex.pos), exp_SPAN : (Lex.pos * Lex.pos), stm_SPAN : (Lex.pos * Lex.pos), ELSE_SPAN : (Lex.pos * Lex.pos), FULL_SPAN : (Lex.pos * Lex.pos)),
                      FULL_SPAN, strm')
                  end
            fun cond_stm_PROD_1_SUBRULE_1_PROD_2 (strm) = let
                  val FULL_SPAN = (Err.getPos(strm), Err.getPos(strm))
                  in
                    (UserCode.cond_stm_PROD_1_SUBRULE_1_PROD_2_ACT (IF_RES, LP_RES, RP_RES, exp_RES, stm_RES, IF_SPAN : (Lex.pos * Lex.pos), LP_SPAN : (Lex.pos * Lex.pos), RP_SPAN : (Lex.pos * Lex.pos), exp_SPAN : (Lex.pos * Lex.pos), stm_SPAN : (Lex.pos * Lex.pos), FULL_SPAN : (Lex.pos * Lex.pos)),
                      FULL_SPAN, strm)
                  end
            in
              (case (lex(strm))
               of (Tok.TINT, _, strm') =>
                    cond_stm_PROD_1_SUBRULE_1_PROD_2(strm)
                | (Tok.TDBL, _, strm') =>
                    cond_stm_PROD_1_SUBRULE_1_PROD_2(strm)
                | (Tok.TBOOL, _, strm') =>
                    cond_stm_PROD_1_SUBRULE_1_PROD_2(strm)
                | (Tok.TSTRING, _, strm') =>
                    cond_stm_PROD_1_SUBRULE_1_PROD_2(strm)
                | (Tok.TVOID, _, strm') =>
                    cond_stm_PROD_1_SUBRULE_1_PROD_2(strm)
                | (Tok.ID(_), _, strm') =>
                    cond_stm_PROD_1_SUBRULE_1_PROD_2(strm)
                | (Tok.INT(_), _, strm') =>
                    cond_stm_PROD_1_SUBRULE_1_PROD_2(strm)
                | (Tok.DBL(_), _, strm') =>
                    cond_stm_PROD_1_SUBRULE_1_PROD_2(strm)
                | (Tok.STR(_), _, strm') =>
                    cond_stm_PROD_1_SUBRULE_1_PROD_2(strm)
                | (Tok.TRUE, _, strm') =>
                    cond_stm_PROD_1_SUBRULE_1_PROD_2(strm)
                | (Tok.FALSE, _, strm') =>
                    cond_stm_PROD_1_SUBRULE_1_PROD_2(strm)
                | (Tok.LP, _, strm') => cond_stm_PROD_1_SUBRULE_1_PROD_2(strm)
                | (Tok.LB, _, strm') => cond_stm_PROD_1_SUBRULE_1_PROD_2(strm)
                | (Tok.RB, _, strm') => cond_stm_PROD_1_SUBRULE_1_PROD_2(strm)
                | (Tok.INCR, _, strm') =>
                    cond_stm_PROD_1_SUBRULE_1_PROD_2(strm)
                | (Tok.DECR, _, strm') =>
                    cond_stm_PROD_1_SUBRULE_1_PROD_2(strm)
                | (Tok.BANG, _, strm') =>
                    cond_stm_PROD_1_SUBRULE_1_PROD_2(strm)
                | (Tok.RETURN, _, strm') =>
                    cond_stm_PROD_1_SUBRULE_1_PROD_2(strm)
                | (Tok.DO, _, strm') => cond_stm_PROD_1_SUBRULE_1_PROD_2(strm)
                | (Tok.WHILE, _, strm') =>
                    cond_stm_PROD_1_SUBRULE_1_PROD_2(strm)
                | (Tok.FOR, _, strm') => cond_stm_PROD_1_SUBRULE_1_PROD_2(strm)
                | (Tok.IF, _, strm') => cond_stm_PROD_1_SUBRULE_1_PROD_2(strm)
                | (Tok.ELSE, _, strm') =>
                    cond_stm_PROD_1_SUBRULE_1_PROD_1(strm)
                | _ => fail()
              (* end case *))
            end
      in
        cond_stm_PROD_1_SUBRULE_1_NT(strm')
      end
      val FULL_SPAN = (#1(IF_SPAN), #2(SR_SPAN))
      in
        (UserCode.cond_stm_PROD_1_ACT (IF_RES, LP_RES, RP_RES, SR_RES, exp_RES, stm_RES, IF_SPAN : (Lex.pos * Lex.pos), LP_SPAN : (Lex.pos * Lex.pos), RP_SPAN : (Lex.pos * Lex.pos), SR_SPAN : (Lex.pos * Lex.pos), exp_SPAN : (Lex.pos * Lex.pos), stm_SPAN : (Lex.pos * Lex.pos), FULL_SPAN : (Lex.pos * Lex.pos)),
          FULL_SPAN, strm')
      end
fun paramlist_NT (strm) = let
      val (LP_RES, LP_SPAN, strm') = matchLP(strm)
      val (typ_RES, typ_SPAN, strm') = typ_NT(strm')
      val (ID_RES, ID_SPAN, strm') = matchID(strm')
      fun paramlist_PROD_1_SUBRULE_1_NT (strm) = let
            val (SEP_RES, SEP_SPAN, strm') = matchSEP(strm)
            val (typ_RES, typ_SPAN, strm') = typ_NT(strm')
            val (ID_RES, ID_SPAN, strm') = matchID(strm')
            val FULL_SPAN = (#1(SEP_SPAN), #2(ID_SPAN))
            in
              ((typ_RES, ID_RES), FULL_SPAN, strm')
            end
      fun paramlist_PROD_1_SUBRULE_1_PRED (strm) = (case (lex(strm))
             of (Tok.SEP, _, strm') => true
              | _ => false
            (* end case *))
      val (SR_RES, SR_SPAN, strm') = EBNF.closure(paramlist_PROD_1_SUBRULE_1_PRED, paramlist_PROD_1_SUBRULE_1_NT, strm')
      val (RP_RES, RP_SPAN, strm') = matchRP(strm')
      val FULL_SPAN = (#1(LP_SPAN), #2(RP_SPAN))
      in
        (UserCode.paramlist_PROD_1_ACT (ID_RES, LP_RES, RP_RES, SR_RES, typ_RES, ID_SPAN : (Lex.pos * Lex.pos), LP_SPAN : (Lex.pos * Lex.pos), RP_SPAN : (Lex.pos * Lex.pos), SR_SPAN : (Lex.pos * Lex.pos), typ_SPAN : (Lex.pos * Lex.pos), FULL_SPAN : (Lex.pos * Lex.pos)),
          FULL_SPAN, strm')
      end
fun defn_NT (strm) = let
      val (typ_RES, typ_SPAN, strm') = typ_NT(strm)
      val (ID_RES, ID_SPAN, strm') = matchID(strm')
      val (SR_RES, SR_SPAN, strm') = let
      fun defn_PROD_1_SUBRULE_1_NT (strm) = let
            fun defn_PROD_1_SUBRULE_1_PROD_1 (strm) = let
                  val (LP_RES, LP_SPAN, strm') = matchLP(strm)
                  val (RP_RES, RP_SPAN, strm') = matchRP(strm')
                  val (LB_RES, LB_SPAN, strm') = matchLB(strm')
                  fun defn_PROD_1_SUBRULE_1_PROD_1_SUBRULE_1_NT (strm) = let
                        val (stm_RES, stm_SPAN, strm') = stm_NT(strm)
                        val FULL_SPAN = (#1(stm_SPAN), #2(stm_SPAN))
                        in
                          ((stm_RES), FULL_SPAN, strm')
                        end
                  fun defn_PROD_1_SUBRULE_1_PROD_1_SUBRULE_1_PRED (strm) = (case (lex(strm))
                         of (Tok.TINT, _, strm') => true
                          | (Tok.TDBL, _, strm') => true
                          | (Tok.TBOOL, _, strm') => true
                          | (Tok.TSTRING, _, strm') => true
                          | (Tok.TVOID, _, strm') => true
                          | (Tok.ID(_), _, strm') => true
                          | (Tok.INT(_), _, strm') => true
                          | (Tok.DBL(_), _, strm') => true
                          | (Tok.STR(_), _, strm') => true
                          | (Tok.TRUE, _, strm') => true
                          | (Tok.FALSE, _, strm') => true
                          | (Tok.LP, _, strm') => true
                          | (Tok.LB, _, strm') => true
                          | (Tok.INCR, _, strm') => true
                          | (Tok.DECR, _, strm') => true
                          | (Tok.BANG, _, strm') => true
                          | (Tok.RETURN, _, strm') => true
                          | (Tok.DO, _, strm') => true
                          | (Tok.WHILE, _, strm') => true
                          | (Tok.FOR, _, strm') => true
                          | (Tok.IF, _, strm') => true
                          | _ => false
                        (* end case *))
                  val (stm_RES, stm_SPAN, strm') = EBNF.closure(defn_PROD_1_SUBRULE_1_PROD_1_SUBRULE_1_PRED, defn_PROD_1_SUBRULE_1_PROD_1_SUBRULE_1_NT, strm')
                  val (RB_RES, RB_SPAN, strm') = matchRB(strm')
                  val FULL_SPAN = (#1(LP_SPAN), #2(RB_SPAN))
                  in
                    (UserCode.defn_PROD_1_SUBRULE_1_PROD_1_ACT (ID_RES, LB_RES, LP_RES, RB_RES, RP_RES, stm_RES, typ_RES, ID_SPAN : (Lex.pos * Lex.pos), LB_SPAN : (Lex.pos * Lex.pos), LP_SPAN : (Lex.pos * Lex.pos), RB_SPAN : (Lex.pos * Lex.pos), RP_SPAN : (Lex.pos * Lex.pos), stm_SPAN : (Lex.pos * Lex.pos), typ_SPAN : (Lex.pos * Lex.pos), FULL_SPAN : (Lex.pos * Lex.pos)),
                      FULL_SPAN, strm')
                  end
            fun defn_PROD_1_SUBRULE_1_PROD_2 (strm) = let
                  val (LP_RES, LP_SPAN, strm') = matchLP(strm)
                  val (RP_RES, RP_SPAN, strm') = matchRP(strm')
                  val (TERM_RES, TERM_SPAN, strm') = matchTERM(strm')
                  val FULL_SPAN = (#1(LP_SPAN), #2(TERM_SPAN))
                  in
                    (UserCode.defn_PROD_1_SUBRULE_1_PROD_2_ACT (ID_RES, LP_RES, RP_RES, typ_RES, TERM_RES, ID_SPAN : (Lex.pos * Lex.pos), LP_SPAN : (Lex.pos * Lex.pos), RP_SPAN : (Lex.pos * Lex.pos), typ_SPAN : (Lex.pos * Lex.pos), TERM_SPAN : (Lex.pos * Lex.pos), FULL_SPAN : (Lex.pos * Lex.pos)),
                      FULL_SPAN, strm')
                  end
            fun defn_PROD_1_SUBRULE_1_PROD_3 (strm) = let
                  val (paramlist_RES, paramlist_SPAN, strm') = paramlist_NT(strm)
                  val (SR_RES, SR_SPAN, strm') = let
                  fun defn_PROD_1_SUBRULE_1_PROD_3_SUBRULE_1_NT (strm) = let
                        fun defn_PROD_1_SUBRULE_1_PROD_3_SUBRULE_1_PROD_1 (strm) = let
                              val (LB_RES, LB_SPAN, strm') = matchLB(strm)
                              fun defn_PROD_1_SUBRULE_1_PROD_3_SUBRULE_1_PROD_1_SUBRULE_1_NT (strm) = let
                                    val (stm_RES, stm_SPAN, strm') = stm_NT(strm)
                                    val FULL_SPAN = (#1(stm_SPAN),
                                      #2(stm_SPAN))
                                    in
                                      ((stm_RES), FULL_SPAN, strm')
                                    end
                              fun defn_PROD_1_SUBRULE_1_PROD_3_SUBRULE_1_PROD_1_SUBRULE_1_PRED (strm) = (case (lex(strm))
                                     of (Tok.TINT, _, strm') => true
                                      | (Tok.TDBL, _, strm') => true
                                      | (Tok.TBOOL, _, strm') => true
                                      | (Tok.TSTRING, _, strm') => true
                                      | (Tok.TVOID, _, strm') => true
                                      | (Tok.ID(_), _, strm') => true
                                      | (Tok.INT(_), _, strm') => true
                                      | (Tok.DBL(_), _, strm') => true
                                      | (Tok.STR(_), _, strm') => true
                                      | (Tok.TRUE, _, strm') => true
                                      | (Tok.FALSE, _, strm') => true
                                      | (Tok.LP, _, strm') => true
                                      | (Tok.LB, _, strm') => true
                                      | (Tok.INCR, _, strm') => true
                                      | (Tok.DECR, _, strm') => true
                                      | (Tok.BANG, _, strm') => true
                                      | (Tok.RETURN, _, strm') => true
                                      | (Tok.DO, _, strm') => true
                                      | (Tok.WHILE, _, strm') => true
                                      | (Tok.FOR, _, strm') => true
                                      | (Tok.IF, _, strm') => true
                                      | _ => false
                                    (* end case *))
                              val (stm_RES, stm_SPAN, strm') = EBNF.closure(defn_PROD_1_SUBRULE_1_PROD_3_SUBRULE_1_PROD_1_SUBRULE_1_PRED, defn_PROD_1_SUBRULE_1_PROD_3_SUBRULE_1_PROD_1_SUBRULE_1_NT, strm')
                              val (RB_RES, RB_SPAN, strm') = matchRB(strm')
                              val FULL_SPAN = (#1(LB_SPAN), #2(RB_SPAN))
                              in
                                (UserCode.defn_PROD_1_SUBRULE_1_PROD_3_SUBRULE_1_PROD_1_ACT (ID_RES, LB_RES, RB_RES, stm_RES, typ_RES, paramlist_RES, ID_SPAN : (Lex.pos * Lex.pos), LB_SPAN : (Lex.pos * Lex.pos), RB_SPAN : (Lex.pos * Lex.pos), stm_SPAN : (Lex.pos * Lex.pos), typ_SPAN : (Lex.pos * Lex.pos), paramlist_SPAN : (Lex.pos * Lex.pos), FULL_SPAN : (Lex.pos * Lex.pos)),
                                  FULL_SPAN, strm')
                              end
                        fun defn_PROD_1_SUBRULE_1_PROD_3_SUBRULE_1_PROD_2 (strm) = let
                              val (TERM_RES, TERM_SPAN, strm') = matchTERM(strm)
                              val FULL_SPAN = (#1(TERM_SPAN), #2(TERM_SPAN))
                              in
                                (UserCode.defn_PROD_1_SUBRULE_1_PROD_3_SUBRULE_1_PROD_2_ACT (ID_RES, typ_RES, TERM_RES, paramlist_RES, ID_SPAN : (Lex.pos * Lex.pos), typ_SPAN : (Lex.pos * Lex.pos), TERM_SPAN : (Lex.pos * Lex.pos), paramlist_SPAN : (Lex.pos * Lex.pos), FULL_SPAN : (Lex.pos * Lex.pos)),
                                  FULL_SPAN, strm')
                              end
                        in
                          (case (lex(strm))
                           of (Tok.TERM, _, strm') =>
                                defn_PROD_1_SUBRULE_1_PROD_3_SUBRULE_1_PROD_2(strm)
                            | (Tok.LB, _, strm') =>
                                defn_PROD_1_SUBRULE_1_PROD_3_SUBRULE_1_PROD_1(strm)
                            | _ => fail()
                          (* end case *))
                        end
                  in
                    defn_PROD_1_SUBRULE_1_PROD_3_SUBRULE_1_NT(strm')
                  end
                  val FULL_SPAN = (#1(paramlist_SPAN), #2(SR_SPAN))
                  in
                    (UserCode.defn_PROD_1_SUBRULE_1_PROD_3_ACT (ID_RES, SR_RES, typ_RES, paramlist_RES, ID_SPAN : (Lex.pos * Lex.pos), SR_SPAN : (Lex.pos * Lex.pos), typ_SPAN : (Lex.pos * Lex.pos), paramlist_SPAN : (Lex.pos * Lex.pos), FULL_SPAN : (Lex.pos * Lex.pos)),
                      FULL_SPAN, strm')
                  end
            fun defn_PROD_1_SUBRULE_1_PROD_4 (strm) = let
                  val (protolist_RES, protolist_SPAN, strm') = protolist_NT(strm)
                  val (TERM_RES, TERM_SPAN, strm') = matchTERM(strm')
                  val FULL_SPAN = (#1(protolist_SPAN), #2(TERM_SPAN))
                  in
                    (UserCode.defn_PROD_1_SUBRULE_1_PROD_4_ACT (ID_RES, typ_RES, TERM_RES, protolist_RES, ID_SPAN : (Lex.pos * Lex.pos), typ_SPAN : (Lex.pos * Lex.pos), TERM_SPAN : (Lex.pos * Lex.pos), protolist_SPAN : (Lex.pos * Lex.pos), FULL_SPAN : (Lex.pos * Lex.pos)),
                      FULL_SPAN, strm')
                  end
            in
              (case (lex(strm))
               of (Tok.LP, _, strm') =>
                    (case (lex(strm'))
                     of (Tok.TINT, _, strm') =>
                          (case (lex(strm'))
                           of (Tok.RP, _, strm') =>
                                defn_PROD_1_SUBRULE_1_PROD_4(strm)
                            | (Tok.SEP, _, strm') =>
                                defn_PROD_1_SUBRULE_1_PROD_4(strm)
                            | (Tok.ID(_), _, strm') =>
                                defn_PROD_1_SUBRULE_1_PROD_3(strm)
                            | _ => fail()
                          (* end case *))
                      | (Tok.TDBL, _, strm') =>
                          (case (lex(strm'))
                           of (Tok.RP, _, strm') =>
                                defn_PROD_1_SUBRULE_1_PROD_4(strm)
                            | (Tok.SEP, _, strm') =>
                                defn_PROD_1_SUBRULE_1_PROD_4(strm)
                            | (Tok.ID(_), _, strm') =>
                                defn_PROD_1_SUBRULE_1_PROD_3(strm)
                            | _ => fail()
                          (* end case *))
                      | (Tok.TBOOL, _, strm') =>
                          (case (lex(strm'))
                           of (Tok.RP, _, strm') =>
                                defn_PROD_1_SUBRULE_1_PROD_4(strm)
                            | (Tok.SEP, _, strm') =>
                                defn_PROD_1_SUBRULE_1_PROD_4(strm)
                            | (Tok.ID(_), _, strm') =>
                                defn_PROD_1_SUBRULE_1_PROD_3(strm)
                            | _ => fail()
                          (* end case *))
                      | (Tok.TSTRING, _, strm') =>
                          (case (lex(strm'))
                           of (Tok.RP, _, strm') =>
                                defn_PROD_1_SUBRULE_1_PROD_4(strm)
                            | (Tok.SEP, _, strm') =>
                                defn_PROD_1_SUBRULE_1_PROD_4(strm)
                            | (Tok.ID(_), _, strm') =>
                                defn_PROD_1_SUBRULE_1_PROD_3(strm)
                            | _ => fail()
                          (* end case *))
                      | (Tok.TVOID, _, strm') =>
                          (case (lex(strm'))
                           of (Tok.RP, _, strm') =>
                                defn_PROD_1_SUBRULE_1_PROD_4(strm)
                            | (Tok.SEP, _, strm') =>
                                defn_PROD_1_SUBRULE_1_PROD_4(strm)
                            | (Tok.ID(_), _, strm') =>
                                defn_PROD_1_SUBRULE_1_PROD_3(strm)
                            | _ => fail()
                          (* end case *))
                      | (Tok.RP, _, strm') =>
                          (case (lex(strm'))
                           of (Tok.TERM, _, strm') =>
                                defn_PROD_1_SUBRULE_1_PROD_2(strm)
                            | (Tok.LB, _, strm') =>
                                defn_PROD_1_SUBRULE_1_PROD_1(strm)
                            | _ => fail()
                          (* end case *))
                      | _ => fail()
                    (* end case *))
                | _ => fail()
              (* end case *))
            end
      in
        defn_PROD_1_SUBRULE_1_NT(strm')
      end
      val FULL_SPAN = (#1(typ_SPAN), #2(SR_SPAN))
      in
        (UserCode.defn_PROD_1_ACT (ID_RES, SR_RES, typ_RES, ID_SPAN : (Lex.pos * Lex.pos), SR_SPAN : (Lex.pos * Lex.pos), typ_SPAN : (Lex.pos * Lex.pos), FULL_SPAN : (Lex.pos * Lex.pos)),
          FULL_SPAN, strm')
      end
fun pgm_NT (strm) = let
      fun pgm_PROD_1_SUBRULE_1_NT (strm) = let
            val (defn_RES, defn_SPAN, strm') = defn_NT(strm)
            val FULL_SPAN = (#1(defn_SPAN), #2(defn_SPAN))
            in
              ((defn_RES), FULL_SPAN, strm')
            end
      fun pgm_PROD_1_SUBRULE_1_PRED (strm) = (case (lex(strm))
             of (Tok.TINT, _, strm') => true
              | (Tok.TDBL, _, strm') => true
              | (Tok.TBOOL, _, strm') => true
              | (Tok.TSTRING, _, strm') => true
              | (Tok.TVOID, _, strm') => true
              | _ => false
            (* end case *))
      val (defn_RES, defn_SPAN, strm') = EBNF.closure(pgm_PROD_1_SUBRULE_1_PRED, pgm_PROD_1_SUBRULE_1_NT, strm)
      val (EOF_RES, EOF_SPAN, strm') = matchEOF(strm')
      val FULL_SPAN = (#1(defn_SPAN), #2(EOF_SPAN))
      in
        (UserCode.pgm_PROD_1_ACT (EOF_RES, defn_RES, EOF_SPAN : (Lex.pos * Lex.pos), defn_SPAN : (Lex.pos * Lex.pos), FULL_SPAN : (Lex.pos * Lex.pos)),
          FULL_SPAN, strm')
      end
in
  (pgm_NT, exp_NT)
end
val pgm_NT =  fn s => unwrap (Err.launch (eh, lexFn, pgm_NT , true) s)
val exp_NT =  fn s => unwrap (Err.launch (eh, lexFn, exp_NT , false) s)

in (pgm_NT, exp_NT) end
  in
fun parse lexFn  s = let val (pgm_NT, exp_NT) = mk lexFn in pgm_NT s end

fun parseexp lexFn  s = let val (pgm_NT, exp_NT) = mk lexFn in exp_NT s end

  end

end
