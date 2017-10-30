(*  COMP 321 Homework 5:  Type-checking for a fragment of C.
*
*   Abstract syntax definitions.
*   
*   N. Danner
*   Fall 2016
*)

structure Ast =
struct

  (*  The type of identifiers.
  *)
  type id = string

  (*  Types.
  *)
  datatype typ = Tbool | Tint | Tdouble | Tstring | Tvoid

  (*  The type of expressions.
  *)
  datatype exp = EInt of int | EDouble of real | EString of string
               | ETrue | EFalse 
               | EId of id
               | ECall of id*(exp list)
               | EPostIncr of id | EPostDecr of id
               | ENot of exp
               | EPreIncr of id | EPreDecr of id 
               | EMul of exp*exp | EDiv of exp*exp | EMod of exp*exp
               | EAdd of exp*exp | ESub of exp*exp
               | ELt of exp*exp | EGt of exp*exp 
               | ELe of exp*exp | EGe of exp*exp
               | EEq of exp*exp | ENeq of exp*exp 
               | EAnd of exp*exp 
               | EOr of exp*exp
               | EAsst of id*exp
               | ECond of exp*exp*exp

  (*  The type of statements.
  *)
  datatype stm = SExp of exp 
               | SDecl of typ*(id list)
               | SInit of typ*((id*exp) list)
               | SReturn of exp 
               | SVReturn
               | SDoWhile of stm*exp
               | SWhile of exp*stm
               | SFor of (typ*id*exp)*exp*exp*stm
               | SBlock of stm list
               | SIf of exp*stm
               | SIfElse of exp*stm*stm

  (*  Parameters and prototypes.
  *)
  type paramdecl = typ*id
  type prototype = typ

  (*  The type of definitions.
  *)
  datatype def = DFun of typ*id*(paramdecl list)*(stm list)
               | DFunProt of typ*id*(prototype list)

  (*  The type of programs.
  *)
  datatype program = PDefs of def list

  (*  ********
  *   'a -> string conversion functions.
  *)

  local

  (*  indentStr indent s = s', where s' is obtained from s by prefixing
  *     indent many spaces at the beginning.
  *)
  fun indentStr (indent : int) (s : string) : string =
    (implode (List.tabulate (indent, fn _ => #" ") )) ^ s

  (*  typToString t = a string representation of t.
  *)
  fun typToString (t : typ) : string =
    case t of
         Tbool => "TBool"
       | Tint => "Tint"
       | Tdouble => "Tdouble"
       | Tvoid => "Tvoid"
       | Tstring => "Tstring"

  (*  expToString indent e = a string representation of e, indented by
  *     indent-many spaces.
  *)
  fun expToString (indent : int) (e : exp) : string =
  let
    fun unToStr(con : string, e : exp) : string =
      indentStr indent (String.concat [
        con, "(", expToString 0 e, ")"
      ])
    fun unIdToStr(con : string, e : id) : string =
      indentStr indent (String.concat [
        con, "(", e, ")"
      ])
    fun binToStr(con : string, e : exp, e' : exp) : string =
      indentStr indent (String.concat [
        con, "(", expToString 0 e, ", ", expToString 0 e', ")"
      ])
    fun binIdToStr(con : string, e : id, e' : exp) : string =
      indentStr indent (String.concat [
        con, "(", e, ", ", expToString 0 e', ")"
      ])
  in
    case e of
         EInt x => indentStr indent ("Eint(" ^ (Int.toString x) ^ ")")
       | EDouble x => indentStr indent ("EDouble(" ^ (Real.toString x) ^ ")")
       | EString s => indentStr indent ("EString(" ^ s ^ ")")
       | ETrue => indentStr indent "ETrue"
       | EFalse => indentStr indent "EFalse"
       | EId id =>
           indentStr indent ("EId(" ^ id ^ ")")
       | ECall(e, es) => indentStr indent (String.concat [
           "ECall(", 
           e, 
           ListFormat.listToString (expToString 0) es, 
           ")"
         ])
       | EPostIncr e => unIdToStr("EPostIncr", e)
       | EPostDecr e => unIdToStr("EPostDecr", e)
       | ENot e => unToStr ("ENot", e)
       | EPreIncr e => unIdToStr("EPreIncr", e)
       | EPreDecr e => unIdToStr("EPDecr", e)
       | EMul(e, e') => binToStr("EMul", e, e')
       | EDiv(e, e') => binToStr("EDiv", e, e')
       | EMod(e, e') => binToStr("EMod", e, e')
       | EAdd(e, e') => binToStr("EAdd", e, e')
       | ESub(e, e') => binToStr("ESub", e, e')
       | ELt (e, e') => binToStr("ELt", e, e')
       | EGt (e, e') => binToStr("EGt", e, e')
       | ELe (e, e') => binToStr("ELe", e, e')
       | EGe (e, e') => binToStr("EGe", e, e')
       | EEq(e, e') => binToStr("EEq", e, e')
       | ENeq(e, e') => binToStr("ENeq", e, e')
       | EAnd(e, e') => binToStr("EAnd", e, e')
       | EOr(e, e') => binToStr("EOr", e, e')
       | EAsst(e, e') => binIdToStr("EAsst", e, e')
       | ECond(e, e0, e1) => indentStr indent (String.concat [
           "ECond(",
           expToString 0 e,
           ", ",
           expToString 0 e0,
           ", ",
           expToString 0 e1,
           ")"
         ])
  end

  (*  stmToString indent s = a string representation of s, indented by
  *     indent-many spaces.
  *)
  fun stmToString (indent : int) (s : stm) : string =
    case s of
         SExp exp =>
           String.concatWith "\n" [
             indentStr indent "SExp(",
             expToString (indent+2) exp,
             indentStr indent ")"
           ]
       | SDecl (qty, ids) =>
           indentStr indent (String.concat [
             "SDecl(", typToString qty, ", ",
             ListFormat.listToString String.toString ids, ")"
           ])
       | SInit(qty, assns) =>
           indentStr indent (String.concat [
             "SInit(", typToString qty, ", ",
             ListFormat.listToString 
               (fn (i, e) => "(" ^ i ^ ", " ^ (expToString 0 e) ^ ")")
               assns,
             ")"
           ])
       | SReturn exp =>
           String.concatWith "\n" [
             indentStr indent "SReturn(",
             expToString (indent+2) exp,
             indentStr indent ")"
           ]
       | SDoWhile(s, e) =>
           String.concatWith "\n" [
             indentStr indent "SDoWhile(",
             stmToString (indent+2) s,
             ",",
             expToString (indent+2) e,
             ")"
           ]
       | SWhile(e, s) =>
           String.concatWith "\n" [
             indentStr indent ("SWhile(" ^ (expToString 0 e) ^ ","),
             stmToString (indent+2) s,
             ")"
           ]
       | SFor((ty,id,e), e0, e1, s) =>
           String.concatWith "\n" [
             indentStr indent (
               "SFor(" ^ (typToString ty) ^ " " ^ id ^ "=" ^ 
               (expToString 0 e) ^ "; " ^
               (expToString 0 e0) ^ "; " ^
               (expToString 0 e1) ^ ","
             ),
             stmToString (indent+2) s,
             ")"
           ]
       | SBlock(stms) =>
           String.concatWith "\n" ([
             indentStr indent "SBlock("
           ] @ (map (stmToString (indent+2)) stms) @ [indentStr indent ")"])
       | SIf (exp, stm) =>
           String.concatWith "\n" [
             indentStr indent ("SIf(" ^ (expToString 0 exp) ^ ", "),
             stmToString (indent+2) stm,
             indentStr indent ")"
           ]
       | SIfElse (exp, stm, stm') =>
           String.concatWith "\n" [
             indentStr indent ("SIfElse(" ^ (expToString 0 exp) ^ ", "),
             stmToString (indent+2) stm,
             indentStr indent "-",
             stmToString (indent+2) stm',
             indentStr indent ")"
           ]

  fun paramDeclToString (indent : int) ((ty, id) : paramdecl) : string =
    indentStr indent (
      (typToString ty) ^ ", " ^ id
    )

  (*  defToString indent defn = a string representation of defn indented by
  *     indent-many spaces.
  *)
  fun defToString (indent : int) (defn : def) : string =
    case defn of
         DFun(t, i, argdecls, stms) =>
           String.concatWith "\n" [
             indentStr indent "DFun(",
             indentStr (indent+2) (typToString t),
             indentStr (indent+2) i,
             String.concatWith "\n" (map (paramDeclToString (indent+2)) argdecls),
             String.concatWith "\n" (map (stmToString (indent+2)) stms),
             indentStr indent ")"
           ]
       | DFunProt(t, i, tys) =>
           String.concatWith "\n" [
             indentStr indent "DFunProt(",
             indentStr (indent+2) (typToString t),
             indentStr (indent+2) i,
             String.concatWith "\n" (map typToString tys),
             indentStr indent ")"
           ]
  in

    val expToString = expToString 0

    (*  programToString defs = a string representation of defs.
    *)
    fun programToString(PDefs defs : program) : string =
      String.concatWith "\n" (map (defToString 0) defs)

  end

  (*  **********
  *   Equality tests.  We could just use =, except for the fact that 
  *   expressions can be of the form EDouble of real, and real is
  *   not an equality type.
  *
  *   These are not needed for HW 3, but I had already written them before
  *   making that decision.
  *)

  (*  expEqual(e, e') = true if e and e' are the same expression, false o/w.
  *)
  fun expEqual(e : exp, e' : exp) : bool =
    case (e, e') of
         (EInt x, EInt x') => x = x'
       | (EDouble x, EDouble x') => Real.==(x, x')
       | (EString s, EString s') => s = s'
       | (ETrue, ETrue) => true
       | (EFalse, EFalse) => true
       | (EId id, EId id') => id = id'

       | (ECall(e, es), ECall(e', es')) =>
           e = e' andalso ListPair.allEq expEqual (es, es')

       | (ECond(e, e0, e1), ECond(e', e0', e1')) =>
            expEqual(e, e') andalso expEqual(e0, e0') andalso expEqual(e1, e1')

       | (
         (EPostIncr e, EPostIncr e') |
         (EPostDecr e, EPostDecr e') |
         (EPreIncr e, EPreIncr e') |
         (EPreDecr e, EPreDecr e')
         ) => e = e'

       | (
         (ENot e, ENot e')
         ) => expEqual (e, e')

       | (
         (EMul(e0, e1), EMul(e0', e1')) |
         (EDiv(e0, e1), EDiv(e0', e1')) |
         (EMod(e0, e1), EMod(e0', e1')) |
         (EAdd(e0, e1), EAdd(e0', e1')) |
         (ESub(e0, e1), ESub(e0', e1')) |
         (ELt (e0, e1), ELt (e0', e1')) | (EGt (e0, e1), EGt (e0', e1')) | 
         (ELe (e0, e1), ELe (e0', e1')) | (EGe (e0, e1), EGe (e0', e1')) | 
         (EEq (e0, e1), EEq (e0', e1')) | (ENeq (e0, e1), ENeq (e0', e1')) |
         (EAnd (e0, e1), EAnd (e0', e1')) | (EOr (e0, e1), EOr (e0', e1'))
         ) => expEqual(e0, e0') andalso expEqual(e1, e1')

       | (EAsst (e0, e1), EAsst (e0', e1')) => 
           e0 = e0' andalso expEqual(e1, e1')
       | _ => false


  (*  stmEqual(s, s') = true if s and s' are the same statement, false o/w.
  *)
  fun stmEqual(s : stm, s' : stm) : bool =
    case (s, s') of
         (SExp e, SExp e') => expEqual(e, e')
       | (SDecl(t, is), SDecl(t', is')) =>
           t = t' andalso is = is'
       | (SInit (t, assns), SInit (t', assns')) =>
           t = t' andalso (map #1 assns) = (map #1 assns') andalso
           ListPair.allEq expEqual (map #2 assns, map #2 assns')
       | (SReturn e, SReturn e') => expEqual(e, e')
       | (SDoWhile(s, e), SDoWhile(s', e')) =>
           stmEqual(s, s') andalso expEqual(e, e')
       | (SWhile(e, s), SWhile(e', s')) =>
           expEqual(e, e') andalso stmEqual(s, s')
       | (SBlock ss, SBlock ss') => ListPair.allEq stmEqual (ss, ss')
       | (SIf(e, s), SIf(e', s')) =>
           expEqual(e, e') andalso stmEqual(s, s')
       | (SIfElse(e, s0, s1), SIfElse(e', s0', s1')) =>
           expEqual(e, e') andalso stmEqual(s0, s0') andalso stmEqual(s1, s1')
       | _ => false

  (*  defEqual(d, d') = true if d and d' are the same definition, false o/w.
  *)
  fun defEqual(d : def, d' : def) : bool =
    case (d, d') of
         (DFun(t, i, args, stms), DFun(t', i', args', stms')) =>
           t = t' andalso i = i' andalso args = args' andalso
           ListPair.allEq stmEqual (stms, stms')
       | (DFunProt(t, i, tys), DFunProt(t', i', tys')) =>
           t = t' andalso i = i' andalso tys = tys'
       | _ => false

  (*  programEqual(p, p') = true if p and p' are the same program, false o/w.
  *)
  fun programEqual(p : program, p' : program) : bool =
    case (p, p') of
         (PDefs defs, PDefs defs') =>
           ListPair.allEq defEqual (defs, defs')

end
