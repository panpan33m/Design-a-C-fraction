(*  COMP 321 Homework 5:  Type-checking for a fragment of C.
*   
*   N. Danner.
*)

structure AnnAst =
struct

  (*  The type of identifiers.
  *)
  type id = Ast.id

  (*  Types.
  *)
  datatype typ = Tbool | Tint | Tdouble | Tstring | Tvoid 
               | Tarr of (typ list)*typ

  (*  The annotated type of expressions.  Notice that expressions that
  *   literals do not need to be annotated with their type, because the
  *   type information is carried by the fact that the literal is an EInt,
  *   EDouble, etc.
  *)
  datatype exp = EInt of int | EDouble of real | EString of string
               | ETrue | EFalse 
               | EId of id*typ
               | ECall of (id*(exp list))*typ
               | EPostIncr of id*typ | EPostDecr of id*typ
               | ENot of exp*typ
               | EPreIncr of id*typ | EPreDecr of id*typ 
               | EMul of (exp*exp)*typ | EDiv of (exp*exp)*typ
               | EMod of (exp*exp)*typ
               | EAdd of (exp*exp)*typ | ESub of (exp*exp)*typ
               | ELt of (exp*exp)*typ | EGt of (exp*exp)*typ 
               | ELe of (exp*exp)*typ | EGe of (exp*exp)*typ
               | EEq of (exp*exp)*typ | ENeq of (exp*exp)*typ 
               | EAnd of (exp*exp)*typ 
               | EOr of (exp*exp)*typ
               | EAsst of (id*exp)*typ
               | ECond of (exp*exp*exp)*typ

  (*  The annotated type of statements.
  *)
  datatype stm = SExp of exp 
               | SDecl of typ*(id list)
               | SInit of typ*((id*exp) list)
               | SDoWhile of stm*exp
               | SWhile of exp*stm
               | SFor of (typ*id*exp)*exp*exp*stm
               | SIf of exp*stm
               | SIfElse of exp*stm*stm
               | SReturn of exp 
               | SVReturn
               | SBlock of stm list


  (*  Parameter declarations and prototypes.
  *)
  type paramdecl = typ*id

  (*  The type of definitions.
  *)
  datatype def = DFun of typ*id*(paramdecl list)*(stm list)
               | DFunProt of typ*id*(typ list)

  (*  The type of programs.
  *)
  datatype program = PDefs of def list

  (*  tyConv ty = ty', where ty' is the AnnAst.typ corresponding to ty.
  *)
  fun tyConv (ty : Ast.typ) : typ =
    case ty of
         Ast.Tint => Tint
       | Ast.Tdouble => Tdouble
       | Ast.Tbool => Tbool
       | Ast.Tvoid => Tvoid
       | Ast.Tstring => Tstring

  fun paramsConv (ps : Ast.paramdecl list) : paramdecl list =
    map (fn (ty, id) => (tyConv ty, id)) ps
    
  fun typeOf (e : exp) : typ =
    case e of
         EInt _ => Tint
       | EDouble _ => Tdouble
       | EString _ => Tstring
       | ETrue => Tbool
       | EFalse => Tbool
       | (
           EId(_, t) |
           ECall(_, t) |
           EPostIncr(_, t) | EPostDecr(_, t) |
           ENot(_, t) |
           EPreIncr(_, t) | EPreDecr(_, t) |
           EMul(_, t) | EDiv(_, t) | EMod(_, t) |
           EAdd(_, t) | ESub(_, t) |
           ELt(_, t) | ELe(_, t) | EGt(_, t) | EGe(_, t) |
           EEq(_, t) | ENeq(_, t) |
           EAnd(_, t) | EOr(_, t) |
           EAsst(_, t) |
           ECond(_, t)
         ) => t

  (*  ********
  *   'a -> string conversion functions.
  *)

  (*  indentStr indent s = s', where s' is obtained from s by prefixing
  *     indent many spaces at the beginning.
  *)
  fun indentStr (indent : int) (s : string) : string =
    (implode (List.tabulate (indent, fn _ => #" ") )) ^ s

  (*  typToString t = a string representation of t.
  *)
  fun typToString ty =
    case ty of
         Tint => "Tint"
       | Tdouble => "Tdouble"
       | Tstring => "Tstring"
       | Tbool => "Tbool"
       | Tvoid => "Tvoid"
       | Tarr(tys, ty) =>
           "Tarr(" ^ (ListFormat.listToString typToString tys) ^ ", " ^
           (typToString ty) ^ ")"

  (*  expToStringWithIndent indent e = a string representation of e, indented by
  *     indent-many spaces.
  *)
  fun expToStringWithIndent (indent : int) (e : exp) : string =
  let
    fun unToStr(con : string, (e, ty) : exp*typ) : string =
      indentStr indent (String.concat [
        con, "(", expToStringWithIndent 0 e, ", ", typToString ty, ")"
      ])
    fun unIdToStr(con : string, (e, ty) : id*typ) : string =
      indentStr indent (String.concat [
        con, "(", e, ", ", typToString ty, ")"
      ])
    fun binToStr(con : string, ((e, e'), ty) : (exp*exp)*typ) : string =
      indentStr indent (String.concat [
        con, "(", expToStringWithIndent 0 e, ", ", expToStringWithIndent 0 e', 
        ", ", typToString ty, ")"
      ])
    fun binIdToStr(con : string, ((e, e'), ty) : (id*exp)*typ) : string =
      indentStr indent (String.concat [
        con, "(", e, ", ", expToStringWithIndent 0 e', 
        ", ", typToString ty, ")"
      ])
  in
    case e of
         EInt x => indentStr indent ("Eint(" ^ (Int.toString x) ^ ")")
       | EDouble x => indentStr indent ("EDouble(" ^ (Real.toString x) ^ ")")
       | EString s => indentStr indent ("EString(" ^ s ^ ")")
       | ETrue => indentStr indent "ETrue"
       | EFalse => indentStr indent "EFalse"
       | EId (id, ty) =>
           indentStr indent ("EId(" ^ id ^ ", " ^ (typToString ty) ^ ")")
       | ECall((f, es), ty) => indentStr indent (String.concat [
           "ECall(", 
           f,
           ", ",
           ListFormat.listToString (expToStringWithIndent 0) es, 
           ", ",
           typToString ty,
           ")"
         ])
       | EPostIncr e => unIdToStr("EPostIncr", e)
       | EPostDecr e => unIdToStr("EPostDecr", e)
       | ENot e => unToStr ("ENot", e)
       | EPreIncr e => unIdToStr("EPreIncr", e)
       | EPreDecr e => unIdToStr("EPDecr", e)
       | EMul(e) => binToStr("EMul", e)
       | EDiv(e) => binToStr("EDiv", e)
       | EMod(e) => binToStr("EMod", e)
       | EAdd(e) => binToStr("EAdd", e)
       | ESub(e) => binToStr("ESub", e)
       | ELt (e) => binToStr("ELt", e)
       | EGt (e) => binToStr("EGt", e)
       | ELe (e) => binToStr("ELe", e)
       | EGe (e) => binToStr("EGe", e)
       | EEq(e) => binToStr("EEq", e)
       | ENeq(e) => binToStr("ENeq", e)
       | EAnd(e) => binToStr("EAnd", e)
       | EOr(e) => binToStr("EOr", e)
       | EAsst(e) => binIdToStr("EAsst", e)
       | ECond((e, e0, e1), ty) => indentStr indent (String.concat [
           "ECond(",
           expToStringWithIndent 0 e,
           ", ",
           expToStringWithIndent 0 e0,
           ", ",
           expToStringWithIndent 0 e1,
           ", ",
           typToString ty,
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
             expToStringWithIndent (indent+2) exp,
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
               (fn (i, e) => "(" ^ i ^ ", " ^ (expToStringWithIndent 0 e) ^ ")")
               assns,
             ")"
           ])
       | SReturn exp =>
           String.concatWith "\n" [
             indentStr indent "SReturn(",
             expToStringWithIndent (indent+2) exp,
             indentStr indent ")"
           ]
       | SVReturn =>
           indentStr indent "SVReturn"
       | SDoWhile(s, e) =>
           String.concatWith "\n" [
             indentStr indent "SDoWhile(",
             stmToString (indent+2) s,
             ",",
             expToStringWithIndent (indent+2) e,
             ")"
           ]
       | SWhile(e, s) =>
           String.concatWith "\n" [
             indentStr indent ("SWhile(" ^ (expToStringWithIndent 0 e) ^ ","),
             stmToString (indent+2) s,
             ")"
           ]
       | SFor((ty,id,e), e0, e1, s) =>
           String.concatWith "\n" [
             indentStr indent (
               "SFor(" ^ (typToString ty) ^ " " ^ id ^ "=" ^ 
               (expToStringWithIndent 0 e) ^ "; " ^
               (expToStringWithIndent 0 e0) ^ "; " ^
               (expToStringWithIndent 0 e1) ^ ","
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
             indentStr indent ("SIf(" ^ (expToStringWithIndent 0 exp) ^ ", "),
             stmToString (indent+2) stm,
             indentStr indent ")"
           ]
       | SIfElse (exp, stm, stm') =>
           String.concatWith "\n" [
             indentStr indent ("SIfElse(" ^ (expToStringWithIndent 0 exp) ^ ", "),
             stmToString (indent+2) stm,
             indentStr indent "-",
             stmToString (indent+2) stm',
             indentStr indent ")"
           ]

  val expToString = expToStringWithIndent 0

  fun paramDeclToString (indent : int) ((ty, id) : paramdecl) : string =
    indentStr indent (
      (typToString ty) ^ ", " ^ id
    )

  fun paramProtoToString (indent : int) (ty : typ) : string =
    typToString ty

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
       | DFunProt(t, i, protos) =>
           String.concatWith "\n" [
             indentStr indent "DFunProt(",
             indentStr (indent+2) (typToString t),
             indentStr (indent+2) i,
             String.concatWith "\n" (map (paramProtoToString (indent+2)) protos),
             indentStr indent ")"
           ]

  (*  programToString defs = a string representation of defs.
  *)
  fun programToString(PDefs defs : program) : string =
    String.concatWith "\n" (map (defToString 0) defs)

  (*  **********
  *   Equality tests.  We could just use =, except for the fact that 
  *   expressions can be of the form EDouble of real, and real is
  *   not an equality type.
  *)

  (*  expEqual(e, e') = true if e and e' are the same expression, false o/w.
  *)
  fun expEqual(e : exp, e' : exp) : bool =
    case (e, e') of
         (EInt x, EInt x') => x = x'
       | (EDouble x, EDouble x') => Real.==(x, x')
       | (EString s, EString s') => s = s'
       (* | (EChar c, EChar c') => c = c' *)
       | (ETrue, ETrue) => true
       | (EFalse, EFalse) => true
       | (EId (id, ty), EId (id', ty')) => id = id' andalso ty = ty'

       | (ECall((f, es), ty), ECall((f', es'), ty')) =>
           f = f' andalso ListPair.allEq expEqual (es, es') andalso
           ty = ty'

       | (ECond((e, e0, e1), ty), ECond((e', e0', e1'), ty')) =>
            expEqual(e, e') andalso 
            expEqual(e0, e0') andalso 
            expEqual(e1, e1') andalso
            ty = ty'

       | (
         (EPostIncr (e, ty), EPostIncr (e', ty')) |
         (EPostDecr (e, ty), EPostDecr (e', ty')) |
         (EPreIncr (e, ty), EPreIncr (e', ty')) |
         (EPreDecr (e, ty), EPreDecr (e', ty'))
         ) => e = e' andalso ty = ty'

       | (
         (ENot (e, ty), ENot (e', ty'))
         ) => expEqual (e, e') andalso ty = ty'

       | (
         (EMul((e0, e1), ty), EMul((e0', e1'), ty')) |
         (EDiv((e0, e1), ty), EDiv((e0', e1'), ty')) |
         (EMod((e0, e1), ty), EMod((e0', e1'), ty')) |
         (EAdd((e0, e1), ty), EAdd((e0', e1'), ty')) |
         (ESub((e0, e1), ty), ESub((e0', e1'), ty')) |
         (ELt ((e0, e1), ty), ELt ((e0', e1'), ty')) | 
         (EGt ((e0, e1), ty), EGt ((e0', e1'), ty')) | 
         (ELe ((e0, e1), ty), ELe ((e0', e1'), ty')) | 
         (EGe ((e0, e1), ty), EGe ((e0', e1'), ty')) | 
         (EEq ((e0, e1), ty), EEq ((e0', e1'), ty')) | 
         (ENeq ((e0, e1), ty), ENeq ((e0', e1'), ty')) |
         (EAnd ((e0, e1), ty), EAnd ((e0', e1'), ty')) | 
         (EOr ((e0, e1), ty), EOr ((e0', e1'), ty'))
         ) => expEqual(e0, e0') andalso expEqual(e1, e1') andalso ty = ty'

       | (EAsst ((x, e), ty), EAsst((x', e'), ty')) =>
           x = x' andalso expEqual(e, e') andalso ty = ty'
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
       | (DFunProt(t, i, protos), DFunProt(t', i', protos')) =>
           t = t' andalso i = i' andalso protos = protos'
       | _ => false

  (*  programEqual(p, p') = true if p and p' are the same program, false o/w.
  *)
  fun programEqual(p : program, p' : program) : bool =
    case (p, p') of
         (PDefs defs, PDefs defs') =>
           ListPair.allEq defEqual (defs, defs')

end
