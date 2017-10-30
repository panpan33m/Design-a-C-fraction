(*  COMP 321 Homework 5:  CPP typing engine.
*   
*   N. Danner
*)

structure Typing =
struct

  (*  An environment is a map from identifiers to types.
  *)
  structure Id : ORD_KEY =
  struct
    type ord_key = Ast.id
    val compare = String.compare
  end
  structure M = SplayMapFn(Id)
  type env_frame = AnnAst.typ M.map
  type env = env_frame list

  (*  Configure the base environment.
  *)
  val baseEnv = M.insert(M.empty, "readInt", AnnAst.Tarr([], AnnAst.Tint))
  val baseEnv = M.insert(baseEnv, "printInt", AnnAst.Tarr([AnnAst.Tint], AnnAst.Tvoid))
  val baseEnv = M.insert(baseEnv, "readDouble", AnnAst.Tarr([], AnnAst.Tdouble))
  val baseEnv = M.insert(baseEnv, "printDouble", AnnAst.Tarr([AnnAst.Tdouble], AnnAst.Tvoid))
  val baseEnv = M.insert(baseEnv, "readBool", AnnAst.Tarr([], AnnAst.Tbool))
  val baseEnv = M.insert(baseEnv, "printBool", AnnAst.Tarr([AnnAst.Tbool], AnnAst.Tvoid))
  val baseEnv = M.insert(baseEnv, "readString", AnnAst.Tarr([], AnnAst.Tstring))
  val baseEnv = M.insert(baseEnv, "printString", AnnAst.Tarr([AnnAst.Tstring], AnnAst.Tvoid))

  exception TypeError
  exception UndeclaredError of Ast.id
  exception MultiplyDeclaredError of Ast.id
  exception ReturnTypeError

  (*  lookupEnv [f_0,...,f_{n-1}] x = f_i(x), where i is the smallest index such
  *   that i is in dom(f_i).
  *
  *   Raises UndeclaredError(x) if x is not in dom(f_i) for any i.
  *)
  fun lookupEnv (G : env) (x : Ast.id) : AnnAst.typ =
    case G of
         [] => raise UndeclaredError(x)
       | fr :: G =>
           valOf(M.find(fr, x))
           handle Option => lookupEnv G x

  (*  extendFrame (f, x, ty) = f{x |-> ty}.
  *   
  *   Raises MultiplyDeclaredError if x is in dom(f).
  *)
  fun extendFrame (fr : env_frame, x : Ast.id, ty : AnnAst.typ) : env_frame =
    case M.find(fr, x) of
         NONE => M.insert(fr, x, ty)
       | SOME _ => raise MultiplyDeclaredError x

  (*  paramTypes [(ty_0, x_0),...,(ty_{n-1}, x_{n-1})] =
  *     [tyConv ty_0,...,tyConv ty_{n-1}].
  *)
  fun paramTypes (params : Ast.paramdecl list) : AnnAst.typ list =
    map (AnnAst.tyConv o #1) params

  (*  declEnvFrame [(x_0, ty_0),...] = {(x_0, tyConv ty_0),...}.
  *)
  fun declEnvFrame (params : Ast.paramdecl list) : env_frame =
    case params of
         [] => M.empty
       | (ty, id) :: ps =>
         let
           val fr = declEnvFrame ps
         in
           M.insert(fr, id, AnnAst.tyConv ty)
         end

  (*  inferArithOp G e0 e1 con = con((e0', e1'), ty'), where
  *   - e0' = infer G e0
  *   - e1' = infer G e1
  *   - ty' is the common type of e0' and e1'.
  *
  *   Raises TypeError if either invocation of inferExp does or the types
  *   of e0' and e1' do not match or are not of type int, double, or string.
  *)
  fun inferArithOp (G : env) (e0 : Ast.exp) (e1 : Ast.exp) 
      (con : (AnnAst.exp*AnnAst.exp)*AnnAst.typ -> AnnAst.exp) : AnnAst.exp =
    let
      val e0' = inferExp G e0
      val e1' = inferExp G e1
    in
      case (AnnAst.typeOf e0', AnnAst.typeOf e1') of
           (AnnAst.Tint, AnnAst.Tint) => con((e0', e1'), AnnAst.Tint)
         | (AnnAst.Tdouble, AnnAst.Tdouble) => con((e0', e1'), AnnAst.Tdouble)
         | (AnnAst.Tstring, AnnAst.Tstring) => con((e0', e1'), AnnAst.Tstring)
         | _ => raise TypeError
    end
  (*  inferShiftOp G e0 e1 con = con((e0', e1'), ty'), where
  *   - e0' = infer G e0
  *   - e1' = infer G e1
  *   - ty' is the common type of e0' and e1'.
  *
  *   Raises TypeError if either invocation of inferExp does or e0' does not
  *   have type int or e1' does not have type int.
  *)
  and inferShiftOp (G : env) (e0 : Ast.exp) (e1 : Ast.exp)
      (con : (AnnAst.exp*AnnAst.exp)*AnnAst.typ -> AnnAst.exp) : AnnAst.exp =
    let
      val e0' = inferExp G e0
      val e1' = inferExp G e1
    in
      case (AnnAst.typeOf e0', AnnAst.typeOf e1') of
           (AnnAst.Tint, AnnAst.Tint) => con((e0', e1'), AnnAst.Tint)
         | _ => raise TypeError
    end

  (*  inferBoolOp G e0 e1 con = con((e0', e1'), Tbool), where
  *   - e0' = infer G e0
  *   - e1' = infer G e1
  *
  *   Raises TypeError if either invocation of inferExp does or the types
  *   of e0' and e1' do not match or are not of type bool.
  *)
  and inferBoolOp (G : env) (e0 : Ast.exp) (e1 : Ast.exp) 
      (con : (AnnAst.exp*AnnAst.exp)*AnnAst.typ -> AnnAst.exp) : AnnAst.exp =
    let
      val e0' = inferExp G e0
      val e1' = inferExp G e1
    in
      case (AnnAst.typeOf e0', AnnAst.typeOf e1') of
           (AnnAst.Tbool, AnnAst.Tbool) => con((e0', e1'), AnnAst.Tbool)
         | _ => raise TypeError
    end

  (*  inferNumRel G e0 e1 con = con((e0', e1'), Tbool), where
  *   - e0' = infer G e0
  *   - e1' = infer G e1
  *
  *   Raises TypeError if either invocation of inferExp does or the types
  *   of e0' and e1' do not match or are not of type int or double.
  *)
  and inferNumRel (G : env) (e0 : Ast.exp) (e1 : Ast.exp) 
      (con : (AnnAst.exp*AnnAst.exp)*AnnAst.typ -> AnnAst.exp) : AnnAst.exp =
    let
      val e0' = inferExp G e0
      val e1' = inferExp G e1
    in
      case (AnnAst.typeOf e0', AnnAst.typeOf e1') of
           (AnnAst.Tint, AnnAst.Tint) => con((e0', e1'), AnnAst.Tbool)
         | (AnnAst.Tdouble, AnnAst.Tdouble) => con((e0', e1'), AnnAst.Tbool)
         | _ => raise TypeError
    end

  (*  inferBinRel G e0 e1 con = con((e0', e1'), Tbool), where
  *   - e0' = infer G e0
  *   - e1' = infer G e1
  *
  *   Raises TypeError if either invocation of inferExp does or the types
  *   of e0' and e1' do not match or are not of type int, double, bool, or 
  *   string.
  *)
  and inferBinRel (G : env) (e0 : Ast.exp) (e1 : Ast.exp) 
      (con : (AnnAst.exp*AnnAst.exp)*AnnAst.typ -> AnnAst.exp) : AnnAst.exp =
    let
      val e0' = inferExp G e0
      val e1' = inferExp G e1
    in
      case (AnnAst.typeOf e0', AnnAst.typeOf e1') of
           (AnnAst.Tint, AnnAst.Tint) => con((e0', e1'), AnnAst.Tbool)
         | (AnnAst.Tdouble, AnnAst.Tdouble) => con((e0', e1'), AnnAst.Tbool)
         | (AnnAst.Tstring, AnnAst.Tstring) => con((e0', e1'), AnnAst.Tbool)
         | (AnnAst.Tbool, AnnAst.Tbool) => con((e0', e1'), AnnAst.Tbool)
         | _ => raise TypeError
    end

  (*  inferExp G e = e', where e' is the annotated AST corresponding
  *   to e, provided G |- e : tau for some tau.
  *
  *   Raises TypeError if G |- e : tau is false for all tau.
  *)
  and inferExp (G : env) (e : Ast.exp) : AnnAst.exp =
    case e of
         Ast.EInt n => AnnAst.EInt n
       | Ast.EDouble x => AnnAst.EDouble x
       | Ast.EString s => AnnAst.EString s
       | Ast.ETrue => AnnAst.ETrue
       | Ast.EFalse => AnnAst.EFalse
       | Ast.EId x => AnnAst.EId(x, lookupEnv G x)
       | Ast.ECall (f, es) =>
         let
           val AnnAst.Tarr(ptys, rty) = lookupEnv G f
           val es' = map (inferExp G) es
         in
           if map AnnAst.typeOf es' <> ptys then raise TypeError
           else AnnAst.ECall((f, es'), rty)
         end
       | Ast.EPostIncr x =>
         let
           val ty = lookupEnv G x
         in
           case ty of
                AnnAst.Tint => AnnAst.EPostIncr(x, ty)
              | _ => raise TypeError
         end
       | Ast.EPostDecr x =>
         let
           val ty = lookupEnv G x
         in
           case ty of
                AnnAst.Tint => AnnAst.EPostDecr(x, ty)
              | _ => raise TypeError
         end
       | Ast.ENot e =>
         let
           val e' = inferExp G e
         in
           case AnnAst.typeOf e' of
                AnnAst.Tbool => AnnAst.ENot(e', AnnAst.Tbool)
              | _ => raise TypeError
         end
       | Ast.EPreIncr x =>
         let
           val ty = lookupEnv G x
         in
           case ty of
                AnnAst.Tint => AnnAst.EPreIncr(x, ty)
              | _ => raise TypeError
         end
       | Ast.EPreDecr x =>
         let
           val ty = lookupEnv G x
         in
           case ty of
                AnnAst.Tint => AnnAst.EPreDecr(x, ty)
              | _ => raise TypeError
         end
       | Ast.EMul(e0, e1) => inferArithOp G e0 e1 AnnAst.EMul
       | Ast.EDiv(e0, e1) => inferArithOp G e0 e1 AnnAst.EDiv
       | Ast.EMod(e0, e1) => inferArithOp G e0 e1 AnnAst.EMod
       | Ast.EAdd(e0, e1) => inferArithOp G e0 e1 AnnAst.EAdd
       | Ast.ESub(e0, e1) => inferArithOp G e0 e1 AnnAst.ESub
       | Ast.ELt(e0, e1) => inferNumRel G e0 e1 AnnAst.ELt
       | Ast.ELe(e0, e1) => inferNumRel G e0 e1 AnnAst.ELe
       | Ast.EGt(e0, e1) => inferNumRel G e0 e1 AnnAst.EGt
       | Ast.EGe(e0, e1) => inferNumRel G e0 e1 AnnAst.EGe
       | Ast.EEq(e0, e1) => inferBinRel G e0 e1 AnnAst.EEq
       | Ast.ENeq(e0, e1) => inferBinRel G e0 e1 AnnAst.ENeq
       | Ast.EAnd(e0, e1) => inferBoolOp G e0 e1 AnnAst.EAnd
       | Ast.EOr(e0, e1) => inferBoolOp G e0 e1 AnnAst.EOr
       | Ast.EAsst(x, e) =>
         let
           val ty : AnnAst.typ = lookupEnv G x
           val e' = checkExp G ty e
         in
           AnnAst.EAsst((x, e'), ty)
         end
       | Ast.ECond(e, e0, e1) =>
         let
           val e' = inferExp G e
           val e0' = inferExp G e0
           val e1' = inferExp G e1
         in
           case AnnAst.typeOf e' of
                AnnAst.Tbool =>
                let
                  val ty0' = AnnAst.typeOf e0'
                  val ty1' = AnnAst.typeOf e1'
                in
                  if ty0' = ty1' then AnnAst.ECond((e', e0', e1'), ty0')
                  else raise TypeError
                end
              | _ => raise TypeError
         end
         

  (*  checkExp G ty e = inferExp G e, provided G |- e : ty.
  *
  *   Raises TypeError if there is no tau such that G |- e : tau.
  *)
  and checkExp (G : env) (ty : AnnAst.typ) (e : Ast.exp)  : AnnAst.exp =
  let
    val e = inferExp G e
  in
    if AnnAst.typeOf e = ty then e
    else raise TypeError
  end

  (*  checkExp G ty e = SOME (inferExp G e), if G |- e : ty,
  *                   = NONE, otherwise.
  *)
  and checkExpOpt (G : env) (ty : AnnAst.typ) (e : Ast.exp)  : 
      AnnAst.exp option =
  let
    val e = inferExp G e
  in
    if AnnAst.typeOf e = ty then SOME e
    else NONE
  end

  fun inferExpNoEnv (e : Ast.exp) : AnnAst.exp =
    inferExp [] e

  (*  checkStm G rty s = s', where s' is the annotated statement corresponding
  *   to s.
  *
  *   Raises ReturnError if s is return e and G |- e : rty is false.
  *)
  fun checkStm (G : env) (rty : AnnAst.typ) (s : Ast.stm) : AnnAst.stm =
    case s of
         Ast.SExp(e) => AnnAst.SExp(inferExp G e)
       | Ast.SDecl _ => raise Fail "checkStm not implemented for SDecl."
       | Ast.SInit _ => raise Fail "checkStm not implemented for SInit."
       | Ast.SReturn e =>
         (
           case checkExpOpt G rty e of
                SOME e' => AnnAst.SReturn e'
              | NONE => raise ReturnTypeError
         )
       | Ast.SVReturn =>
         (
           case rty of
                AnnAst.Tvoid => AnnAst.SVReturn
              | _ => raise ReturnTypeError
         )
       | Ast.SDoWhile (s, e) =>
         let
           val s' = checkStm G rty s
           val e' = checkExp G (AnnAst.tyConv Ast.Tbool) e
         in
           AnnAst.SDoWhile(s', e')
         end
       | Ast.SWhile(e, s) =>
         let
           val e' = checkExp G (AnnAst.tyConv Ast.Tbool) e
           val s' = checkStm G rty s
         in
           AnnAst.SWhile(e', s')
         end
       | Ast.SFor ((ty, x, e), e0, e1, s) =>
         let
           val ty' = AnnAst.tyConv ty
           val e' = checkExp G ty' e
           val fr :: G' = G
           val fr' = extendFrame(fr, x, ty')
           val G' = fr' :: G'
           val e0' = inferExp G' e0
           val e1' = inferExp G' e1
           val s' = checkStm G' rty s
         in
           AnnAst.SFor((ty', x, e'), e0', e1', s')
         end
       | Ast.SBlock ss =>
           AnnAst.SBlock (checkStms (M.empty :: G) rty ss)
       | Ast.SIf (e, s) => 
         let
           val e' = checkExp G (AnnAst.tyConv Ast.Tbool) e
           val s' = checkStm G rty s
         in
           AnnAst.SIf(e', s')
         end
       | Ast.SIfElse (e, s0, s1) => 
         let
           val e' = checkExp G (AnnAst.tyConv Ast.Tbool) e
           val s0' = checkStm G rty s0
           val s1' = checkStm G rty s1
         in
           AnnAst.SIfElse(e', s0', s1')
         end

  (*  checkStms G rty ss = ss', where ss' is the annotated sequence of
  *   statements corresponding to ss.
  *)
  and checkStms (G : env) (rty : AnnAst.typ) (ss : Ast.stm list) : 
      AnnAst.stm list =
    case ss of
         [] => []
       | Ast.SDecl(ty, xs) :: ss =>
         let
           val fr :: G' = G
           val ty' = AnnAst.tyConv ty
           val fr' = foldl (fn (y, m) => extendFrame(m, y, ty')) fr xs
         in
           AnnAst.SDecl(ty', xs) :: checkStms (fr' :: G') rty ss
         end
       | Ast.SInit(ty, xes) :: ss =>
         let
           val (xs, es) = ListPair.unzip xes
           val fr :: G' = G
           val ty' = AnnAst.tyConv ty
           val es' = map (checkExp G ty') es
           val fr' = foldl (fn (y, m) => extendFrame(m, y, ty')) fr xs
         in
           AnnAst.SInit(ty', ListPair.zip(xs, es')) :: checkStms (fr' :: G') rty ss
         end
       | s :: ss => checkStm G rty s :: checkStms G rty ss

  fun checkDefs(
      protos : env_frame, 
      defs : env_frame, 
      ds : Ast.def list) : AnnAst.def list =
    case ds of
         [] => []
       | Ast.DFun(rty, id, params, ss) :: ds =>
         let
           val rty' = AnnAst.tyConv rty

           val funType = AnnAst.Tarr(paramTypes params, rty')

           fun doCheck() =
           let
             val defs' = 
               (*
               M.insert(defs, id, AnnAst.Tarr(paramTypes params, rty'))
               *)
               M.insert(defs, id, funType)
             val fr'' = declEnvFrame(params)
             val ss' = checkStms ([fr'', defs', protos]) rty' ss
           in
             AnnAst.DFun(rty', id, AnnAst.paramsConv params, ss') ::
               (checkDefs(protos, defs', ds))
           end
         in
           case M.find(defs, id) of
                SOME _ => raise MultiplyDeclaredError id
              | NONE =>
                  case M.find(protos, id) of
                       SOME ty =>
                         if ty = funType
                         then doCheck()
                         else raise MultiplyDeclaredError id
                     | NONE => doCheck()
         end
       | Ast.DFunProt(rty, id, tys) :: ds =>
         let
           fun doCheck() =
             let
               val rty' = AnnAst.tyConv rty
               val protos' =
                 M.insert(protos, id, AnnAst.Tarr(map AnnAst.tyConv tys, rty'))
             in
               AnnAst.DFunProt(rty', id, map AnnAst.tyConv tys) ::
                 (checkDefs(protos', defs, ds))
             end
         in
           case M.find(protos, id) of
                SOME _ => raise MultiplyDeclaredError id
              | NONE => doCheck()
         end

  fun checkPgm (Ast.PDefs ds : Ast.program) : AnnAst.program =
    AnnAst.PDefs(checkDefs(baseEnv, M.empty, ds))


end
