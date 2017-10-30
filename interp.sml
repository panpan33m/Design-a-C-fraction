(*  COMP 321 Homework 6:  Interpreter for a fragment of C.
*   
*   N. Danner
*   Fall 2016
*
*   There are two common approaches to handling global definitions in a program
*   such as we have in this fragment:
*
*   1.  Put the global definitions in a frame at the bottom of the stack.  This
*       makes a lot of sense for typical functional languages, where there is no
*       real distinction between "global" and "local" definitions.
*   2.  Put the global definitions in a separate frame.  This makes more sense
*       for languages where there is a real distinction between global and local
*       definitions.  For example, in C, function definitions can only occur
*       globally.  Therefore it makes more sense to put all function definitions
*       in a separate frame so that when evaluating a function call expression,
*       the interpreter can look up the definition of the function directly in
*       that frame, rather than unwinding the stack of local definitions to get
*       to the bottom, which is the only place it could occur.
*
*   The implementation here takes approach (2).  Notice though that it is a bit
*   of a pain, because *every* execution and evaluation function must take the
*   globals frame as an argument, which just gets passed around and around.
*   Possibly better would be a (structure-)global reference, but we hate using
*   references.
*)

structure Interp =
struct

  structure A = AnnAst
  
  datatype value = VInt of int | VDbl of real | VString of string 
                 | VBool of bool
                 | VFn of (A.typ) * (A.id list) * (A.stm list)
                 | VNone | VNull

  type frame = value Frame.frame
  type env = value Env.env

  exception NoMainError
  exception NoReturnError
  exception UninitializedError
  exception RuntimeTypeError

  fun valueToString (v : value) : string =
    case v of
         VInt n => Int.toString n
       | VDbl x => Real.toString x
       | VString s => s
       | VBool b => Bool.toString b
       | _ => raise Fail "Not implemented"

  (*  globalsFrame ds = the frame consisting of the global definitions in ds.
  *)
  fun globalsFrame (ds : A.def list) : frame =
    case ds of
         [] => Frame.empty
       | A.DFun(rty, f, args, ss) :: ds =>
           Frame.extend (globalsFrame ds, f, VFn(rty, map #2 args, ss))
       | A.DFunProt _ :: ds =>
           globalsFrame ds

  (*  argsFrame fr globals Gamma [x_0,...,x_{n-1}] [e_0,...,e_{n-1}] = 
  *     (fr', Gamma'), where 
  *     - Gamma_{-1} = Gamma
  *     - Gamma_i is the updated environment after evaluating e_i to get v_i.
  *     - Gamma' = Gamma_{n-1}
  *     - fr' is obtained by extending fr with bindings x_i |-> v_i.
  *
  *   In other words, Gamma' is the environment that results after evaluating
  *   each e_i, and fr' is the extension of fr obtained by binding x_i to the
  *   value of e_i.
  *)
  fun argsFrame 
      (fr : frame) 
      (gs : frame) 
      (Gamma : env) 
      (args : A.id list) 
      (es : A.exp list) : frame*env =
    case (args, es) of
         ([], []) => (fr, Gamma)
       | (x :: args, e :: es) =>
         let
           val (v, Gamma') = eval gs Gamma e
         in
           argsFrame (Frame.extend(fr, x, v)) gs Gamma' args es
         end

  (*  evalBinRel gs G e0 e1 rel = (VBool(rel(v0, v1)), G'), where v_i is
  *   the value of e_i and G' is the environment after evaluating
  *   e_0 and e_1.
  *)
  and evalBinRel 
    (gs : frame)
    (Gamma : env) 
    (e0 : A.exp) 
    (e1 : A.exp) 
    (rel : value*value -> bool) : value*env =
  let
    val (x0, Gamma0) = eval gs Gamma e0
    val (x1, Gamma1) = eval gs Gamma0 e1
  in
    (VBool(rel(x0, x1)), Gamma1)
  end

  (*  evalBinOp gs G e0 e1 rator = (rator(v0, v1), G'), where v_i is
  *   the value of e_i and G' is the environment after evaluating
  *   e_0 and e_1.
  *)
  and evalBinOp
      (gs : frame)
      (Gamma : env)
      (e0 : A.exp)
      (e1 : A.exp)
      (rator : value*value -> value) : value*env =
  let
    val (x0, Gamma0) = eval gs Gamma e0
    val (x1, Gamma1) = eval gs Gamma0 e1
  in
    (rator(x0, x1), Gamma1)
  end

  (*  eval gs G e = (v, G'), where v is the value of e under G and G' is the
  *   updated environment after evaluating e under G.
  *)
  and eval (gs : frame) (Gamma : env) (e : A.exp) : value*env =
    case e of
         A.EInt n => (VInt n, Gamma)
       | A.EDouble x => (VDbl x, Gamma)
       | A.EString s => (VString s, Gamma)
       | A.ETrue => (VBool true, Gamma)
       | A.EFalse => (VBool false, Gamma)
       | A.EId(x, _) => 
         let
           val v = Env.lookup Gamma x
         in
           case v of
                VNull => raise UninitializedError
              | _ => (v, Gamma)
         end
       | A.ECall((f, es), _) =>
         let
           (*  doPrint [e] G p prints the value of e using p.  p is intended
           *   to do a case analysis on the value of e to determine the
           *   appropriate IoBase.printXXX function to use.
           *)
           fun doPrint 
               ([e] : AnnAst.exp list) 
               (G : env) 
               (p : value -> unit) : value*env =
           let
             val (v, Gamma') = eval gs Gamma e
           in
             ((p v ; VNone), Gamma')
           end
         in
           case f of
                "readInt" => (VInt(IoBase.readInt()), Gamma)
              | "printInt" => 
                doPrint es Gamma (fn (VInt n) => IoBase.printInt(n))
              | "readDouble" => (VDbl(IoBase.readDouble()), Gamma)
              | "printDouble" => 
                doPrint es Gamma (fn (VDbl x) => IoBase.printDouble(x))
              | "readBool" => (VBool(IoBase.readBool()), Gamma)
              | "printBool" => 
                doPrint es Gamma (fn (VBool t) => IoBase.printBool(t))
              | "readString" => (VString(IoBase.readString()), Gamma)
              | "printString" => 
                doPrint es Gamma (fn (VString s) => IoBase.printString(s))
              | _ =>
                let
                  val VFn(rty, params, ss) = valOf(Frame.lookup (gs, f))
                  val (fr, Gamma') = 
                    argsFrame Frame.empty gs Gamma params es
                in
                  case (rty, execStms gs (Env.pushFrame Env.empty fr) ss) 
                    of
                       (A.Tvoid, (VNone, _)) => (VNone, Gamma')
                     | (_, (VNone, _)) => raise NoReturnError
                     | (_, (v, _)) => (v, Gamma')
                end
         end
       | A.EPostIncr(x, _) =>
         let
           val VInt n = Env.lookup Gamma x
           val Gamma' = Env.update Gamma x (VInt(n+1))
         in
           (VInt n, Gamma')
         end
       | A.EPostDecr(x, _) =>
         let
           val VInt n = Env.lookup Gamma x
           val Gamma' = Env.update Gamma x (VInt(n-1))
         in
           (VInt n, Gamma')
         end
       | A.ENot(e, _) => 
         let
           val (VBool t, Gamma') = eval gs Gamma e
         in
           (VBool (not t), Gamma')
         end
       | A.EPreIncr(x, _) =>
         let
           val VInt n = Env.lookup Gamma x
           val v = VInt (n+1)
           val Gamma' = Env.update Gamma x v
         in
           (v, Gamma')
         end
       | A.EPreDecr(x, _) =>
         let
           val VInt n = Env.lookup Gamma x
           val v = VInt (n-1)
           val Gamma' = Env.update Gamma x v
         in
           (v, Gamma')
         end
       | A.EMul((e0, e1), A.Tint) =>
           evalBinOp gs Gamma e0 e1 (fn (VInt n0, VInt n1) => VInt(n0*n1))
       | A.EDiv((e0, e1), A.Tint) =>
           evalBinOp gs Gamma e0 e1 (fn (VInt n0, VInt n1) => VInt(n0 div n1))
       | A.EMod((e0, e1), A.Tint) =>
           evalBinOp gs Gamma e0 e1 (fn (VInt n0, VInt n1) => VInt(n0 mod n1))
       | A.EAdd((e0, e1), A.Tint) =>
           evalBinOp gs Gamma e0 e1 (fn (VInt n0, VInt n1) => VInt(n0+n1))
       | A.ESub((e0, e1), A.Tint) =>
           evalBinOp gs Gamma e0 e1 (fn (VInt n0, VInt n1) => VInt(n0-n1))
       | A.EMul((e0, e1), A.Tdouble) =>
           evalBinOp gs Gamma e0 e1 (fn (VDbl x0, VDbl x1) => VDbl(x0*x1))
       | A.EDiv((e0, e1), A.Tdouble) =>
           evalBinOp gs Gamma e0 e1 (fn (VDbl x0, VDbl x1) => VDbl(x0/x1))
       | A.EAdd((e0, e1), A.Tdouble) =>
           evalBinOp gs Gamma e0 e1 (fn (VDbl x0, VDbl x1) => VDbl(x0+x1))
       | A.ESub((e0, e1), A.Tdouble) =>
           evalBinOp gs Gamma e0 e1 (fn (VDbl x0, VDbl x1) => VDbl(x0-x1))
       | A.ELt((e0, e1), _) =>
         (
           case A.typeOf e0 of
                A.Tint =>
                  evalBinRel gs Gamma e0 e1 (fn (VInt n0, VInt n1) => n0<n1)
              | A.Tdouble =>
                  evalBinRel gs Gamma e0 e1 (fn (VDbl n0, VDbl n1) => n0<n1)
         )
       | A.ELe((e0, e1), _) =>
         (
           case A.typeOf e0 of
                A.Tint =>
                  evalBinRel gs Gamma e0 e1 (fn (VInt n0, VInt n1) => n0<=n1)
              | A.Tdouble =>
                  evalBinRel gs Gamma e0 e1 (fn (VDbl n0, VDbl n1) => n0<=n1)
         )
       | A.EGt((e0, e1), _) =>
         (
           case A.typeOf e0 of
                A.Tint =>
                  evalBinRel gs Gamma e0 e1 (fn (VInt n0, VInt n1) => n0>n1)
              | A.Tdouble =>
                  evalBinRel gs Gamma e0 e1 (fn (VDbl n0, VDbl n1) => n0>n1)
         )
       | A.EGe((e0, e1), _) =>
         (
           case A.typeOf e0 of
                A.Tint =>
                  evalBinRel gs Gamma e0 e1 (fn (VInt n0, VInt n1) => n0>=n1)
              | A.Tdouble =>
                  evalBinRel gs Gamma e0 e1 (fn (VDbl n0, VDbl n1) => n0>=n1)
         )
       | A.EEq((e0, e1), _) =>
         (
           case A.typeOf e0 of
                A.Tint =>
                  evalBinRel gs Gamma e0 e1 (fn (VInt n0, VInt n1) => n0=n1)
              | A.Tdouble =>
                  evalBinRel gs Gamma e0 e1 
                    (fn (VDbl x0, VDbl x1) => Real.==(x0, x1))
              | A.Tstring =>
                  evalBinRel gs Gamma e0 e1 
                    (fn (VString s0, VString s1) => s0=s1)
              | A.Tbool =>
                  evalBinRel gs Gamma e0 e1 (fn (VBool b0, VBool b1) => b0=b1)
         )
       | A.ENeq((e0, e1), _) =>
         (
           case A.typeOf e0 of
                A.Tint =>
                  evalBinRel gs Gamma e0 e1 (fn (VInt n0, VInt n1) => n0<>n1)
              | A.Tdouble =>
                  evalBinRel gs Gamma e0 e1 
                    (fn (VDbl x0, VDbl x1) => Real.!=(x0, x1))
              | A.Tstring =>
                  evalBinRel gs Gamma e0 e1 
                    (fn (VString s0, VString s1) => s0<>s1)
              | A.Tbool =>
                  evalBinRel gs Gamma e0 e1 (fn (VBool b0, VBool b1) => b0<>b1)
         )
       | A.EAnd((e0, e1), _) =>
           evalBinOp gs Gamma e0 e1 
             (fn (VBool b0, VBool b1) => VBool(b0 andalso b1))
       | A.EOr((e0, e1), _) =>
           evalBinOp gs Gamma e0 e1 
             (fn (VBool b0, VBool b1) => VBool(b0 orelse b1))
        | A.EAsst((x, e), _) =>
          let
            val (v, Gamma') = eval gs Gamma e
            val Gamma'' = Env.update Gamma' x v
          in
            (v, Gamma'')
          end
        | A.ECond((e, e0, e1), _) =>
          let
            val (VBool t, Gamma') = eval gs Gamma e
          in
            if t then eval gs Gamma' e0
            else eval gs Gamma' e1
          end
        | _ => raise RuntimeTypeError

  (*  execStms gs G ss = (v, G'), where v is the value returned by the first
  *   return statement in ss that is executed and G' is the updated environment
  *   after executing ss starting with G.
  *)
  and execStms (gs : frame) (Gamma : env) (ss : A.stm list) : value*env =
    case ss of
         [] => (VNone, Gamma)
       | s :: ss =>
           case execStm gs Gamma s of
                (VNone, Gamma') => execStms gs Gamma' ss
              | (v, Gamma') => (v, Gamma')

  (*  **********
  *   execS* :  execute the corresponding statement with the given globals and
  *   environment, returning the value of the first return statement executed
  *   and the updated environment.
  *)

  and execSDecl (gs : frame) (Gamma : env) (xs : Ast.id list) : value*env =
    (VNone, Env.extends Gamma xs VNull)

  and execSInit 
      (gs : frame) 
      (Gamma : env) 
      (xses : (Ast.id*AnnAst.exp) list) : value*env =
    case xses of
         [] => (VNone, Gamma)
       | (x, e) :: xses =>
         let
           val (v, Gamma') = eval gs Gamma e
           val Gamma'' = Env.extend Gamma' x v
         in
           execSInit gs Gamma'' xses
         end

  and execSDoWhile 
      (gs : frame) (Gamma : env) (e : A.exp) (s : A.stm) : value*env =
  let
    val (v, Gamma') = execStm gs Gamma s
  in
    case v of
         VNone =>
         let
           val (VBool t, Gamma'') = eval gs Gamma' e
         in
           case t of
                true => execSDoWhile gs Gamma'' e s
              | false => (v, Gamma'')
         end
       | _ => (v, Gamma')
  end

  and execSWhile 
      (gs : frame) (Gamma : env) (e : A.exp) (s : A.stm) : value*env =
    case eval gs Gamma e of
         (VBool true , Gamma') =>
         (
           case execStm gs Gamma' s of
                (VNone, Gamma'') => execSWhile gs Gamma'' e s
              | (v, Gamma'') => (v, Gamma'')
         )
       | (VBool false, Gamma') => (VNone, Gamma')

  and execSFor 
      (gs : frame) 
      (Gamma : env) 
      (x : A.id) 
      (e : A.exp) 
      (e0 : A.exp) 
      (e1 : A.exp)
      (s : A.stm) : value*env =
  let
    val (v, Gamma') = eval gs Gamma e
    val Gamma'' = Env.pushFrame Gamma' (Frame.extend(Frame.empty, x, v))

    fun doLoop (Gamma : env) : value*env =
      case eval gs Gamma e0 of
           (VBool true, Gamma') =>
           let
             val (v, Gamma'') = execStm gs Gamma' s
             val (_, Gamma''') = eval gs Gamma'' e1
           in
             doLoop Gamma'''
           end
         | (VBool false, Gamma') => (VNone, Gamma')

    val (v, fr :: Gamma''') = doLoop Gamma''
  in
    (v, Gamma''')
  end

  and execSIf (gs : frame) (Gamma : env) (e : A.exp) (s : A.stm) : value*env =
    case eval gs Gamma e of
         (VBool true, Gamma') => execStm gs Gamma' s
       | (VBool false, Gamma') => (VNone, Gamma')
       | _ => raise RuntimeTypeError

  and execSIfElse 
      (gs : frame) (Gamma : env) (e : A.exp) (s0 : A.stm) (s1 : A.stm) : 
      value*env =
    case eval gs Gamma e of
         (VBool true, Gamma') => execStm gs Gamma' s0
       | (VBool false, Gamma') => execStm gs Gamma' s1
       | _ => raise RuntimeTypeError

  and execSBlock (gs : frame) (Gamma : env) (ss : A.stm list) : value*env =
  let
    val Gamma' = Env.pushFrame Gamma Frame.empty
    val (v, Gamma'') = execStms gs Gamma' ss
  in
    (v, Env.popFrame Gamma'')
  end

  (*  execStm gs G s = (v, G'), where v is the value returned by the first
  *   return statement executed in s under gs and G, and G' is the updated
  *   environment.
  *)
  and execStm (gs : frame) (Gamma : env) (s : A.stm) : value*env =
    case s of
         A.SExp(e) => (VNone, #2(eval gs Gamma e))
       | A.SDecl(ty, xs) => execSDecl gs Gamma xs 
       | A.SInit(ty, xses) => execSInit gs Gamma xses
       | A.SReturn e => eval gs Gamma e
       | A.SVReturn => (VNone, Gamma)
       | A.SDoWhile(s, e) => execSDoWhile gs Gamma e s
       | A.SWhile(e, s) => execSWhile gs Gamma e s
       | A.SFor((ty, x, e), e0, e1, s) => execSFor gs Gamma x e e0 e1 s
       | A.SBlock(ss) => execSBlock gs Gamma ss
       | A.SIf(e, s) => execSIf gs Gamma e s
       | A.SIfElse(e, s0, s1) => execSIfElse gs Gamma e s0 s1

  (*  evalNoEnv e = v, where v is the value of e evaluated with no globals and
  *   the empty environment.
  *)
  fun evalNoEnv (e : A.exp) : value =
  let
    val (v, _) = eval (Frame.empty : frame) Env.empty e
  in
    v
  end

  (*  exec p = n, where n is the int value returned by the main function in p.
  *)
  fun exec(p : A.program) : int =
  let
    val A.PDefs ds = p
    val globals = globalsFrame ds

    fun execMain() : int =
    let
      val VFn(rty, params, ss) = valOf(Frame.lookup (globals, "main"))
    in
      case execStms globals (Env.pushFrame Env.empty Frame.empty) ss of
           (VInt n, _) => n
         | _ => raise NoReturnError
    end
    handle Option => raise NoMainError

  in
    execMain()
  end

end
