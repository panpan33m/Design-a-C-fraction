(*  COMP 321 Homework 7:  Compiler for a fragment of C.
*
*   N. Danner
*   Fall 2016
*)

(* Celine Tao & Eric Porestsky *)

structure Compile =
struct

  structure A = AnnAst

  structure T = TextIO

  exception Unimplemented

  datatype j_type = J_I | J_D | J_V | J_Z | J_String

  type locs = int Env.env (* Env.pushFrame Env.empty Frame.empty *)
  type nextLoc = int list
  type nextLb = int
  type jfuntyps = j_type * (j_type list) (* return type * arg types *)
  type jfunsig = jfuntyps * (int Frame.frame) * int (* typs, locs, nextLoc *)
  type env = locs * nextLoc * nextLb * (jfunsig Frame.frame)



  (*  compile(p, outs) = ().  As a side-effect, p is compiled to Jasmin
  *   assembly, with the resulting assembly code written to the output
  *   stream outs.  The client is responsible for opening outs before calling
  *   this function and closing it after this function returns.
  *)


  fun mainReturn(ss: A.stm list) : A.stm list =
    case ss of
      [] => ss
      |x::xs => (case x of
                  A.SReturn e => A.SVReturn::mainReturn(xs)
                  | _ => x::mainReturn(xs))


  fun typToJtyp (t : A.typ) : j_type =
      case t of
          A.Tint => J_I
        | A.Tdouble => J_D
        | A.Tstring => J_String
        | A.Tbool => J_Z
        | A.Tarr (ts, t) => raise Unimplemented
        | A.Tvoid => J_V


  fun JtypToStr (jt : j_type) : string =
      case jt of
           J_I => "I"
         | J_D => "D"
         | J_V => "V"
         | J_Z => "Z"
         | J_String => "String"

  fun JtypsToStr (jts : j_type list) : string =
      case jts of
           [] => ""
         | x::xs => (JtypToStr x) ^ (JtypsToStr xs)

  fun jfunTypToStr (jft : jfuntyps) : string =
      let val (jt, jts) = jft
          val jtStr = JtypToStr jt
          val jtsStr = JtypsToStr jts
      in
          "(" ^ jtsStr ^ ")" ^ jtStr
      end

  fun newLabel ((locs, nl, nlb, funsigfr) : env) : string * env =
      ("LBL" ^ (Int.toString nlb) , (locs, nl, nlb+1, funsigfr))

  fun argtypes (pdl : A.paramdecl list) : j_type list =
      case pdl of
          [] => []
        | (t, id) :: tids => typToJtyp t :: (argtypes tids)

  fun getFunTypes (ds : A.def list) : jfuntyps Frame.frame =
      case ds of
           [] => Frame.empty
         | d::defs => case d of
                        A.DFun (t, id, pdl, stms) => Frame.extend ((getFunTypes defs), id, (typToJtyp t, argtypes pdl))
                      | A.DFunProt (t, id, ts) => raise Unimplemented

  fun getFunParamLoc (pdl : A.paramdecl list) (nl : int) (jfsFr : int Frame.frame) : int Frame.frame * int =
         case pdl of
              [] => (jfsFr, nl)
            | (t, id) :: tids => getFunParamLoc tids (nl+1) (Frame.extend (jfsFr, id, nl))

  fun getFunSig (d : A.def) : jfunsig =
      case d of
           A.DFun (t, id, pdl, stms) => let val (fr, i) = getFunParamLoc pdl 0 Frame.empty
                                          val ts = valOf (Frame.lookup((getFunTypes [d]), id) )
                                      in
                                          (ts, fr, i)
                                      end
         | A.DFunProt (t, id, ts) => raise Unimplemented

  fun getFunSigs (ds : A.def list) : jfunsig Frame.frame =
      case ds of
           [] => Frame.empty
         | d::defs =>
            case d of
                A.DFun (t, id, pdl, stms) =>
                  let val jfs = getFunSig d
                  in
                       Frame.extend (getFunSigs defs, id, jfs)
                  end
             | A.DFunProt (t, id, ts) => getFunSigs defs

  fun extendLocalStore ((locs, nl::rest, nlb, funsigfr) : env) (t : A.typ) (ids : A.id list) : env =
      case ids of
           [] => (locs, nl::rest, nlb, funsigfr)
         | i::is => let val locs1 = Env.extend locs i nl
                        val (newlocs, newnl::rest, nlb, funsigfr) = extendLocalStore (locs1, (nl+1)::rest, nlb, funsigfr) t is
                    in
                        case t of
                             A.Tbool => (newlocs, (newnl+1)::rest, nlb, funsigfr)
                           | A.Tint => (newlocs, (newnl+1)::rest, nlb, funsigfr)
                           | A.Tdouble => (newlocs, (newnl+2)::rest, nlb, funsigfr)
                    end

 fun funExtend (ev: env) (pdl: A.paramdecl list) : env =
      case pdl of
        [] => ev
        | (t, id) :: tids => let val updatedEv = extendLocalStore ev t [id] in

              (funExtend updatedEv tids)

        end





  fun compile(p : A.program, outs : T.outstream) : unit =
      let fun emit (s: string) : unit = let val out = T.output (outs, s ^ "\n")
                                        in
                                            T.flushOut outs
                                        end
          fun concatStr (ss: string list) : string = String.concatWith "\n" ss
          fun emitstrs (ss: string list) : unit = emit (concatStr ss)
          fun emitLb (s: string) : unit = emit (s ^ ":")
          fun compileExp (ev: env) (e: A.exp) : env =
              case e of
                  A.EInt n => ev before emit ("ldc " ^ (Int.toString n))
                | A.EDouble x => ev before emit ("ldc2_w " ^ (Real.toString x))
                | A.EString s => raise Unimplemented
                | A.ETrue => ev before emit ("iconst_1")
                | A.EFalse => ev before emit ("iconst_0")
                | A.EId(x, t) => let val (loc, _, _, _) = ev
                                     val xloc = Env.lookup loc x
                                 in
                                   case t of
                                        A.Tint => ev before emit ("iload " ^ (Int.toString xloc))
                                      | A.Tdouble => ev before emit ("dload " ^ (Int.toString xloc))
                                      | A.Tbool => ev before emit ("iload " ^ (Int.toString xloc))
                                 end

                | A.ECall((f, es), t) => let fun compileExps (ev: env) (es: A.exp list) : env =
                                                 case es of
                                                      [] => ev
                                                    | e::exs => compileExps (compileExp ev e) exs
                                             val evArg = compileExps ev es
                                             val () =
                                             (case f of
                                                  "printInt" => emit "invokestatic CSupport/printInt(I)V"
                                                | "printDouble" => emit "invokestatic CSupport/printDouble(D)V"
                                                | "printBool" => emit "invokestatic CSupport/printBool(Z)V"
                                                | "readInt" => emit "invokestatic CSupport/readInt()I"
                                                | "readDouble" => emit "invokestatic CSupport/readDouble()D"
                                                | "readBool" => emit "invokestatic CSupport/readBool()Z"
                                                | _ =>  let val (_,_,_,jfunsigFr) = ev
                                                            val (jfunt,_,_) = valOf (Frame.lookup(jfunsigFr, f))
                                                            val jfuntStr = jfunTypToStr jfunt
                                                        in emit ("invokestatic C/" ^ f ^ jfuntStr) end
                                             )
                                         in evArg
                                         end

                | A.EPostIncr(x, _) => let val (loc, _, _, _) = ev
                                           val xloc = Env.lookup loc x
                                       in ev before emitstrs ([("iload " ^ (Int.toString xloc)),
                                                               ("iinc " ^ (Int.toString xloc) ^ " 1")])
                                       end
                | A.EPostDecr(x, _) => let val (loc, _, _, _) = ev
                                           val xloc = Env.lookup loc x
                                       in ev before emitstrs ([("iload " ^ (Int.toString xloc)),
                                                               ("iinc " ^ (Int.toString xloc) ^ " -1")])
                                       end

                | A.ENot(e, _) => let val en0 = compileExp ev e
                                      val (lbl, en0') = newLabel en0
                                      val (stop, en1) = newLabel en0'
                                      val () = emit ("ifeq " ^ lbl)
                                      val () = emit ("iconst_0")
                                      val () = emit ("goto " ^ stop)
                                      val () = emit (lbl ^ ":")
                                      val () = emit ("iconst_1")
                                      val () = emit (stop ^ ":")
                                      in
                                            en1
                                      end

                | A.EPreIncr(x, _) => let val (loc, _, _, _) = ev
                                          val xloc = Env.lookup loc x
                                      in ev before emitstrs ([("iinc " ^ (Int.toString xloc) ^ " 1"),
                                                              ("iload " ^ (Int.toString xloc))])
                                      end

                | A.EPreDecr(x, _) => let val (loc, _, _, _) = ev
                                          val xloc = Env.lookup loc x
                                      in ev before emitstrs ([("iinc " ^ (Int.toString xloc) ^ " -1"),
                                                              ("iload " ^ (Int.toString xloc))])
                                      end

                | A.EMul((e0, e1), t) => let val en0 = compileExp ev e0
                                             val en1 = compileExp en0 e1 in
                                             (case t of
                                                A.Tint => let val () = emit ("imul") in
                                                                  en1
                                                          end
                                                | _ => let val () = emit("dmul") in
                                                      en1
                                                      end
                                                  )
                                              end

                | A.EDiv((e0, e1), t) => let val en0 = compileExp ev e0
                                             val en1 = compileExp en0 e1 in
                                              (case t of
                                                A.Tint => let val () = emit ("idiv") in
                                                                  en1 end
                                                | _ => let val () = emit("ddiv") in
                                                            en1 end
                                                  )
                                              end

                | A.EMod((e0, e1), t) => let val en0 = compileExp ev e0
                                             val en1 = compileExp en0 e1 in
                                              (case t of
                                                A.Tint => let val () = emit ("irem") in
                                                            en1 end
                                                | _ => let val () = emit("drem") in
                                                          en1 end
                                                  )

                                              end


                | A.EAdd((e0, e1), t) => let val en0 = compileExp ev e0
                                             val en1 = compileExp en0 e1 in
                                              (case t of
                                                A.Tint => let val () = emit ("iadd") in
                                                            en1 end
                                                | _ => let val () = emit("dadd") in
                                                            en1 end
                                                  )
                                              end


                | A.ESub((e0, e1), t) => let val en0 = compileExp ev e0
                                             val en1 = compileExp en0 e1 in
                                              (case t of
                                                A.Tint => let val () = emit ("isub") in
                                                              en1 end
                                                | _ => let val () = emit("dsub") in
                                                          en1 end
                                                  )
                                              end

                | A.ELt((e0, e1), t) => (case A.typeOf(e0) of
                                        A.Tint => let val () = emit "ldc 1"
                                                      val en0 = compileExp ev e0
                                                      val en1 = compileExp en0 e1
                                                      val (lbl, en1') = newLabel en1
                                                      val () = emit ("if_icmplt " ^ lbl)
                                                      val () = emit "pop"
                                                      val () = emit "ldc 0"
                                                      val () = emit (lbl ^ ":")
                                                  in
                                                      en1'
                                                  end
                                      | A.Tdouble =>  let val en0 = compileExp ev e0
                                                          val en1 = compileExp en0 e1
                                                          val (lbl, en1') = newLabel en1
                                                          val (stop, en2) = newLabel en1'
                                                          val () = emit ("dcmpg")
                                                          val () = emit ("iflt " ^ lbl)
                                                          val () = emit ("ldc 0")
                                                          val () = emit ("goto " ^ stop)
                                                          val () = emit (lbl ^ ":")
                                                          val () = emit ("ldc 1")
                                                          val () = emit (stop ^ ":" ) in
                                                              en2
                                                          end)

                | A.ELe((e0, e1), t) => (case A.typeOf(e0) of
                                          A.Tint =>
                                            let val () = emit "ldc 1"
                                               val en0 = compileExp ev e0
                                               val en1 = compileExp en0 e1
                                               val (lbl, en1') = newLabel en1
                                               val () = emit ("if_icmple " ^ lbl)
                                               val () = emit "pop"
                                               val () = emit "ldc 0"
                                               val () = emit (lbl ^ ":")
                                            in
                                               en1'
                                            end
                                         | A.Tdouble =>
                                            let val en0 = compileExp ev e0
                                                val en1 = compileExp en0 e1
                                                val (lbl, en1') = newLabel en1
                                                val (stop, en2) = newLabel en1'
                                                val () = emit ("dcmpg")
                                                val () = emit ("ifgt " ^ lbl)
                                                val () = emit ("ldc 1")
                                                val () = emit ("goto " ^ stop)
                                                val () = emit (lbl ^ ":")
                                                val () = emit ("ldc 0")
                                                val () = emit (stop ^ ":" ) in
                                                    en2
                                            end)

                | A.EGt((e0, e1), t) => (case A.typeOf(e0) of
                                        A.Tint => let val () = emit "ldc 1"
                                                      val en0 = compileExp ev e0
                                                      val en1 = compileExp en0 e1
                                                      val (lbl, en1') = newLabel en1
                                                      val () = emit ("if_icmpgt " ^ lbl)
                                                      val () = emit "pop"
                                                      val () = emit "ldc 0"
                                                      val () = emit (lbl ^ ":")
                                                  in
                                                      en1'
                                                  end
                                      | A.Tdouble =>  let val en0 = compileExp ev e0
                                                          val en1 = compileExp en0 e1
                                                          val (lbl, en1') = newLabel en1
                                                          val (stop, en2) = newLabel en1'
                                                          val () = emit ("dcmpg")
                                                          val () = emit ("ifle " ^ lbl)
                                                          val () = emit ("ldc 1")
                                                          val () = emit ("goto " ^ stop)
                                                          val () = emit (lbl ^ ":")
                                                          val () = emit ("ldc 0")
                                                          val () = emit (stop ^ ":" ) in
                                                              en2
                                                          end)

                | A.EGe((e0, e1), t) => (case A.typeOf(e0) of
                                             A.Tint =>
                                               let
                                                 val () = emit "ldc 1"
                                                 val en0 = compileExp ev e0
                                                 val en1 = compileExp en0 e1
                                                 val (lbl, en1') = newLabel en1
                                                 val () = emit ("if_icmpge " ^ lbl)
                                                 val () = emit "pop"
                                                 val () = emit "ldc 0"
                                                 val () = emit (lbl ^ ":")
                                               in
                                                   en1'
                                               end
                                           | A.Tdouble =>
                                              let val en0 = compileExp ev e0
                                                  val en1 = compileExp en0 e1
                                                  val (lbl, en1') = newLabel en1
                                                  val (stop, en2) = newLabel en1'
                                                  val () = emit ("dcmpg")
                                                  val () = emit ("iflt " ^ lbl)
                                                  val () = emit ("ldc 1")
                                                  val () = emit ("goto " ^ stop)
                                                  val () = emit (lbl ^ ":")
                                                  val () = emit ("ldc 0")
                                                  val () = emit (stop ^ ":" ) in
                                                      en2
                                              end)

                  | A.EEq((e0, e1), t) => (case A.typeOf(e0) of
                                            A.Tint =>
                                              let val () = emit "ldc 1"
                                                  val en0 = compileExp ev e0
                                                  val en1 = compileExp en0 e1
                                                  val (lbl, en1') = newLabel en1
                                                  val () = emit ("if_icmpeq " ^ lbl)
                                                  val () = emit "pop"
                                                  val () = emit "ldc 0"
                                                  val () = emit (lbl ^ ":") in
                                                          en1'
                                              end
                                          | A.Tdouble =>
                                              let
                                                  val en0 = compileExp ev e0
                                                  val en1 = compileExp en0 e1
                                                  val (lbl, en1') = newLabel en1
                                                  val (stop, en2) = newLabel en1'
                                                  val () = emit ("dcmpg")
                                                  val () = emit ("ifeq " ^ lbl)
                                                  val () = emit ("ldc 0")
                                                  val () = emit ("goto " ^ stop)
                                                  val () = emit (lbl ^ ":")
                                                  val () = emit ("ldc 1" )
                                                  val () = emit (stop ^ ":" ) in
                                                        en2
                                              end)

                | A.ENeq((e0, e1), t) => (case A.typeOf(e0) of
                                            A.Tint =>
                                             let val () = emit "ldc 1"
                                                 val en0 = compileExp ev e0
                                                 val en1 = compileExp en0 e1
                                                 val (lbl, en1') = newLabel en1
                                                 val () = emit ("if_icmpne " ^ lbl)
                                                 val () = emit "pop"
                                                 val () = emit "ldc 0"
                                                 val () = emit (lbl ^ ":")
                                             in
                                                 en1'
                                             end
                                         | A.Tdouble =>
                                             let
                                                 val en0 = compileExp ev e0
                                                 val en1 = compileExp en0 e1
                                                 val (lbl, en2) = newLabel en1
                                                 val (stop, en3) = newLabel en2
                                                 val () = emit ("dcmpg")
                                                 val () = emit ("ifeq " ^ lbl)
                                                 val () = emit ("ldc 1")
                                                 val () = emit ("goto " ^ stop)
                                                 val () = emit (lbl ^ ":")
                                                 val () = emit ("ldc 0" )
                                                 val () = emit (stop ^ ":" )
                                             in
                                                en3
                                             end)

                | A.EAnd((e0, e1), _) => let val en0 = compileExp ev e0
                                             val (lbl, en0') = newLabel en0
                                             val () = emit "dup"
                                             val () = emit ("ifeq " ^ lbl)
                                             val () = emit "pop"
                                             val en1 = compileExp en0' e1
                                             val () = emit (lbl ^ ":")
                                         in
                                             en1
                                         end

                | A.EOr((e0, e1), _) => let val en0 = compileExp ev e0
                                            val (lbl, en0') = newLabel en0
                                            val () = emit "dup"
                                            val () = emit "ldc 1"
                                            val () = emit ("if_icmpeq " ^ lbl)
                                            val () = emit "pop"
                                            val en1 = compileExp en0' e1
                                            val () = emit (lbl ^ ":")
                                         in
                                             en1
                                         end

                | A.EAsst((x, e), t) => let val ev0 = compileExp ev e
                                            val (loc0,_,_,_) = ev0
                                            val xloc = Env.lookup loc0 x
                                        in
                                          (case t of
                                                A.Tint => ev0 before
                                                        emitstrs ([("dup"),
                                                                   ("istore " ^ (Int.toString xloc))])
                                              | A.Tbool => ev0 before
                                                        emitstrs ([("dup"),
                                                                   ("istore " ^ (Int.toString xloc))])
                                              | A.Tdouble => ev0 before
                                                           emitstrs ([("dup2"),
                                                                      ("dstore " ^ (Int.toString xloc))]))
                                        end

                | A.ECond((e, e0, e1), _) => let val ev' = compileExp ev e
                                                 val (lbl1, newev) = newLabel ev'
                                                 val () = emit ("ifeq " ^ lbl1)
                                                 val ev0 = compileExp newev e0
                                                 val (lbl2, newev') = newLabel ev0
                                                 val () = emit ("goto " ^ lbl2)
                                                 val () = emit (lbl1 ^ ":")
                                                 val ev1 = compileExp newev' e1
                                                 val () = emit (lbl2 ^ ":")
                                             in
                                                 ev1
                                             end

         fun compileStm (ev : env, s : A.stm) : env =
           case s of
                A.SExp(e) => (case e of
                              A.ECall((f, es), t) =>  (

                                case t of  A.Tvoid =>

                                  (case A.typeOf e of
                                   A.Tdouble => let val ev0 = compileExp ev e
                                                   in ev0
                                                   end
                                 | _ => let val ev0 = compileExp ev e
                                            in ev0
                                            end )


                                | _ => (case A.typeOf e of
                                   A.Tdouble => let val ev0 = compileExp ev e
                                                   val () = emit "pop2"
                                                   in ev0
                                                   end
                                 | _ => let val ev0 = compileExp ev e
                                            val () = emit "pop"
                                            in ev0
                                            end)   )

                              | _ => (case A.typeOf e of
                                   A.Tdouble => let val ev0 = compileExp ev e
                                                   val () = emit "pop2"
                                                   in ev0
                                                   end
                                 | _ => let val ev0 = compileExp ev e
                                            val () = emit "pop"
                                            in ev0
                                            end)                )

              | A.SDecl(ty, xs) => extendLocalStore ev ty xs
              | A.SInit(ty, xses) => (case xses of
                [] => ev
                | (id, e) :: ides => let val ev0 = compileExp ev e
                                         val ev1 = extendLocalStore ev0 ty [id]
                                         val (loc0,_,_,_) = ev1
                                         val xloc = Env.lookup loc0 id
                                         val () = (case A.typeOf e of A.Tdouble => emit "dup2" | _ => emit "dup")
                                         val () = (case A.typeOf e of A.Tdouble => emit ("dstore " ^ (Int.toString xloc)) | _ => emit ("istore " ^ (Int.toString xloc)))
                                           in

                                            (case A.typeOf e of
                                                   A.Tdouble => compileStm(ev1, (A.SInit(ty, ides)))
                                                               before emit "pop2"
                                                 | _ => compileStm(ev1, (A.SInit(ty, ides)))
                                                        before emit "pop"
                                              )

                                         end

                                         )

              | A.SReturn e => (case A.typeOf e of
                                   A.Tdouble => let val ev0 = compileExp ev e
                                                   val () = emit "dreturn"
                                                   in ev0
                                                   end
                                 | _ => let val ev0 = compileExp ev e
                                            val () = emit "ireturn"
                                            in ev0
                                            end)

              | A.SVReturn => ev before emit "return"
              | A.SDoWhile(s, e) => let val (top, ev1) = newLabel ev
                                        val (final, ev1') = newLabel ev1
                                        val () = emit (top ^ ":")
                                        val ev2 = compileStm(ev1', s)
                                        val ev3 = compileExp ev2 e
                                        val () = emit ("ifeq " ^ final)
                                        val () = emit ("goto " ^ top)
                                        val () = emit (final ^ ":")
                                    in ev3
                                    end

              | A.SWhile(e, s) =>  let val (top, ev1) = newLabel ev
                                       val (final, ev1') = newLabel ev1
                                       val () = emit (top ^ ":")
                                       val ev2 = compileExp ev1' e
                                       val () = emit ("ifeq " ^ final)
                                       val ev3 = compileStm(ev2,s)
                                       val () = emit ("goto " ^ top)
                                       val () = emit (final ^ ":")
                                    in
                                          ev3
                                    end

              | A.SFor((ty, x, e), e0, e1, s) => let fun getLocs (ev: env) : int Env.env =
                                                         let val (locs,_,_,_) = ev
                                                         in locs end
                                                     val ev1 = compileExp ev e
                                                     val ev1 = extendLocalStore ev1 ty [x]
                                                     val storeCmd =
                                                        (case ty of
                                                            A.Tint => "istore"
                                                          | A.Tbool => "istore"
                                                          | A.Tdouble => "dstore")
                                                     val () = emit (storeCmd ^ " " ^ (Int.toString (Env.lookup (getLocs ev1) x)))
                                                     val (label, ev2) = newLabel ev1
                                                     val (top, ev3) = newLabel ev2
                                                     val () = emit (top ^ ":")
                                                     val ev4 = (compileExp ev3 e0)
                                                     val () = emit ("ifeq " ^ label)
                                                     val ev5 = (compileStm(ev4, s))
                                                     val ev6 = (compileExp ev5 e1)
                                                     val () = emit "pop"
                                                     val () = emit ("goto " ^ top)
                                                     val () = emit (label ^ ":")
                                                 in
                                                     ev6
                                                 end

              | A.SBlock(ss) => let val (locEnv, nextL, nextB, funs) = ev
                                    val locEnvEmp = (Env.pushFrame locEnv Frame.empty)
                                    val newEv = (locEnvEmp, nextL, nextB, funs)
                                    val (locEnv', nextL', nextB', funs') = (compileStmList newEv ss) in

                                      ((Env.popFrame locEnv'), nextL', nextB', funs')

                end

              | A.SIf(e, s) => let val (lbl, ev1) = newLabel ev
                                   val ev2 = compileExp ev1 e
                                   val () = emit ("ifeq " ^ lbl)
                                   val ev3 = compileStm(ev2, s)
                                   val () = emit (lbl ^ ":")
                               in
                                    ev3
                               end

              | A.SIfElse(e, s0, s1) => let val (tru, ev1) = newLabel ev
                                            val (fals, ev2) = newLabel ev1
                                            val ev3 = compileExp ev2 e
                                            val () = emit ("ifeq " ^ fals)
                                            val ev4 = compileStm(ev3, s0)
                                            val () = emit ("goto " ^ tru)
                                            val () = emit (fals ^ ":")
                                            val ev5 = compileStm(ev4, s1)
                                            val () = emit (tru ^ ":")
                                        in
                                            ev5
                                        end

          and compileStmList (ev : env) (ss: A.stm list) : env =
                case ss of
                    [] => ev
                  | x::xs => let val updatedEv = compileStm(ev, x)
                             in
                                compileStmList updatedEv xs
                             end

          fun compileDef (ev : env) (def : A.def) : env =
              case def of
                  A.DFun (t, id, args, ss) =>
                    let val jt = typToJtyp t
                        val jtStr = JtypToStr jt
                        val tylist = argtypes args
                        val tyStr = JtypsToStr tylist

                        val extendedEv = funExtend ev args

                        val () =
                        (case id of
                             "main" => emit ".method public static main([Ljava/lang/String;)V"
                           | _ => emit (".method public static " ^ id ^ "(" ^ tyStr ^")" ^ jtStr)
                        )
                        val () = emit ".limit locals 1000"
                        val () = emit ".limit stack 1000"

                        val (locEnv, nextL, nextB, funs) = extendedEv
                        val newev = (locEnv, 0::nextL, nextB, funs)
                        val (locEnv, nextL', nextB, funs) = (case id of "main" => compileStmList newev (mainReturn(ss)) | _ => compileStmList newev ss)
                        val (x::xs) = nextL'
                        val finalev = (locEnv, xs, nextB, funs)
                        val () = emit "nop"
                        val () = emit ".end method"
                    in finalev
                    end
                | _ => ev

          fun compileDefs (ev : env) (defs : A.def list) : env =
              case defs of
                   [] => ev
                 | d::ds => let val updated = compileDef ev d in 
                    compileDefs ev ds
                 end

          val () = emitstrs([(".class public C"),
                         (".super java/lang/Object"),
                         (""),
                         (".method public <init>()V"),
                         ("  aload_0"),
                         ("  invokenonvirtual java/lang/Object/<init>()V"),
                         ("  return"),
                         (".end method"),
                         ("")
                       ])

          val A.PDefs ds = p
          val baseEv = ((Env.pushFrame Env.empty Frame.empty),
                        [0],
                        0,
                        getFunSigs ds
                       )
      in
          (let val final = compileDefs baseEv ds in
              ()
          end)
      end

end
