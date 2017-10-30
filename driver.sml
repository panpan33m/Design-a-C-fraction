(*  COMP 321 homework 7:  CPP driver.
*   
*   Upon building this driver, there are several ways of executing it from
*   the shell.  
*
*   - To lex a program that is in file f and print the resulting tokens to the
*     screen:
*
*       $ ./driver lex f
*
*   - To parse a program that is in file f and print the resulting
*     Ast.program value to the screen (using Ast.programToString):
*
*       $ ./driver parse f
*
*   - To type-check a program that is in file f and print the resulting
*     annotated abstract syntax tree to the screen (using
*     AnnAst.programToString):
*
*       $ ./driver check f
*
*   - To execute a program that is in file f:
*
*       $ ./driver exec f
*
*     Each time a readXXX function is called in the program, the program will
*     read a line from standard input, and each time a printXXX function is
*     called in the program, the result will be printed to standard output.
*
*   - To compile a program that is in file f.cc to Jasmin assembly:
*
*       $ ./driver compile f.cc
*
*     This will produce a Jasmin assembly code file f.j in the same directory as
*     f.cc.  To compile f.j to a Java class file:
*
*       $ java -jar jasmin.jar f.j
*
*     This will produce a class file named C.class, provided f.j is assembly
*     that defines a class named C.  To run the class file on the JVM:
*
*       $ java C
*
*     You must run this command in a directory that has both C.class and
*     CSupport.class.
*
*   - Options:
*
*       --expr:  the contents of f are an expression, not a program.
*       --arg:   the argument is the program itself or the expression itself,
*                rather than the name of a file with the program/expression.
*
*   N. Danner
*)

structure Driver =
struct

  structure Lex = CPPLexer
  structure Toks = CPPGrmTokens
  structure P = CPPGrmParseFn(Lex)

  structure T = TextIO

  (*  printnl s = ().
  *
  *   As a side-effect, s will be printed to the terminal followed by a newline.
  *)
  fun printnl(s : string) : unit =
    print (String.concat [s, "\n"])

  fun printssnl(ss : string list) : unit =
    printnl (String.concatWith " " ss)

  fun tokensToString strm =
  let
    val sm = AntlrStreamPos.mkSourcemap()
    val lex = Lex.lex sm

    fun tokensToList (strm : Lex.strm) =
      case lex strm of
           (Toks.EOF, _, _) => [Toks.EOF]
         | (t, _, strm) => t :: tokensToList strm
  in
    String.concatWith " " (map Toks.toString (tokensToList strm))
  end

  (*  parse parser strm = ().  Parses strm using the function parse,
  *   which ought to be either P.parse or P.parseE, where E is an entry point
  *   to the parser specifed in an %entry directive.
  *)
  fun parse parser strm =
  let
    val sm = AntlrStreamPos.mkSourcemap()
    val lex = Lex.lex sm

    (*  e : AsToks.exp option is the expression that could be parsed from strm.
    *   strm : Lex.strm is the rest of the stream after the parse.
    *   repairs is the list of repairs to the stream made by the parser
    *     in order to successfully parse.
    *
    *   For us:  a parse is only successful if e = SOME e' and repairs = [].
    *)
    val (e, strm, repairs) = parser lex strm
  in
    case (repairs, lex strm, e) of
         ([], (Toks.EOF, _, _), SOME e') => e'
       | ([], (Toks.EOF, _, _), NONE) =>
           raise Fail "Parse result:  NONE."
       | ([], (_, _, _), _) =>
           raise Fail "Extra tokens!"
       | (_, _, _) =>
           raise Fail (String.concatWith "\n" [
             "********* Parser reports errors *********",
             String.concatWith "\n" (
               map (AntlrRepair.repairToString Toks.toString sm) repairs
             ),
             "*****************************************"
           ])
  end


  structure M = SplayMapFn(
    struct type ord_key = string val compare = String.compare end : ORD_KEY)

  exception doUsage
  val usage = String.concatWith "\n" [
    "driver cmd [--expr] [--arg] s",
    "",
    "Process the file s according to cmd.  Possible values of cmd are:",
    "\tlex:      perform lexical analysis and print the token sequence.",
    "\tparse:    parse and print the abstract syntax tree.",
    "\tcheck:    type-check and print the annotated abstract syntax tree.",
    "\texec:     execute the program using standard input and output.",
    "\tcompile:  compile the program to Jasmin assembly.",
    "",
    "Options:",
    "\t--expr:  s specifies an expression, not a program",
    "\t--arg:   process s itself; i.e., s does not name a file to read",
    "\n"
  ]

  fun main(arg0 : string, argv : string list) : int =
  let

    fun compile (filename, strm) =
    let
      val dir = OS.Path.dir filename
      val fileBase = OS.Path.base filename
      val jFile = OS.Path.joinBaseExt {base=fileBase, ext=SOME "j"}
      val outs = T.openOut jFile
    in
      (
        Compile.compile(
          (Typing.checkPgm o (parse P.parse)) strm,
          outs
        ) ;
        T.closeOut outs ;
        "Compilation successful"
      )
      handle e =>
        String.concatWith " " ["Compilation raised exception: ", exnMessage e]
    end

    val pgmHandlers = [
      ("lex", tokensToString o #2),
      ("parse", Ast.programToString o (parse P.parse) o #2),
      ("check", 
        AnnAst.programToString o Typing.checkPgm o (parse P.parse) o #2),
      ("exec", 
        Int.toString o Interp.exec o Typing.checkPgm o (parse P.parse) o #2),
      ("compile", compile)
    ]

    val expHandlers = [
      ("lex", tokensToString o #2),
      ("parse", Ast.expToString o (parse P.parseexp) o #2),
      ("check", AnnAst.expToString o Typing.inferExpNoEnv o (parse P.parseexp) o
      #2),
      ("exec", Interp.valueToString o Interp.evalNoEnv o Typing.inferExpNoEnv o
        (parse P.parseexp) o #2),
      ("compile",
        fn _ => raise Fail "Compilation not supported for expressions.")
    ]

    val makeHandlerMap =
      foldr (fn ((cmd, hndlr), m) => M.insert(m, cmd, hndlr)) M.empty

    val pgmHandlerMap = makeHandlerMap pgmHandlers
    val expHandlerMap = makeHandlerMap expHandlers

    val streamFromFile = (Lex.streamifyInstream o TextIO.openIn)
    val streamFromString = (Lex.streamifyInstream o TextIO.openString)

    val stream = ref (streamFromFile)
    val handlerMap = ref(pgmHandlerMap)

    (*  handleOpt : handle a single option by setting stream or parser
    *   appropriately.
    *
    *   Pre-condition:  oa = "--" ^ oa'.
    *)
    fun handleOpt (oa : string) : unit =
    let
    in
      case String.substring(oa, 2, String.size oa - 2) of
           "arg" => stream := streamFromString
         | "expr" => handlerMap := expHandlerMap
         | _ => raise doUsage
    end

    (*  handleOpts : handle all options by calling handleOpt o for each option o
    *   on the command line.
    *)
    fun handleOpts (optsargs : string list) : string list =
    let
    in
      case optsargs of
           [] => []
         | oa :: oas =>
             if String.isPrefix "--" oa then (handleOpt oa ; handleOpts oas)
             else oa :: oas
    end

    val cmd :: optsArgs = argv

    val [arg] = handleOpts optsArgs

    val hndlr = valOf(M.find(!handlerMap, cmd))

    val res = hndlr (arg, !stream arg)

  in
    (printnl res ; 0)
  end
  handle 
    (* Usage errors *)
      doUsage => (print usage ; 1)
    | Bind => (print usage ; 1)
    | Option => (print usage ; 1)
    (* I/O errors *)
    | e as IO.Io {name=name, function=_, cause=cause} => 
        (printnl (String.concatWith " " [
          "I/O error reading",
          name,
          "(",
          exnMessage cause,
          ")"
        ]) ; 1)
    (* Typing errors *)
    | Typing.TypeError =>
        (printnl (String.concatWith " " [
          "Type-checker reports a type error."
        ]) ; 1)
    | Typing.ReturnTypeError =>
        (printnl (String.concatWith " " [
          "Function returns a value of incorrect type."
        ]) ; 1)
    | Typing.UndeclaredError id =>
        (printnl (String.concatWith " " [
          "Undeclared variable", id
        ]) ; 1)
    | Typing.MultiplyDeclaredError id =>
        (printnl (String.concatWith " " [
          "Multiply-declared variable or function", id
        ]) ; 1)
    (* Everything else *)
    | e => (printnl (String.concatWith " " ["Exception: ", exnMessage e]) ; 1)

end
