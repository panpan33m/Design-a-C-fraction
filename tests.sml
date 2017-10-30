(*  Tests for COMP 321 Homework 6:  interpreter for a fragment of C
*
*   N. Danner
*   Fall 2016
*)

structure Tests =
struct

  structure U = UnitTest
  structure TR = TestRunner

  structure CPPParser = CPPGrmParseFn(CPPLexer)
  structure Tok = CPPGrmTokens

  structure T = TextIO

  exception BadParse of string

  val jasminJar = "jasmin.jar"

  fun parse filename =
  let
    val sm = AntlrStreamPos.mkSourcemap()
    val lex = CPPLexer.lex sm
    val ins = TextIO.openIn filename
    val strm = CPPLexer.streamifyInstream ins
    val (e, strm, repairs) = CPPParser.parse lex strm
  in
    case (repairs, lex strm, e) before TextIO.closeIn ins of
         ([], (Tok.EOF, _, _), SOME e') => e'
       | ([], (Tok.EOF, _, _), NONE) => raise BadParse "parse returns NONE"
       | ([], (_, _, _), _) => raise BadParse "extra tokens after parse"
       | (_, _, _) => raise BadParse "parse makes repairs"
  end

  (*  checkCompilePgm f = t, where t is a test that succeeds if 
  *   Interp.exec p produces the output in f ^ ".output" when it is
  *   given input  in f ^ ".input".  
  *
  *   Side-effect:  output of p is in f ^ ".results".
  *
  *   See assignment description for details.
  *)
  fun checkCompileAssmExecPgm (filename : string) : U.test =
  let
    val dir = OS.Path.dir filename
    val fileBase = OS.Path.base filename
    val jFile = OS.Path.joinBaseExt {base=fileBase, ext=SOME "j"}

    val fileIn = filename ^ ".input"
    val fileOut = filename ^ ".results"
    val fileExp = filename ^ ".output"

    fun readFile(filename : string) : string =
    let
      val ins = T.openIn filename
      val s = Substring.string (
        Substring.dropr Char.isSpace (Substring.full (T.inputAll ins))
      )
      val () = T.closeIn ins
    in
      s
    end

    fun testCompile() : unit =
    let
      val outs = T.openOut jFile
    in
      (
        Compile.compile (Typing.checkPgm (parse filename), outs) ;
        T.closeOut outs
      )
    end

    fun testAssm() : int =
    let
      val assembleCmd = String.concatWith " " [
        "java -jar " ^ jasminJar,
        "-d",
        dir,
        jFile,
        " >/dev/null"
      ]
    in
      OS.Process.system assembleCmd
    end

    fun testExecute() : string =
    let

      val runCmd = String.concatWith " " [
        "java -classpath",
        dir,
        "C",
        "<",
        fileIn,
        ">",
        fileOut
      ]
      val _ = OS.Process.system runCmd

      val res = 
        implode (
          map
            (fn c => if c = #"-" then #"~" else c) (explode (readFile fileOut))
        )
    in
      res
    end

    val exp = readFile fileExp
  in
    U.seqTest (filename, [
      U.doIt (filename ^ "(compiles)", testCompile),
      U.assertEqInt (filename ^ "(assembles)", testAssm, 0),
      U.assertEqStr (filename ^ "(executes correctly)", testExecute, exp)
    ])
  end

  (*  cFiles d = a list of all files with suffix .cc contained in
  *   any recursive subdirectory of d.
  *)
  fun cFiles (d : string)  : string list =
  let
    val ds : OS.FileSys.dirstream = OS.FileSys.openDir d

    fun files (curdir : string) (ds : OS.FileSys.dirstream) : string list =
    let
    in
      case OS.FileSys.readDir ds of
           NONE => []
         | SOME f =>
             let
               val full_f = curdir ^ "/" ^ f
             in
               if OS.FileSys.isDir full_f 
               then (cFiles full_f) @ (files curdir ds)
               else full_f :: (files curdir ds)
             end
    end
  in
    List.filter (String.isSuffix ".cc") (files d ds)
  end
  handle SysErr => []

  fun checkGoodProgramTests () =
    ("Check program compilation/assembly/execution", 
    map 
      checkCompileAssmExecPgm (cFiles "testfiles/good"))

  fun allTests () = [
    checkGoodProgramTests()
  ]

  fun printnl (s : string) : unit =
    print (s ^ "\n")

  fun main(arg0 : string, argv : string list) : int =
  let
    val _ = TR.runTimedTestSuites (allTests (), 60, true)
  in
    0
  end
  handle e => (printnl (exnMessage e) ; 1)


  fun runTests() = main("", [])

end
