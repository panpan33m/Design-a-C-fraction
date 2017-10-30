structure IoBase =
struct

  structure T = TextIO
  structure S = T.StreamIO

  val inStream : T.instream ref = ref (T.stdIn)
  val outStream : T.outstream ref = ref (T.stdOut)
  val verbose : bool ref = ref(false)

  fun setIO (ins : T.instream , outs : T.outstream ) : unit =
    (inStream := ins ; outStream := outs)

  fun closeIO () : unit =
  let
    val () = print "Closing streams..."
  in
    (
      print "Closing ins..." ; T.closeIn (!inStream) ; 
      print "Closing outs..." ; T.closeOut (!outStream) ;
      print "Streams closed.\n"
    )
  end

  fun setVerbose (v : bool) : unit =
    verbose := v

  fun readInt () : int =
  let
    val () = 
      if !verbose
      then print "Enter an integer: "
      else ()
  in
    case T.inputLine (!inStream) of
         SOME(line) =>
         (
           valOf(Int.fromString line)
           handle Option =>
             raise Fail (
               "Expected integer, got " ^ 
               (String.substring(line, 0, String.size line - 1)) ^
               "."
             )
         )
       | NONE =>
           raise Fail (
             "Unexpected end-of-stream on input."
           )
  end

  fun printInt (n : int) : unit =
    T.output(!outStream, (Int.toString n) ^ "\n")


  fun readBool () : bool =
  let
    val () = 
      if !verbose
      then print "Enter a bool: "
      else ()
  in
    case T.inputLine (!inStream) of
         SOME(line) =>
         (
           valOf(Bool.fromString line)
           handle Option =>
             raise Fail (
               "Expected bool, got " ^ 
               (String.substring(line, 0, String.size line - 1)) ^
               "."
             )
         )
       | NONE =>
           raise Fail (
             "Unexpected end-of-stream on input."
           )
  end

  fun printBool (x : bool) : unit =
    T.output(!outStream, (Bool.toString x) ^ "\n")

  fun readDouble () : real =
  let
    val () = 
      if !verbose
      then print "Enter an double: "
      else ()
  in
    case T.inputLine (!inStream) of
         SOME(line) =>
         (
           valOf(Real.fromString line)
           handle Option =>
             raise Fail (
               "Expected double, got " ^ 
               (String.substring(line, 0, String.size line - 1)) ^
               "."
             )
         )
       | NONE =>
           raise Fail (
             "Unexpected end-of-stream on input."
           )
  end

  fun printDouble (x : real) : unit =
    T.output(!outStream, (Real.toString x) ^ "\n")

  fun readString () : string =
  let
    val () = 
      if !verbose
      then print "Enter a string: "
      else ()
  in
    case T.inputLine (!inStream) of
         SOME(line) => String.substring(line, 0, String.size line - 1)
       | NONE =>
           raise Fail (
             "Unexpected end-of-stream on input."
           )
  end

  fun printString (x : string) : unit =
    T.output(!outStream, x ^ "\n")

end
