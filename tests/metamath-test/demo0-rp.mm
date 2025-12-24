$( This is the Metamath database demo0-rp.mm. It is mangled. $)

$( The database demo0.mm was created by Norman Megill. $)

$( !
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
  Metamath source file demo0.mm
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#

                           ~~ PUBLIC DOMAIN ~~
This work is waived of all rights, including copyright, according to the CC0
Public Domain Dedication.  https://creativecommons.org/publicdomain/zero/1.0/

Norman Megill - https://us.metamath.org

$)


$(
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
  demo0.mm: An introductory formal system example
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#

  This file is the introductory formal system example described in Chapter 2 of
  the Metamath book.

$)

$( Declare the constant symbols we will use. $)
  $c 0 + = -> ( ) term wff |- $.

$( Declare the metavariables we will use. $)
  $v t r s P Q $.

$( Specify properties of the metavariables. $)
  tt $f term t $.
  tr $f term r $.
  ts $f term s $.
  wp $f wff P $.

  ${
    min $e |- P $.
    wq.mp $f wff Q $.
    maj $e |- ( P -> Q ) $.
    $( Define the modus ponens inference rule. $)
    mp $a |- Q $.
  $}

  wq $f wff Q $.

  $( Define "term" (part 1 of 2). $)
  tze $a term 0 $.

  $( Define "term" (part 2 of 2). $)
  tpl $a term ( t + r ) $.

  $( Define "wff" (part 1 of 2). $)
  weq $a wff t = r $.

  $( Define "wff" (part 2 of 2). $)
  wim $a wff ( P -> Q ) $.

  $( State Axiom ~ a1 . $)
  a1 $a |- ( t = r -> ( t = s -> r = s ) ) $.

  $( State Axiom ~ a2 . $)
  a2 $a |- ( t + 0 ) = t $.

  $( Prove a theorem.  (Contributed by NM, 1-Jan-2004.) $)
  th1 $p |- t = t $=
  $( Here is its proof: $)
    tt tze tpl tt weq
    tt a2
    tt tt weq
    tt tze tpl tt weq
    tt a2 $( |- ( t + 0 ) = t $)
    tt tze tpl tt weq tt tt weq wim
    tt tze tpl tt tt a1 $( |- ( ( t + 0 ) = t -> ( ( t + 0 ) = t -> t = t ) ) $)
    mp
    mp
    $.
