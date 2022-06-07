module Agda.Compiler.FLib where
{-# LANGUAGE QuasiQuotes #-}
import Text.RawString.QQ

getFLib :: String
getFLib = [r|variable MAXNUM 100000000000000 MAXNUM !
variable ENDFLAG 1234 ENDFLAG !

: -= 1 - ;

: += 1 + ;

: .N ( x1 x2 .. xn n -- )
    0 do
        . 
    loop
;

: dropN ( x1 x2 .. xn n -- )
    0 do
        drop
    loop
;

: TRecurse 
    POSTPONE AGAIN
    POSTPONE THEN
; immediate

: printType ( o1 -- )
    dup MAXNUM @ <
    if .
    else @ 1 cells + @ execute
    then
;

: ordering 
    1 2 3
    cr ." with a stack of " .s
    cr ." and local bindings of { a b c }... "
    { a b c }
    cr ." a =  " a . ." , b = " b . ." , c = " c .
    cr ." so the rightmost local binding will correspond to the top of the stack! "
    cr ." the pass function passes arguments in reverse order, the first value that is passed will always be at the top of the stack at the start of the function! "
;

: fillArray ( xn .. x2 x1 addr n -- )
    0 do
        dup rot rot i cells + !
    loop drop
;

: fillHere ( ENDFLAG xn .. x2 x1 -- )
    BEGIN
    ,
    dup ENDFLAG = if
        ,
        exit
    then
    AGAIN
;

: pushArrayN { addr n -- xn .. x2 x1 }
    n 0 > if n 0 do
        addr i cells + @
    loop
    then
;

: pushArray { addr -- xn .. x2 x1 ENDFLAG }
    ENDFLAG
    0
    BEGIN
    addr 1 pick cells + @
    dup ENDFLAG = if
        2drop
        EXIT
    then
    swap 1 +
    AGAIN
;

: reverse { addr n -- }
    cr ." addr= " addr . ." , n= " n . cr
    .s cr
    0 begin             ( 0 -- )
    .s
    dup addr swap       ( i addr i -- )
    cells + @ >r        ( i -- )
    ." >r ->  " r@ . cr
    += dup n =
    until               ( i -- )
    . cr
    0 begin             ( 0 -- )
    .s cr
    dup r> addr rot       ( i x addr i -- )
    cells + !        ( i -- )
    dup += swap n =
    until               ( i -- )
    drop
;

: printArrayN ( addr n -- )
    0 do
    dup i cells + ?
    loop
    drop
;

: printArray ( addr -- )
    { addr }
    0
    cr ." [ "
    BEGIN
    addr 1 pick cells + @
    dup ENDFLAG = if
        ." ] " cr
        2drop
        EXIT
    then
    . ." , "
    1 +
    AGAIN
;

: map ( xt addr len -- )
    0 do    \ using the len already on the stack, we now create the for loop
            \ if we want to execute this loop without as normal, 
            \ nothing should be added to the stack by the end of the iteration
        2dup  ( xt addr xt addr -- )
        i cells + @ ( xt addr xt addr addr[i] -- )
        swap execute .
    loop 2drop
;

defer passMany


: curry ( x xt1 -- xt2 )
    swap 2>r 
    :noname r> postpone literal r> compile, postpone ; 
;

variable THUNK 1 cells allot 2 thunk !
variable RESULT 1 cells allot 2 thunk !

: isThunk ( o1 -- 0/-1 )
    dup MAXNUM @ < 0 =
    if
        @ THUNK =
    else
        drop 0
    then
;

: isResult
    dup MAXNUM @ < 0 =
    if
        @ RESULT =
    else
        drop 0
    then
;


: makeTHUNK ( xt -- [THUNK xt] )
    dup isThunk
    1 pick isResult +
    0 = if
    thunk here 2 fillArray
    here 
    2 cells allot 
    then
;
:noname ." T: " ; THUNK 1 cells + !

: makeRESULT ( val -- [RESULT val] )
    result here 2 fillArray
    here 
    2 cells allot 
;
:noname ." R: " ; RESULT 1 cells + !

: toResult ( [THUNK val] -- [RESULT val] )
    dup result swap !
;

: shallowPrint { o1 }
    ." ("
    o1 MAXNUM @ <
    if o1 .
    else
        o1 ENDFLAG = if
            ." ENDFLAG??!?! "
        else
        o1 isThunk if
            ." THUNK"
        else o1 isResult if
            ." RES: "
            o1 1 cells + @ recurse
        else
            o1 @ 1 cells + @ 
            execute
            o1 @ @ 1 >
            if
                o1 @ @ 1 do
                    o1 i cells + @
                    recurse
                loop
            then
        then
        then
        then
    then
        ." )"
;

variable target

variable 2InARow
0 2InARow !

variable printer


: dethunk ( o1 -- o11 )
    \ cr ." actually called "
    BEGIN
    \ cr ." dethunking... " dup printType
    dup MAXNUM @ < if   ( o1 )
        EXIT            ( -- o1 )
    then
    dup isThunk 0 =   ( o1 0/-1 )
    1 pick isResult 0 = ( o1 0/-1 0/-1)
    * if    ( o1 )
        \ ." found " dup printType cr
        \ dup shallowPrint cr
        EXIT                ( -- o1 )
    then
    dup @ THUNK = if          ( o1 )
        dup 1 cells + @         ( o1 [addr o11] )
        \ cr .s
        ENDFLAG swap
        \ cr ." executing... " .s
        execute                 ( o1 o11 )
        \ cr ." passing many... " .s
        passMany
        \ cr .s
        \ cr ." done! "
        \ recurse                     ( o1 o11 )
        swap dup                    ( o11 o1 )
        \ cr dup printType
        RESULT swap !               ( o11 o1 )
        \ cr ." set to result! "
        1 pick swap                 ( o11 o11 o1 )
        1 cells + !                 ( o11 )
        \ ." dethunked to " dup printType cr
    else
        \ ." already dethunked! " dup printType cr
        1 cells + @
    then
    AGAIN
;

: deepDethunk ( [THUNK o1] -- o1 )
    \ cr ." deepdethunk " cr
    BEGIN
    \ dup printType
    dethunk                     ( o1 )
    \ ." ??? " cr
    \ ." -> " o1 printType cr
    dup MAXNUM @ < 0 =          ( o1 0/-1 )
    if
        dup @ THUNK = 0 =   ( o1 0/-1 )
        1 pick @ RESULT = 0 = ( o1 0/-1 0/-1)
        * if            ( o1 )
            dup @ @ 1 >                 ( o1 0/-1 )
            if                          ( o1 )
                dup @ @ 1 do                ( o1 )
                    dup i cells + @ recurse     ( o1 o1[i] )
                    1 pick i cells + !          ( o1 )
                loop
            then
            \ ." deepdethunked to: "
            \ dup printer @ execute cr
            EXIT
        then
    else EXIT
    then
    AGAIN
;


: pushThunks { o1 } ( o1 -- o2 o3 .. on )
    \ ." RETURN STACK!!!!!!!!!!!!!!!! " CR .RETURNSTACK cr cr 
    o1 MAXNUM @ < 0 =
    if
        o1 @ THUNK = if
            \ ." pushed thunk " cr
            o1
        else
            o1 @ @ 1 >
            if
                o1 @ @ 1 do
                    \ ." recursing "
                    o1 i cells + @ recurse
                loop
            then
        then
        \ ." returning " cr
    then
;

: deepDethunk2 ( [THUNK o1] -- o1 )
    begin
    dup isThunk while
        dethunk
    repeat
;

: pass ( x [THUNK xt1] -- [THUNK xt2] ) 
    dup @               ( x [THUNK xt] [T:] )
    THUNK = if          ( x [THUNK xt] )
        \ dup 1 cells + @     ( x [THUNK xt] xt )
        \ 2 pick swap         ( x [THUNK xt] x xt )
        \ curry               ( x [THUNK xt] xt2 )
        \ cr ." passed?" 
        tuck tuck 1 cells + @ curry
        swap 1 cells + !
    else
        \ ." trying to pass to an already evaluated thunk " cr
        \ ." or perhaps not even a thunk at all! " cr
        swap drop
    then
;

:noname ( ENDFLAG xn .. x2 x1 [THUNK xt1] -- [THUNK xt2])
    \ cr .s
    BEGIN
    swap
    \ cr ." passing "
    dup ENDFLAG = if
        drop
        EXIT
    then
    swap pass
    AGAIN

; is passMany


: foldThunks ( addr - THUNK )
    \ cr ." folding thunks... " .s
    pushArray       ( xn .. x2 x1 ENDFLAG )
    makeTHUNK       ( [THUNK xn] .. x2 x1 ENDFLAG)
    BEGIN
    swap            ( xn-1 [THUNK xn] .. x2 x1 ENDFLAG )
    dup ENDFLAG = if 
        drop        ( [THUNK xn] )
        \ cr ." folded thunks " .s
        EXIT
    then
    makeTHUNK pass
    AGAIN
;

variable WILDCARD 1 cells allot
: makeWILDCARD wildcard here 1 fillArray here 1 cells allot ;
:noname ." WILDCARD " ; WILDCARD 1 cells + !


: isType  ( obj type -- 0/-1 )
    swap @ =
;

variable wildcards 10 cells allot
variable pointer

: print { o1 }
    ." ("
    o1 MAXNUM @ <
    if o1 .
    else
        o1 dethunk drop
        o1 @ 1 cells + @ execute
        o1 @ @ 1 >
        if
            o1 @ @ 1 do
                o1 i cells + @
                recurse
            loop
        then
    then
        ." )"
;

' print printer !

: thunklessPrint { o1 }
    ." ("
    o1 MAXNUM @ <
    if o1 .
    else
        o1 dethunk drop
        o1 THUNK = 0 = if
            o1 @ 1 cells + @ execute
        then
        o1 @ @ 1 >
        if
            o1 @ @ 1 do
                o1 i cells + @
                recurse
            loop
        then
    then
        ." )"
;


defer obj=?

: obj= ( o1 o2 -- 0/-1 )
    \ cr ." obj= "
    \ cr ." comparing o1 and o2. " \ cr ." o1 = " swap dup . dup shallowprint \ cr ." o2 = " swap dup . dup shallowprint
    \ \ cr .s
    dup MAXNUM @ >          ( o1 o2 0/-1 )
    if                      ( o1 o2 )
        \ cr ." o2 is not a literal "
        dup @ WILDCARD =        ( o1 o2 0\-1 )
        if                      ( o1 o2 )
            \ cr ." o2 is a wildcard "
            drop                            ( o1 )
            wildcards pointer @ cells + !   ( )
            pointer @ 1 + pointer !
            -1                              ( -1 )
            EXIT
        then
    then
    \ \ cr ." o2 is not a wildcard " \ cr .s
    swap dup MAXNUM @ >     ( o2 o1 0/-1 )
    if                      ( o2 o1 )
        \ cr ." o1 is not a literal "
        dup @ WILDCARD =        ( o2 o1 0/-1)
        if                      ( o2 o1 )
            \ cr ." o1 is a wildcard "
            drop                            ( o2 )
            wildcards pointer @ cells + !   ( )
            pointer @ 1 + pointer !
            -1                              ( -1 )
            EXIT
        then                    ( o1 o2 )
    then                    ( o1 o2 )
        \ ." ------------- " \ cr
        deepdethunk                                ( o1 o22 )
        \ dethunk                                ( o1 o22 )
        \ dup shallowPrint \ cr
        \ ." ------------- " \ cr
        swap deepdethunk                           ( o22 o11 )
        \ swap dethunk                           ( o22 o11 )
        \ cr ." post dethunk, "
        \ cr ." o1 = " swap dup shallowprint \ cr ." o2 = " swap dup shallowprint \ cr .s
        \ cr ." dethunked both " .s
        dup MAXNUM @ <  ( o22 o11 0/-1 )
        rot             ( o11 0/-1 o22 )
        dup MAXNUM @ <  ( o11 0/-1 o22 0/-1 )
        rot +           ( o11 o22 0/-1 )
        \ cr .s
        if
            =
            EXIT
        then
        \ dup shallowPrint \ cr
        \ ." ------------- " \ cr \ cr
        2dup                                        ( o22 o11 o22 o11 )
        @ swap @                                    ( o22 o11 t11 t22 )
        =                                           ( o22 o11 0/-1 )
        swap dup @ @                                ( o22 0/-1 o11 n )
        rot swap                                    ( o22 o11 0/-1 n )
        1 > *                                       ( o22 o11 0/-1 )
        if                                          ( o22 o11 )
            \ cr ." same type, comparing attributes... "
            dup @ @ 1                                   ( o22 o11 n 1 )
            -1                                          ( o22 o11 n 1 -1 )
            begin
                2 pick 2 pick                               ( o22 o11 n i -1 n i )
                >                                           ( o22 o11 n i -1 0/-1 )
            while                                       ( o22 o11 n i -1 )
                3 pick 2 pick                               ( o22 o11 n i -1 o11 i )
                cells + @                                   ( o22 o11 n i -1 o11[i] )
                5 pick 3 pick                               ( o22 o11 n i -1 o11[i] o22 i )
                cells + @                                   ( o22 o11 n i -1 o11[i] o22[i] )
                swap recurse                                ( o22 o11 n i -1 0/-1 )
                \ swap obj=?                                  ( o22 o11 n i -1 0/-1 )
                *                                           ( o22 o11 n i 0/-1 )
                dup 0 = if                                  ( o22 o11 n i 0/-1 )
                    swap drop 1 pick 1 + swap               ( o22 o11 n n+1 0 )
                then
                swap 1 + swap
            repeat
                                                        ( o22 o11 n i -1 )
            >r                                          ( o22 o11 n i )
            4 dropn                                     ( )
            r>                                          ( 0/-1 )
            \ dup @ @ 1 do
            \     o11 i  cells + @
            \     o22 i cells + @
            \     obj=? *
            \ loop
            \ 0 = 0 =
        else
            @ swap @ =                                  ( 0/-1 )
        then
;


:noname ( o1 o2 -- 0/-1 )
    \ cr ." obj=? " .s
    dethunk         ( o1 o22 )
    swap dethunk    ( o22 o11 )
    \ cr ." dethunked both " .s
    dup MAXNUM @ <  ( o22 o11 0/-1 )
    rot             ( o11 0/-1 o22 )
    dup MAXNUM @ <  ( o11 0/-1 o22 0/-1 )
    rot +           ( o11 o22 0/-1 )
    \ cr .s
    if              ( o11 o22 )
        =           ( 0/-1 )
    else
        \ cr ." going back to obj= " .s
        obj=        ( 0/-1 )
    then
; is obj=?


: isItTrueTyped ( bool -- ) 
    \ cr
    true = if
        ." Yup, thats true! "
    else
        ." are you kidding me? thats false! "
    then \ cr
;|]