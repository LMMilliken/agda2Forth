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


\ : dethunk { o1 }
\     o1 MAXNUM @ < 0 = if
\         o1 @ THUNK = if     \ if o1 is a thunk...
\             o1 1 cells + @ if \ if the thunk needs evaluating
\                 o1 2 cells + @ execute  \ execute (evaluate) the contents of the thunk
\                 0 o1 1 cells + !        \ set the flag to false, to show it has been evaluated
\                 dup o1 2 cells + !      \ set the value of the thunk to the value of the now evaluated expression
\             else o1 2 cells + @
\             then recurse
\         else o1
\         then
\     else o1
\     then
\ ;

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
        dup @ THUNK = 0 =   ( o1 0/-1 ) \ if it is not a thunk
        1 pick @ RESULT = 0 = ( o1 0/-1 0/-1)   \ AND it is not a result
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

\     { addr }
\     addr printArray
\     ." FOLDING... addr = " addr .
\     cr ." i = 0 "
\     addr @ makeTHUNK    ( f0 )
\     1                   ( f0 1 )
\     cr .s
\     BEGIN
\     cr ." i = " dup .
\     cr .s
\     addr 1 pick         ( fn-1 n addr n )
\     cr ." addr 1 pick " .s
\     cells + @           ( fn-1 n fn )
\     cr ." cells + @ " .s
\     ." failed? "
\     dup ENDFLAG = if
\         2drop               ( fn-1 )
\         EXIT                ( fn-1 )
\     then
\     makeTHUNK
\     rot                 ( n fn fn-1 )
\     swap                ( n fn-1 fn )
\     cr .s
\     pass                ( n fn )
\     swap                ( fn n )
\     1 +                 ( fn n+1 )
\     AGAIN
\ ;





