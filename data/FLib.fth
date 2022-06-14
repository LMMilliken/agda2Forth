variable MAXNUM 100000000000000 MAXNUM !
variable ENDFLAG 1234 ENDFLAG !
: -= 1 - ;
: += 1 + ;
: dropN ( x1 x2 .. xn n -- )
    0 do
        drop
    loop
;
: printType ( o1 -- )
    dup MAXNUM @ <
    if .
    else @ 1 cells + @ execute
    then
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
: dethunk ( o1 -- o11 )
    BEGIN
    dup MAXNUM @ < if   ( o1 )
        EXIT            ( -- o1 )
    then
    dup isThunk 0 =   ( o1 0/-1 )
    1 pick isResult 0 = ( o1 0/-1 0/-1)
    * if    ( o1 )
        EXIT                ( -- o1 )
    then
    dup @ THUNK = if          ( o1 )
        dup 1 cells + @         ( o1 [addr o11] )
        ENDFLAG swap
        execute                 ( o1 o11 )
        passMany
        swap dup                    ( o11 o1 )
        RESULT swap !               ( o11 o1 )
        1 pick swap                 ( o11 o11 o1 )
        1 cells + !                 ( o11 )
    else
        1 cells + @
    then
    AGAIN
;
: deepDethunk ( [THUNK o1] -- o1 )
    BEGIN
    dethunk                     ( o1 )
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
            EXIT
        then
    else EXIT
    then
    AGAIN
;


: pushThunks { o1 } ( o1 -- o2 o3 .. on )
    o1 MAXNUM @ < 0 =
    if
        o1 @ THUNK = if
            o1
        else
            o1 @ @ 1 >
            if
                o1 @ @ 1 do
                    o1 i cells + @ recurse
                loop
            then
        then
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
        tuck tuck 1 cells + @ curry
        swap 1 cells + !
    else
        swap drop
    then
;

:noname ( ENDFLAG xn .. x2 x1 [THUNK xt1] -- [THUNK xt2])
    BEGIN
    swap
    dup ENDFLAG = if
        drop
        EXIT
    then
    swap pass
    AGAIN
; is passMany

: foldThunks ( addr - THUNK )
    pushArray       ( xn .. x2 x1 ENDFLAG )
    makeTHUNK       ( [THUNK xn] .. x2 x1 ENDFLAG)
    BEGIN
    swap            ( xn-1 [THUNK xn] .. x2 x1 ENDFLAG )
    dup ENDFLAG = if 
        drop        ( [THUNK xn] )
        EXIT
    then
    makeTHUNK pass
    AGAIN
;

variable WILDCARD 1 cells allot
: makeWILDCARD wildcard here 1 fillArray here 1 cells allot ;
:noname ." WILDCARD " ; WILDCARD 1 cells + !

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

: obj= ( o1 o2 -- 0/-1 )
    dup MAXNUM @ >          ( o1 o2 0/-1 )
    if                      ( o1 o2 )
        dup @ WILDCARD =        ( o1 o2 0\-1 )
        if                      ( o1 o2 )
            drop                            ( o1 )
            wildcards pointer @ cells + !   ( )
            pointer @ 1 + pointer !
            -1                              ( -1 )
            EXIT
        then
    then
    swap dup MAXNUM @ >     ( o2 o1 0/-1 )
    if                      ( o2 o1 )
        dup @ WILDCARD =        ( o2 o1 0/-1)
        if                      ( o2 o1 )
            drop                            ( o2 )
            wildcards pointer @ cells + !   ( )
            pointer @ 1 + pointer !
            -1                              ( -1 )
            EXIT
        then                    ( o1 o2 )
    then                    ( o1 o2 )
        deepdethunk                                ( o1 o22 )
        swap deepdethunk                           ( o22 o11 )
        dup MAXNUM @ <  ( o22 o11 0/-1 )
        rot             ( o11 0/-1 o22 )
        dup MAXNUM @ <  ( o11 0/-1 o22 0/-1 )
        rot +           ( o11 o22 0/-1 )
        if
            =
            EXIT
        then
        2dup                                        ( o22 o11 o22 o11 )
        @ swap @                                    ( o22 o11 t11 t22 )
        =                                           ( o22 o11 0/-1 )
        swap dup @ @                                ( o22 0/-1 o11 n )
        rot swap                                    ( o22 o11 0/-1 n )
        1 > *                                       ( o22 o11 0/-1 )
        if                                          ( o22 o11 )
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
        else
            @ swap @ =                                  ( 0/-1 )
        then
;

: fastConsume ( n -- 0 )
    BEGIN
        dup 0 = if
            EXIT
        then
        1 -
    AGAIN
;

: fastPow2 ( n -- 2^n )
    1 swap  ( 1 n -- 2^n )
    BEGIN   ( m n -- m * 2^n )
        dup 0 =
        if
            drop
            EXIT
        then
        swap 2 * swap 1 -
    AGAIN
;

: fastRange ( n -- [addr of arr n] )
    here swap
    BEGIN   ( addr n )
    dup 0 = if  ( addr n )
        ,       ( addr )
        EXIT
    then
    dup ,       ( addr n )
    1 -         ( addr n-1 )
    AGAIN
;

: cell- -1 cells ;

: mid ( l r -- mid ) over - 2/ cell- and + ;
 
: exch ( addr1 addr2 -- ) dup @ >r over @ swap ! r> swap ! ;
 
: partition ( l r -- l r r2 l2 )
  2dup mid @ >r ( r: pivot )
  2dup begin
    swap begin dup @  r@ < while cell+ repeat
    swap begin r@ over @ < while cell- repeat
    2dup <= if 2dup exch >r cell+ r> cell- then
  2dup > until  r> drop ;
 
: fastQsort ( l r -- )
  partition  swap rot
  \ 2over 2over - + < if 2swap then
  2dup < if recurse else 2drop then
  2dup < if recurse else 2drop then ;
 
: fastSort ( array len -- )
  dup 2 < if 2drop exit then
  1- cells over + fastQsort ;
  