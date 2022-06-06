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