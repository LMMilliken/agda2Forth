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
;