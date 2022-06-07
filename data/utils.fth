variable MAXNUM 100000000000000 MAXNUM !
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