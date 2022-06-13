: refresh ( -- )
    \ s" loader.fth" included
    s" utils.fth" included
    s" arrays.fth" included
    s" higherOrder.fth" included
    s" types.fth" included
    s" solutions.fth" included
    cr ." refreshed!" cr
;
refresh