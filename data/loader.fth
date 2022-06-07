: refresh ( -- )
    \ s" loader.fth" included
    s" utils.fth" included
    s" arrays.fth" included
    s" higherOrder.fth" included
    s" types.fth" included
    cr ." refreshed!" cr
;
refresh