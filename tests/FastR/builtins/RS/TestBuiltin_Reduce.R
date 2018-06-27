argv <- structure(list(f = '+', x = 1:7, accumulate = TRUE),     .Names = c('f', 'x', 'accumulate'));do.call('Reduce', argv)
argv <- structure(list(f = function(f, ...) f(...), x = list(.Primitive('log'),     .Primitive('exp'), .Primitive('acos'), .Primitive('cos')),     init = 0, right = TRUE), .Names = c('f', 'x', 'init', 'right'));do.call('Reduce', argv)

