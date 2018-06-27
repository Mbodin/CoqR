argv <- list(FALSE, FALSE); .Internal(beta(argv[[1]], argv[[2]]))
argv <- list(logical(0), logical(0)); .Internal(beta(argv[[1]], argv[[2]]))
argv <- structure(list(a = 0.01, b = 171), .Names = c('a', 'b'));do.call('beta', argv)
argv <- structure(list(a = 1e-200, b = 1e-200), .Names = c('a',     'b'));do.call('beta', argv)
