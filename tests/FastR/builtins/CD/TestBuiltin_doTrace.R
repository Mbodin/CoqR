argv <- list(c(1, 1, 2));.doTrace(argv[[1]]);
argv <- structure(list(expr = expression(quote(x <- c(1, x)))),     .Names = 'expr');do.call('.doTrace', argv)
