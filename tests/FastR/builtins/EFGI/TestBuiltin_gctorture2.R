argv <- list(FALSE); .Internal(gctorture(argv[[1]]))
argv <- list(NULL); .Internal(gctorture(argv[[1]]))
argv <- list(NULL, NULL, FALSE); .Internal(gctorture2(argv[[1]], argv[[2]], argv[[3]]))
argv <- list(NULL, NULL, NULL); .Internal(gctorture2(argv[[1]], argv[[2]], argv[[3]]))
argv <- list(FALSE, FALSE, FALSE); .Internal(gctorture2(argv[[1]], argv[[2]], argv[[3]]))
