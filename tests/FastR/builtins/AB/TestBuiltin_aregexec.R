argv <- list('FALSE', 'FALSE', c(0.1, NA, NA, NA, NA), c(1L, 1L, 1L), FALSE, FALSE, FALSE); .Internal(aregexec(argv[[1]], argv[[2]], argv[[3]], argv[[4]], argv[[5]], argv[[6]], argv[[7]]))
argv <- list('(lay)(sy)', c('1 lazy', '1', '1 LAZY'), c(2, NA, NA, NA, NA), c(1L, 1L, 1L), FALSE, FALSE, FALSE); .Internal(aregexec(argv[[1]], argv[[2]], argv[[3]], argv[[4]], argv[[5]], argv[[6]], argv[[7]]))
