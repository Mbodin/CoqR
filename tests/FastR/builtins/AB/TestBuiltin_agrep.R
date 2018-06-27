argv <- list('x86_64-linux-gnu', 'x86_64-linux-gnu', FALSE, FALSE, c(1L, 1L, 1L), c(0.1, NA, NA, NA, NA), FALSE, TRUE); .Internal(agrep(argv[[1]], argv[[2]], argv[[3]], argv[[4]], argv[[5]], argv[[6]], argv[[7]], argv[[8]]))
argv <- list('lasy', c(' 1 lazy 2', '1 lasy 2'), FALSE, FALSE, c(1L, 1L, 1L), structure(c(NA, 0.1, 0.1, 0, 0.1), .Names = c('cost', 'insertions', 'deletions', 'substitutions', 'all')), FALSE, TRUE); .Internal(agrep(argv[[1]], argv[[2]], argv[[3]], argv[[4]], argv[[5]], argv[[6]], argv[[7]], argv[[8]]))
argv <- list('laysy', c('1 lazy', '1', '1 LAZY'), FALSE, TRUE, c(1L, 1L, 1L), c(2, NA, NA, NA, NA), FALSE, TRUE); .Internal(agrep(argv[[1]], argv[[2]], argv[[3]], argv[[4]], argv[[5]], argv[[6]], argv[[7]], argv[[8]]))
argv <- list('laysy', c('1 lazy', '1', '1 LAZY'), TRUE, FALSE, c(1L, 1L, 1L), c(2, NA, NA, NA, NA), FALSE, TRUE); .Internal(agrep(argv[[1]], argv[[2]], argv[[3]], argv[[4]], argv[[5]], argv[[6]], argv[[7]], argv[[8]]))
{ .Internal(agrep(7, "42", F, F, NULL, NULL, F, F)) }
{ .Internal(agrep(character(), "42", F, F, NULL, NULL, F, F)) }
{ .Internal(agrep("7", 42, F, F, NULL, NULL, F, F)) }
{ .Internal(agrepl(7, "42", F, F, NULL, NULL, F, F)) }
{ .Internal(agrepl(character(), "42", F, F, NULL, NULL, F, F)) }
{ .Internal(agrepl("7", 42, F, F, NULL, NULL, F, F)) }
{ agrep('a', c('a'), ignore.case=T) }
{ agrep('A', c('a'), ignore.case=T) }
{ agrep('a', c('A'), ignore.case=T) }
{ agrep('a', c('a', 'b'), ignore.case=T) }
{ agrep('a', c('b', 'a'), ignore.case=T) }
{ agrep('a', c('b', 'a'), ignore.case=F) }
{ agrep('a', c('b', 'a', 'z'), max.distance=0, ignore.case=T) }
{ agrep('A', c('b', 'a', 'z'), max.distance=0, ignore.case=T) }
{ agrep('a', c('b', 'a', 'z'), max.distance=1, ignore.case=T) }
{ agrep('A', c('b', 'a', 'z'), max.distance=1, ignore.case=T) }
