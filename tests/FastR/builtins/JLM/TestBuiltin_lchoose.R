argv <- list(FALSE, FALSE); .Internal(lchoose(argv[[1]], argv[[2]]))
argv <- list(50L, 0:48); .Internal(lchoose(argv[[1]], argv[[2]]))
argv <- list(0.5, 1:9); .Internal(lchoose(argv[[1]], argv[[2]]))
{ .Internal(lchoose(NA, 1)) }
{ .Internal(lchoose(1, NA)) }
{ .Internal(lchoose(NULL, 1)) }
{ .Internal(lchoose(1, NULL)) }
{ .Internal(lchoose(logical(0), logical(0))) }
{ .Internal(lchoose(2, 2.2)) }
{ .Internal(lchoose(0:2, 2.2)) }
{ .Internal(lchoose(c(2.2, 3.3), 2)) }
{ .Internal(lchoose(c(2.2, 3.3), c(2,3,4))) }
{ .Internal(lchoose(c(2.2, 3.3, 4.4), c(2,3))) }
.Internal(lchoose(structure(array(21:24, dim=c(2,2)), dimnames=list(a=c('a1','a2'),b=c('b1','b2'))), 2))
.Internal(lchoose(47, structure(array(21:24, dim=c(2,2)), dimnames=list(a=c('a1','a2'),b=c('b1','b2')))))
.Internal(lchoose(structure(47, myattr='hello'), 2))
