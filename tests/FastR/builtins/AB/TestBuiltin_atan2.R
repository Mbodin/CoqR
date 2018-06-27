argv <- list(structure(0.142857142857143, .Names = 'Var2'), structure(1.75510204081633, .Names = 'Var1')); .Internal(atan2(argv[[1]], argv[[2]]))
argv <- list(structure(0.142857142857143, .Names = 'Var2'), 1.75510204081633); .Internal(atan2(argv[[1]], argv[[2]]))
.Internal(atan2(structure(c(1,2), .Names = c('a','b')), 1));
.Internal(atan2(structure(1:2, .Names = c('a','b')), 1));
.Internal(atan2(structure(1:6, dim = c(2,3)), 1));
x <- 1:4; class(x) <- 'asdfasdf'; attr(x, 'f') <- 'fff'; names(x) <- c('a','b','c','d'); y <- 1:2; class(y) <- 'fds'; attr(y, 'a') <- 'Asdf'; names(y) <- c('v','y'); .Internal(atan2(x,1)); .Internal(atan2(x,x)); .Internal(atan2(x,y)); .Internal(atan2(y,x)); .Internal(atan2(y,1))
argv <- list(structure(-0.224489795918367, .Names = 'Var2'), structure(-0.816326530612245, .Names = 'Var1')); .Internal(atan2(argv[[1]], argv[[2]]))
argv <- list(c(-1.95681154249341, -2.88854075894443, -2.84850921846233, -2.14635417317387, -1.72790445779804, -0.92649412488672, -0.261537463816701, 0.948205247045638, 1.0990096500205, 2.09024037060933, 2.90928417418961, 4.00425294069879, 1.70515935701163), c(-3.2406391957027, -2.61163262017643, -0.21977838696678, 1.24931893031091, 1.6032898858835, 2.16902716372255, 2.15792786802985, 2.10075226013806, 2.04989923648162, 1.49269068253165, 0.515893014329757, -2.61745072267338, -4.64929811590859)); .Internal(atan2(argv[[1]], argv[[2]]))
argv <- list(0+1i, 0+0i); .Internal(atan2(argv[[1]], argv[[2]]))
argv <- list(2.43782895752771e-05, 0.999996523206508); .Internal(atan2(argv[[1]], argv[[2]]))
argv <- list(logical(0), logical(0)); .Internal(atan2(argv[[1]], argv[[2]]))
{ atan2(0.4, 0.8) }
{ atan2(c(0.3,0.6,0.9), 0.4) }
{ atan2(0.4, c(0.3,0.6,0.9)) }
{ atan2(c(0.3,0.6,0.9), c(0.4, 0.3)) }
{ atan2() }
{ atan2(0.7) }
{ atan2(NULL, 1) }
{ atan2(2, new.env()) }
{ atan2(2, as.symbol('45')) }
