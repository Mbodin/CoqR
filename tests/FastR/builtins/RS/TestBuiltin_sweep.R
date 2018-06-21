argv <- structure(list(x = structure(integer(0), .Dim = c(5L,     0L)), MARGIN = 2, STATS = integer(0)), .Names = c('x', 'MARGIN',     'STATS'));" + "do.call('sweep', argv)
{ sweep(array(1:24, dim = 4:2), 1, 5) }
{ sweep(array(1:24, dim = 4:2), 1, 1:4) }
{ sweep(array(1:24, dim = 4:2), 1:2, 5) }
{ A <- matrix(1:15, ncol=5); sweep(A, 2, colSums(A), "/") }
{ A <- matrix(1:50, nrow=4); sweep(A, 1, 5, '-') }
{ A <- matrix(7:1, nrow=5); sweep(A, 1, -1, '*') }
