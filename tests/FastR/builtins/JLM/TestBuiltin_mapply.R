argv <- list(.Primitive('c'), list(list(), list(), list()), NULL); .Internal(mapply(argv[[1]], argv[[2]], argv[[3]]))
mapply(rep, 1:4, 4:1)
mapply(function(x, y) seq_len(x) + y, c(a =  1, b = 2, c = 3),  c(A = 10, B = 0, C = -10))
mapply(rep, times = 1:4, MoreArgs = list(x = 42))
word <- function(C, k) paste(rep.int(C, k), collapse = ""); utils::str(mapply(word, LETTERS[1:6], 6:1, SIMPLIFY = FALSE))
{ mapply(rep.int, 42, MoreArgs = list(4)) }
{ mapply(rep, times = 1:4, x = 4:1) }
{ mapply(rep, times = 1:4, MoreArgs = list(x = 42)) }
