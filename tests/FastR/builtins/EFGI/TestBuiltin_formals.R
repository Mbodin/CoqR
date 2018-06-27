argv <- list(.Primitive('length<-')); .Internal(formals(argv[[1]]))
argv <- list(logical(0)); .Internal(formals(argv[[1]]))
argv <- list(structure(numeric(0), .Dim = c(0L, 0L))); .Internal(formals(argv[[1]]))
argv <- list(structure(list(c0 = structure(integer(0), .Label = character(0), class = 'factor')), .Names = 'c0', row.names = character(0), class = 'data.frame')); .Internal(formals(argv[[1]]))
{ f <- function(a) {}; formals(f) }
{ f <- function(a, b) {}; formals(f) }
{ f <- function(a, b = c(1, 2)) {}; formals(f) }
