argv <- list(9L);prod(argv[[1]]);
argv <- list(c(1000L, 1000L));prod(argv[[1]]);
argv <- list(c(4, 2.5, 1.3, -1.20673076923077));prod(argv[[1]]);
argv <- list(structure(c(4L, 4L, 2L), .Names = c('Hair', 'Eye', 'Sex')));prod(argv[[1]]);
argv <- list(integer(0));prod(argv[[1]]);
argv <- list(structure(c(2, 0, 1, 2), .Dim = c(2L, 2L), .Dimnames = list(c('A', 'B'), c('A', 'B'))));prod(argv[[1]]);
argv <- list(structure(c(TRUE, TRUE, TRUE, TRUE), .Dim = c(2L, 2L), .Dimnames = list(c('A', 'B'), c('A', 'B'))));prod(argv[[1]]);
argv <- list(c(0.138260298853371, 0.000636169906925458));prod(argv[[1]]);
argv <- list(NA_integer_);prod(argv[[1]]);
prod( );
argv <- list(numeric(0));prod(argv[[1]]);
{ foo <- function(...) prod(...); foo(); }
