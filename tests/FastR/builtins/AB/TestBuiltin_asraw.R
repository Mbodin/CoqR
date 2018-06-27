argv <- list(structure(numeric(0), .Dim = c(0L, 0L)));as.raw(argv[[1]]);
argv <- list(integer(0));as.raw(argv[[1]]);
argv <- list(logical(0));as.raw(argv[[1]]);
argv <- list(character(0));as.raw(argv[[1]]);
argv <- list(NULL);as.raw(argv[[1]]);
argv <- list(list());as.raw(argv[[1]]);
{ as.raw() }
{ as.raw(NULL) }
{ as.raw(1) }
{ as.raw(1L) }
{ as.raw(1.1) }
{ as.raw(c(1, 2, 3)) }
{ as.raw(c(1L, 2L, 3L)) }
{ as.raw(list(1,2,3)) }
{ as.raw(list("1", 2L, 3.4)) }
{ as.raw.cls <- function(x) 42; as.raw(structure(c(1,2), class='cls')); }
{ as.raw(1+1i) }
{ as.raw(-1) }
{ as.raw(-1L) }
{ as.raw(NA) }
{ as.raw("test") }
{ as.raw(c(1+3i, -2-1i, NA)) }
{ as.raw(c(1, -2, 3)) }
{ as.raw(c(1,1000,NA)) }
{ as.raw(c(1L, -2L, 3L)) }
{ as.raw(c(1L, -2L, NA)) }
{ as.raw('10000001') }
{ as.raw(c('10000001', '42')) }
{ y <- as.raw(c(5L, 6L)); attr(y, 'someAttr') <- 'someValue'; x <- as.raw(y); x[[1]] <- as.raw(42); y }
