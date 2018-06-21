argv <- list(structure(c(0L, 0L, 0L, 1L), .Names = c('Y', 'B', 'V', 'N')));as.logical(argv[[1]]);
argv <- list(structure(c(-4, 1), .Names = c('', '')));as.logical(argv[[1]]);
argv <- list(structure(c(1L, 0L, 0L, 0L, 0L), .Names = c('bibtype', NA, NA, NA, NA)));as.logical(argv[[1]]);
argv <- list(c(1L, NA, 0L));as.logical(argv[[1]]);
argv <- list('FALSE');as.logical(argv[[1]]);
argv <- list(structure(logical(0), .Dim = c(0L, 0L), .Dimnames = list(NULL, NULL)));as.logical(argv[[1]]);
argv <- list(c(3.74165738677394, 0, 8.55235974119758, 1.96396101212393));as.logical(argv[[1]]);
argv <- list(NULL);as.logical(argv[[1]]);
argv <- list(structure('TRUE', .Names = '.registration'));as.logical(argv[[1]]);
argv <- list(structure(c(0, 1, 2, 2), .Dim = c(4L, 1L), .Dimnames = list(c('Y', 'B', 'V', 'N'), NULL)));as.logical(argv[[1]]);
argv <- list(c(TRUE, FALSE, FALSE, FALSE, TRUE, FALSE, TRUE, FALSE, FALSE, FALSE, FALSE, FALSE, FALSE, FALSE));as.logical(argv[[1]]);
argv <- list(structure(list(a = 1), .Names = 'a'));as.logical(argv[[1]]);
argv <- list(structure(list(c0 = structure(integer(0), .Label = character(0), class = 'factor')), .Names = 'c0', row.names = character(0), class = 'data.frame'));as.logical(argv[[1]]);
argv <- list(c(1, 2, 3, 4, 5, NA, NA, 2, 3, 4, 5, 6));as.logical(argv[[1]]);
{ as.logical(1) }
{ as.logical("false") }
{ as.logical("dummy") }
{ x<-c(a=1.1, b=2.2); dim(x)<-c(1,2); attr(x, "foo")<-"foo"; y<-as.logical(x); attributes(y) }
{ x<-c(a=1L, b=2L); dim(x)<-c(1,2); attr(x, "foo")<-"foo"; y<-as.logical(x); attributes(y) }
{ as.logical(c("1","hello")) }
{ as.logical("TRUE") }
{ as.logical(10+2i) }
{ as.logical(c(3+3i, 4+4i)) }
{ as.logical(NULL) }
{ as.logical.cls <- function(x) 42; as.logical(structure(c(1,2), class='cls')); }
{ y <- c(T, F); attr(y, 'someAttr') <- 'someValue'; x <- as.logical(y); x[[1]] <- F; y }
