{ vapply(c(1L, 2L, 3L, 4L), function(x) x+5L, c(1L)) }
{ iv <- integer(1); iv[[1]] = 1L; vapply(c(1L, 2L, 3L, 4L), function(x) x+5L, iv) }
{ vapply(c(10, 20, 30, 40), function(x) x/2, c(1)) }
{ vapply(c("hello", "goodbye", "up", "down"), function(x) x, c("a"), USE.NAMES = FALSE) }
{ vapply(c("hello", "goodbye", "up", "down"), function(x) x, c("a")) }
{ vapply(c(3+2i, 7-4i, 8+6i), function(x) x+(3+2i), c(1+1i)) }
{ vapply(c(TRUE, FALSE, TRUE), function(x) x, c(TRUE)) }
{ vapply(c(TRUE, FALSE, TRUE), function(x) FALSE, c(TRUE)) }
{ vapply(c(1L, 2L, 3L, 4L), function(x, y) x+5L, c(1L), 10) }
{ f<-function(x) as.integer(x + 1) ; y<-vapply(list(1:3, 6:8), f, rep(7, 3)); y }
{ f<-function(x) x + 1 ; y<-vapply(list(1:3, 6:8), f, rep(as.double(NA), 3)); y }
{ f<-function(x) x + 1 ; y<-vapply(list(1:3), f, rep(as.double(NA), 3)); y }
{ f <- function(a, ...) vapply(a, function(.) identical(a, T, ...), NA); v <- c(1,2,3); f(v) }
{ f<-function(x,y) x-y; w<-c(42, 42); z<-7; vapply(w, f, as.double(NA), x=z) }
{ vapply(c("foo", "bar"), 42, c(TRUE)) }
{ vapply(c("foo", "bar"), function(x) FALSE, function() 42) }
{ vapply(c("foo", "bar"), function(x) FALSE, c(TRUE), USE.NAMES=logical()) }
{ vapply(c("foo", "bar"), function(x) FALSE, c(TRUE), USE.NAMES="42") }
{ vapply(c("foo", "bar"), function(x) FALSE, c(TRUE), USE.NAMES=42) }
{ vapply(quote(a), function(x) 42, 1); }
{ vapply(quote(a), function(x) quote(b), quote(a)); }
{ vapply(c(1,2,3), 42, 1); }
{ vapply(1:3, function(x) rep(1, x), 1); }
{ vapply(1:3, function(x) rep(1, x), 1:3); }
{ vapply(1:3, function(x) rep(1, x), 1L:3L); }
{ m <- matrix(c(1,2,3,4,5,6),2) ; apply(m,1,sum) }
{ m <- matrix(c(1,2,3,4,5,6),2) ; apply(m,2,sum) }
{ a <- vapply(list(a=1:20,b=1:20), function (x) x, FUN.VALUE=1:20); attributes(a); a[1:5] }
{ b <- list(a=structure(c(1:3), names=c('x','y')),b=structure(c(1:3), names=c('x2','y2','z2'))); a <- vapply(b, function (x) x, FUN.VALUE=1:3); attributes(a); a[1:5] }
{ a<-structure(1:2, names=c('a1','a2')); b<-vapply(a, function(v) v + 3, 0); names(b)[1]<-'x'; a }
