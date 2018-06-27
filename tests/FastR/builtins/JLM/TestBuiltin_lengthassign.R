argv <- list(c('A', 'B'), value = 5);`length<-`(argv[[1]],argv[[2]]);
argv <- list(list(list(2, 2, 6), list(2, 2, 0)), value = 0);`length<-`(argv[[1]],argv[[2]]);
argv <- list(list(list(2, 2, 6), list(1, 3, 9), list(1, 3, -1)), value = 1);`length<-`(argv[[1]],argv[[2]]);
argv <- list(c(28, 27, 26, 25, 24, 23, 22, 21, 20, 19, 18, 17, 16, 15, 14, 13, 12, 11, 10, 9, 8, 7, 6, 5, 4, 3, 2, 1), value = 0L);`length<-`(argv[[1]],argv[[2]]);
argv <- list(c(0L, 1L, 2L, 3L, 4L, 5L, 6L, 0L, 1L, 2L, 3L, 4L, 5L, 6L, 0L, 1L, 2L, 3L, 4L, 5L, 6L, 0L, 1L, 2L, 3L, 4L, 5L, 6L), value = 0L);`length<-`(argv[[1]],argv[[2]]);
argv <- list(list(), value = 0L);`length<-`(argv[[1]],argv[[2]]);
argv <- structure(list(1:3, value = TRUE), .Names = c('', 'value'));do.call('length<-', argv)
{ x<-c(a=1, b=2); length(x)<-1; x }
{ x<-c(a=1, b=2); length(x)<-4; x }
{ x<-data.frame(a=c(1,2), b=c(3,4)); length(x)<-1; x }
{ x<-data.frame(a=c(1,2), b=c(3,4)); length(x)<-4; x }
{ x<-data.frame(a=1,b=2); length(x)<-1; attributes(x) }
{ x<-data.frame(a=1,b=2); length(x)<-4; attributes(x) }
{ x<-factor(c("a", "b", "a")); length(x)<-1; x }
{ x<-factor(c("a", "b", "a")); length(x)<-4; x }
{ x <- 1:4 ; length(x) <- 2 ; x }
{ x <- 1:2 ; length(x) <- 4 ; x }
{ x <- 1 ; f <- function() { length(x) <<- 2 } ; f() ; x }
{ x <- 1:2 ; z <- (length(x) <- 4) ; z }
{ x<-c(a=7, b=42); length(x)<-4; x }
{ x<-c(a=7, b=42); length(x)<-1; x }
{ x<-NULL; length(x)<-2; x }
{ x<-quote(a); length(x)<-2 }
{ x<-c(42, 1); length(x)<-'3'; x }
{ x<-c(42, 1); length(x)<-3.1; x }
{ x<-c(42, 1); length(x)<-c(1,2) }
