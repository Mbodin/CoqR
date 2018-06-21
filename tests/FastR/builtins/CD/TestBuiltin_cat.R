argv <- list('headn', 1:2, 'n', 3:4, file = 'foo4');cat(argv[[1]],argv[[2]],argv[[3]],argv[[4]],argv[[5]]);
argv <- list(list('Loading required package: splinesn'), structure(2L, class = c('terminal', 'connection')), '', FALSE, NULL, FALSE); .Internal(cat(argv[[1]], argv[[2]], argv[[3]], argv[[4]], argv[[5]], argv[[6]]))
argv <- list('%commentnn%anothern%n%n', 'C1tC2tC3n'Panel't'Area Examined't'% Blemishes'n', ''1't'0.8't'3'n', ''2't'0.6't'2'n', ''3't'0.8't'3'n', file = 'test.dat', sep = '');cat(argv[[1]],argv[[2]],argv[[3]],argv[[4]],argv[[5]],argv[[6]],argv[[7]]);
argv <- list('#commentnn#anothern#n#n', 'C1tC2tC3n'Panel't'Area Examined't'# Blemishes'n', ''1't'0.8't'3'n', ''2't'0.6't'2'n', ''3't'0.8't'3'n', file = 'test.dat', sep = '');cat(argv[[1]],argv[[2]],argv[[3]],argv[[4]],argv[[5]],argv[[6]],argv[[7]]);
argv <- list('headn', file = 'foo2');cat(argv[[1]],argv[[2]]);
{ cat() }
{ cat(1) }
{ cat(1, sep="n") }
{ cat(1,2,3) }
{ cat("a") }
{ cat("a", "b") }
{ cat(1, "a") }
{ cat(c(1,2,3)) }
{ cat(c("a","b")) }
{ cat(c(1,2,3),c("a","b")) }
{ cat(TRUE) }
{ cat(TRUE, c(1,2,3), FALSE, 7, c("a","b"), "x") }
{ cat(1:3) }
{ cat("hi",1:3,"hello") }
{ cat(2.3) }
{ cat(1.2,3.4) }
{ cat(c(1.2,3.4),5.6) }
{ cat(c(TRUE,FALSE), TRUE) }
{ cat(NULL) }
{ cat(1L) }
{ cat(1L, 2L, 3L) }
{ cat(c(1L, 2L, 3L)) }
{ cat(1,2,sep=".") }
{ cat("hi",1[2],"hello",sep="-") }
{ cat("hi",1[2],"hello",sep="-n") }
{ m <- matrix(as.character(1:6), nrow=2) ; cat(m) }
{ cat(sep=" ", "hello") }
{ cat(rep(NA, 8), "Hey","Hey","Goodbye","n") }
{ cat("hi",NULL,"hello",sep="-") }
{ cat("hi",integer(0),"hello",sep="-") }
{ cat("a", "b", "c", sep=c("-", "+")) }
{ cat(c("a", "b", "c"), "d", sep=c("-", "+")) }
{ cat(paste(letters, 100* 1:26), fill = TRUE, labels = paste0("{", 1:10, "}:"))}
{ foo <- function(a,b) cat(a,b); foo(42,); }
{ f <- function(...) {cat(...,sep="-")}; f("a") }
{ f <- function(...) {cat(...,sep="-n")}; f("a") }
{ f <- function(...) {cat(...,sep="-")}; f("a", "b") }
{ f <- function(...) {cat(...,sep="-n")}; f("a", "b") }
cat(list(), expression(), sep='this-should-be-ok')
cat(list(1,2,3))
cat(parse(text='42'))
cat(quote(a))
cat(quote(3+3))
