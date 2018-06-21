{ a<- 1; b <- 2; mget(c("a", "b")) }
{ a<- 1; b <- 2; mget(c('a', 'b'), envir=1) }
{ a<- 1; b <- 2; f <- function() { mget(c("a", "b"), inherits=TRUE)}; f() }
{ a<- 1; mget(c("a", "b"), ifnotfound=list(100)) }
{ b <- 2; f <- function() { mget(c("a", "b"), ifnotfound=list(100), inherits=TRUE)}; f() }
{ mget(c("a", "b"), ifnotfound=list(100, 200)) }
{ a<- 1; b <- 2; mget(c("a", "b"), mode="numeric") }
{ a<- 1; b <- "2"; mget(c("a", "b"), mode=c("numeric", "character")) }
{ mget("_foo_", ifnotfound=list(function(x) "bar")) }
{ x<-mget("_foo_", ifnotfound=list(function(x) sys.call(0))); print(x[[1]][[1]]); print(x[[1]][[2]]) }
{ x<-mget("_foo_", ifnotfound=list(function(x) sys.call(1))); list(x[[1]][[1]], x[[1]][[2]], x[[1]][[3]][[1]], x[[1]][[3]][[2]][[1]], x[[1]][[3]][[2]][[2]], x[[1]][[3]][[2]][[3]]) }
mget('abc', ifnotfound = list(`[`))
mget('abc', ifnotfound = list(function(x) cat('NOT FOUND', x, 'n')))
mget('abc', ifnotfound = list(function(x, y = 'default value') cat('NOT FOUND', x, ',', y, 'n')))
