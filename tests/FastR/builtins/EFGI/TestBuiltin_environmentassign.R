{ e1 <- new.env(); environment(e1) <- NULL }
{ e1 <- new.env(); e2 <- new.env(); environment(e1) <- e2 }
{ e1 <- new.env(); environment(e1) <- 3 }
{ e1 <- 1; environment(e1) <- NULL }
{ e1 <- 1; e2 <- new.env(); environment(e1) <- e2 }
{ e1 <- 1; environment(e1) <- 3 }
{ f <- function() {}; e1 <- new.env(); environment(f) <- e1 }
{ f <- function() {}; environment(f) <- NULL }
{ f <- function() x; f2 <- f; e <- new.env(); assign('x', 2, envir=e); x <- 1; environment(f) <- e; c(f(), f2())}
{ f <- NULL; environment(f) <- new.env() }
{ f <- asS4(function(x) x+1); r <- isS4(f); environment(f) <- new.env(); r && isS4(f) }
{ jh <- function(x) x+1; attributes(jh) <- list(myMetaData ='hello'); environment(jh) <- new.env(); attr(jh, 'myMetaData') }
