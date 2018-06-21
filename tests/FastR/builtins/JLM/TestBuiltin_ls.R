f <- function(){ x <- 42; a <- 'two'; ls() }; f()
e <- new.env(); assign('.x',42,e); assign('y','42',e); ls(envir=e, all.names=%0)", new String[]{"TRUE", "FALSE
.Internal(ls(42, TRUE, TRUE))
