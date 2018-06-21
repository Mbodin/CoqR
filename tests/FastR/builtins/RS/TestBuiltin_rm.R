tmp <- 42; rm(tmp); tmp
tmp <- 42; rm(list='tmp'); tmp
 e <- new.env(); e$a <- 42; rm(list='a', envir=e); e$a
tmp <- 42; f <- function() rm(list='tmp',inherits=T); f(); tmp
{ env0 <- new.env(); env0$a <- 123L; env1 <- new.env(parent=env0); env1$b <- 456L; rm('a', envir=env1, inherits=T); lapply(c(env0, env1), function(x) ls(x)) }
{ env0 <- new.env(); env0$a <- 123L; env1 <- new.env(parent=env0); env1$b <- 456L; rm('a', envir=env1, inherits=F); lapply(c(env0, env1), function(x) ls(x)) }
{ env0 <- new.env(); env0$b <- 123L; env1 <- new.env(parent=env0); env1$b <- 456L; rm('b', envir=env1, inherits=F); lapply(c(env0, env1), function(x) ls(x)) }
{ rm(list=ls(baseenv(), all.names=TRUE), envir=baseenv()) }
{ e <- new.env(parent=baseenv()); rm('c', envir=e, inherits=T) }
{ e <- new.env(parent=baseenv()); e$a <- 1234L; rm(c('c', 'a'), envir=e, inherits=T); ls(e) }
{ e <- new.env(); e$a <- 1234L; rm(list=c('c', 'a'), envir=e); ls(e) }
{ e <- new.env(); e$a <- 1234L; lockEnvironment(e); rm(list='a', envir=e); ls(e) }
{ e <- new.env(); e$a <- 1234L; lockBinding('a', e); rm(list='a', envir=e); ls(e) }
{ rm(list='a', envir=emptyenv()) }
{ rm(list=ls(emptyenv()), envir=emptyenv()) }
tmp <- 42; rm(tmp, inherits='asd')
.Internal(remove(list=33, environment(), F))
tmp <- 42; rm(tmp, envir=NULL)
tmp <- 42; rm(tmp, envir=42)
