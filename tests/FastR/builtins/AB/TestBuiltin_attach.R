d <- data.frame(colNameX=c(1,2,3)); attach(d); colNameX
d <- list(colNameX=c(1,2,3)); attach(d); colNameX
e <- attach(NULL); attr(e, 'name')
d <- list(col=c(1,2,3)); e <- attach(d, name='hello'); attr(e, 'name')
attach(list())
attach('string')
attach(list(x=42), pos='string')
attach(list(), name=42)
detach('string')
d <- list(colNameX=c(1,2,3)); attach(d); detach(d); colNameX
d <- data.frame(colNameX=c(1,2,3)); attach(d); d$colNameX[1] <- 42; colNameX
