tmp <- c(1,8,NA,3); pivot <- c(1,2,4,3); tmp[pivot] <- tmp; tmp
f <- quote(a+b); attr(f, 'mya') <- 42; f[[2]] <- quote(q); f
e1 <- expression(x^2); l1 <- quote(y^2); l1[1] <- e1; l1[[1]]==e1[[1]]
e1 <- expression(x^2); l1 <- quote(y^2); l1[1] <- e1; l1
{ foo <- function(x, idx) { x[idx] <- F; x }; foo(c(T,T,T,T), structure(c('a'), .Names = c('a'))); r <- foo(c(T,T,T,T), structure(c('a', 'b'), .Names = c('a', 'b'))); r }
