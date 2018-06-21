{ quote(1:3) }
{ quote(list(1, 2)) }
{ typeof(quote(1)) }
{ typeof(quote(x + y)) }
{ class(quote(x + y)) }
{ mode(quote(x + y)) }
{ is.call(quote(x + y)) }
{ quote(x <- x + 1) }
{ typeof(quote(x)) }
{ l <- quote(a[3] <- 4) ; f <- function() { eval(l) } ; f() }
{ l <- quote(a[3] <- 4) ; eval(l) ; f() }
{ l <- quote(x[1,1] <- 10) ; f <- function() { eval(l) } ; x <- matrix(1:4,nrow=2) ; f() ; x }
{ l <- quote(x[1] <- 1) ; f <- function() { eval(l) } ; x <- 10 ; f() ; x }
{ l <- quote(x[1] <- 1) ; f <- function() { eval(l) ; x <<- 10 ; get("x") } ; x <- 20 ; f() }
quote(?sum)
quote(??show)
quote(?`[[`)
quote(?'+')
quote()
quote(expr=)
quote(expr=...)
quote(...)
typeof(quote(a[,2])[[3]])
{ res <- quote(a[,2])[[3]]; typeof(res) }
quote(foo@bar)[[3]]
quote(foo$bar)[[3]]
quote(foo$'bar')[[3]]
quote(foo@'bar')[[3]]
quote(foo@bar <- 3)[[2]][[3]]
