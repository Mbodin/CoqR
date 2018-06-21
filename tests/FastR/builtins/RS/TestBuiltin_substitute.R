{ f <- function(expr) { substitute(expr) } ; f(a * b) }
{ f <- function() { delayedAssign("expr", a * b) ; substitute(expr) } ; f() }
{ f <- function() { delayedAssign("expr", a * b) ; substitute(dummy) } ; f() }
{ delayedAssign("expr", a * b) ; substitute(expr) }
{ f <- function(expr) { expr ; substitute(expr) } ; a <- 10; b <- 2; f(a * b) }
{ f <- function(y) { substitute(y) } ; typeof(f()) }
{ f <- function(y) { as.character(substitute(y)) } ; f("a") }
{ f <- function(x) { g <- function() { substitute(x) } ; g() } ;  f(a * b) }
{ substitute(a, list(a = quote(x + y), x = 1)) }
{ f <- function(x = y, y = x) { substitute(x) } ; f() }
{ f <- function(a, b=a, c=b, d=c) { substitute(d) } ; f(x + y) }
{ f <- function(x) { substitute(x, list(a=1,b=2)) } ; f(a + b) }
{ f <- function(...) { substitute(list(a=1,b=2,...,3,...)) } ; f(x + z, a * b) }
{ f <- function(...) { substitute(list(...)) } ; f(x + z, a * b) }
{ f<-function(...) { substitute(list(...)) }; is.language(f(c(1,2))) }
{ f<-function(...) { substitute(list(...)) }; length(f(c(1,2))) }
{ f<-function(...) { substitute(list(...)) }; is.symbol(f(c(x=1,2))[[1]]) }
{ f<-function(...) { substitute(list(...)) }; is.language(f(c(x=1,2))[[2]]) }
{ f<-function(...) { substitute(list(...)) }; typeof(f(c(1,2))) }
{ g<-function() { f<-function() { 42 }; substitute(f()) } ; typeof(g()[[1]]) }
{ f<-function(...) { substitute(list(...)) }; is.symbol(f(c(x=1,2))[[2]][[1]]) }
{ f<-function(...) { substitute(list(...)) }; is.double(f(c(x=1,2))[[2]][[2]]) }
{ f <- function() { substitute(list(a=1,b=2,...,3,...)) } ; f() }
{ f <- function(...) { substitute(list(a=1,b=2,...,3,...)) } ; f() }
{ f <- function(...) { substitute(list(a=1,b=2,...,3,...,c=8)) } ; f() }
{ f<-function(...) { substitute(list(...)) }; f(c(1,2)) }
{ f<-function(...) { substitute(list(...)) }; f(c(x=1, 2)) }
{ f<-function(...) { substitute(list(...)) }; f(c(x=1, 2, z=3)) }
{ env <- new.env() ; z <- 0 ; delayedAssign("var", z+2, assign.env=env) ; substitute(var, env=env) }
{ env <- new.env() ; z <- 0 ; delayedAssign("var", z+2, assign.env=env) ; z <- 10 ; substitute(var, env=env) }
{ substitute(if(a) { x } else { x * a }, list(a = quote(x + y), x = 1)) }
{ f <- function() { substitute(x(1:10), list(x=quote(sum))) } ; f() }
{ substitute(x + y, list(x=1)) }
{ f <- function(expra, exprb) { substitute(expra + exprb) } ; f(a * b, a + b) }
{ f <- function(z) { g <- function(y) { substitute(y)  } ; g(z) } ; f(a + d) }
{ substitute(a[x], list(a = quote(x + y), x = 1)) }
{ substitute(x <- x + 1, list(x = 1)) }
{ f <- function(y) { substitute(y) } ; f() }
{ substitute(function(x, a) { x + a }, list(a = quote(x + y), x = 1)) }
f<-function(..., list=character()) { substitute(list(...))[-1L] }; as.character(f("config"))
{ substitute({class(y) <- x; y}, list(x=42)) }
f<-function(...) { print(typeof(get('...'))); environment() }; e <- f(c(1,2), b=15, c=44); substitute(foo2({...}), e)
f<-function(x,name) substitute(x$name); f(foo, bar)
f<-function(x,name) substitute(x@name); f(foo, bar)
f<-function(x,name) substitute(x$name<-1); f(foo, bar)
f<-function(x,name) substitute(x@name<-2); f(foo, bar)
f<-function(x,name) substitute(x$name); f(foo, bar); foo <- new.env(); foo$bar <- 1; eval(f(foo,bar))
f<-function(x,name) substitute(x$name <- 5); f(foo, bar); foo <- new.env(); eval(f(foo,bar)); foo$bar
f<-function(x,name) substitute(x@name); f(foo, bar); setClass('cl', representation(bar='numeric')); foo <- new('cl'); foo@bar <- 1; eval(f(foo,bar))
f<-function(x,name) substitute(x@name <- 5); f(foo, bar); setClass('cl', representation(bar='numeric')); foo <- new('cl'); eval(f(foo,bar)); foo@bar
substitute(1, 1)
substitute(1, 1, 1)
substitute(expr=1, env=1)
substitute(1, NULL)
substitute(1, NA)
substitute(1, c(list(1)))
substitute(1, list(c(list(1))))
substitute(1, list(list(1)))
a<-substitute(quote(x+1), NULL); a
a<-substitute(quote(x+1), NA); a
a<-substitute(quote(x+1), list(1)); a
a<-substitute(quote(x+1), list(x=1)); a
a<-substitute(quote(x+1), list(y=1)); a
a<-substitute(quote(x+1), c(list(x=1), 'breakme')); a
a<-substitute(quote(x+1), c(c(list(x=1)))); a
a<-substitute(quote(x+1), list(c(c(list(x=1))))); a
a<-substitute(quote(x+1), list(list(x=1))); a
a<-substitute(quote(x+1), c(list(x=1, 1))); a
a<-substitute(quote(x+y), c(list(x=1), list(y=1))); a
substitute(quote(x+1), environment())
f<-function() {}; substitute(quote(x+1), f)
substitute(quote(x+1), setClass('a'))
typeof(substitute(set))
{ foo <- function(...) assign.dots(...); assign.dots <- function (...) { args <- list(...); sapply(substitute(list(...))[-1], deparse) }; q <- 1; foo(q); }
{ foo <- function(...) bar(..1); bar <- function(x) { substitute(x); }; foo(1+2); }
{ foo <- function(...) bar(..1); bar <- function(x) { x; substitute(x); }; foo(1+2); }
{ foo <- function(...) bar(..1); bar <- function(...) { substitute(..1); }; foo(1+2); }
{ foo <- function(...) bar(..1); bar <- function(...) { ..1; substitute(..1); }; foo(1+2); }
{ foo <- function(...) bar(..1); bar <- function(...) { substitute(list(...)); }; foo(1+2); }
{ foo <- function(...) bar(..1); bar <- function(...) { list(...); substitute(list(...)); }; foo(1+2); }
{ foo <- function(...) bar(...); bar <- function(x) { substitute(x); }; foo(1+2); }
{ foo <- function(...) bar(...); bar <- function(x) { x; substitute(x); }; foo(1+2); }
{ foo <- function(...) bar(...); bar <- function(...) { substitute(..1); }; foo(1+2); }
{ foo <- function(...) bar(...); bar <- function(...) { ..1; substitute(..1); }; foo(1+2); }
{ foo <- function(...) bar(...); bar <- function(...) { substitute(list(...)); }; foo(1+2); }
{ foo <- function(...) bar(...); bar <- function(...) { list(...); substitute(list(...)); }; foo(1+2); }
{ foo <- function(...) bar(3+2); bar <- function(x) { substitute(x); }; foo(1+2); }
{ foo <- function(...) bar(3+2); bar <- function(x) { x; substitute(x); }; foo(1+2); }
{ foo <- function(...) bar(3+2); bar <- function(...) { substitute(..1); }; foo(1+2); }
{ foo <- function(...) bar(3+2); bar <- function(...) { ..1; substitute(..1); }; foo(1+2); }
{ foo <- function(...) bar(3+2); bar <- function(...) { substitute(list(...)); }; foo(1+2); }
{ foo <- function(...) bar(3+2); bar <- function(...) { list(...); substitute(list(...)); }; foo(1+2); }
typeof(substitute())
