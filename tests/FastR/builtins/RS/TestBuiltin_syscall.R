{ f <- function() sys.call() ; f() }
{ f <- function(x) sys.call() ; f(x = 2) }
{ f <- function() sys.call(1) ; g <- function() f() ; g() }
{ f <- function() sys.call(2) ; g <- function() f() ; h <- function() g() ; h() }
{ f <- function() sys.call(1) ; g <- function() f() ; h <- function() g() ; h() }
{ f <- function() sys.call(-1) ; g <- function() f() ; h <- function() g() ; h() }
{ f <- function() sys.call(-2) ; g <- function() f() ; h <- function() g() ; h() }
{ f <- function() sys.call() ; g <- function() f() ; h <- function() g() ; h() }
{ f <- function() sys.call() ; typeof(f()[[1]]) }
{ f <- function(x) sys.call() ; typeof(f(x = 2)[[1]]) }
{ f <- function(x) sys.call() ; typeof(f(x = 2)[[2]]) }
{ f <- function(x) sys.call() ; f(2) }
{ f <- function(x) sys.call() ; g <- function() 23 ; f(g()) }
{ f <- function(x, y) sys.call() ; f(1, 2) }
{ f <- function(x, y) sys.call() ; f(x=1, 2) }
{ f <- function(x, y) sys.call() ; f(1, y=2) }
{ f <- function(x, y) sys.call() ; f(y=1, 2) }
{ f <- function(x, y) sys.call() ; f(y=1, x=2) }
{ (function() sys.call())() }
{ foo<-function(x, z) UseMethod("foo"); foo.baz<-function(x, z) NextMethod(); y<-1; class(y)<-c("baz", "bar"); foo.bar<-function(x, z) sys.call(0); foo(y, 42) }
{ foo<-function(x, ...) UseMethod("foo"); foo.baz<-function(x, ...) NextMethod(); y<-1; class(y)<-c("baz", "bar"); foo.bar<-function(x, ...) sys.call(0); foo(y, 42) }
{ bar.default<-function(a)sys.call(); bar<-function(a)UseMethod('bar'); bar(a=42); }
{ bar.default<-function(a,...,b)sys.call(); bar<-function(a,x,...)UseMethod('bar'); bar(1,x=2,b=3,c=4); }
{ x<-do.call(function() sys.call(0), list()); x[[1]] }
{ x<-(function(f) f())(function() sys.call(1)); list(x[[1]], x[[2]][[1]], x[[2]][[2]], x[[2]][[3]]) }
{ foo <- function(x) lapply(1:7, function(i) sys.call(i))[c(-4,-7)];boo <- function(bo) bar(bo);callboo <- function(cb) do.call('boo', list(cb));fun <- function(f) callboo(f);fun(42);}
