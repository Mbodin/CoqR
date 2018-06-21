argv <- list(2); .Internal(sys.parent(argv[[1]]))
{ sys.parent() }
{ f <- function() sys.parent() ; f() }
{ f <- function() sys.parent() ; g <- function() f() ; g() }
{ f <- function() sys.parent() ; g <- function() f() ; h <- function() g() ; h() }
{ f <- function(x) sys.parent(x); f(0) }
{ f <- function(x) sys.parent(x); f(4) }
{ f <- function(x) sys.parent(x); f(-4) }
{ f <- function(x) x; g <- function() f(sys.parent()); h <- function() g(); h() }
{ f <- function(x=sys.parent()) x ; g <- function() f() ; h <- function() g() ; h() }
{ f <- function(x) x ; g <- function(y) f(y) ; h <- function(z=sys.parent()) g(z) ; h() }
{ u <- function() sys.parent() ; f <- function(x) x ; g <- function(y) f(y) ; h <- function(z=u()) g(z) ; h() }
{ v <- function() sys.parent() ; u<- function() v(); f <- function(x) x ; g <- function(y) f(y) ; h <- function(z=u()) g(z) ; h() }
{ f <- function(x) { print(sys.parent()); x }; g <- function(x) f(x); m <- function() g(g(sys.parent())); callm <- function() m(); callm() }
{ foo <- function(x) sapply(1:7, function(i) sys.parent(i)); bar <- function(ba) do.call(foo, list(ba));boo <- function(bo) bar(bo);callboo <- function(cb) do.call('boo', list(cb));fun <- function(f) callboo(f);fun(42);}
