a <- 0; f <- function(x) { a <- 1; UseMethod('f') }; f.default <- function(x) { a <- 2; (function(x) get('a', envir = parent.frame(x)))(x) }; f(1); f(2); f(3)
a <- 0; f <- function(x) { a <- 1; UseMethod('f') }; f.default <- function(x) { a <- 2; get('a', envir = parent.frame()) }; f(1)
a <- 0; f <- function(x) { a <- 1; UseMethod('f') }; f.foo <- function(x) { a <- 2; NextMethod(); };f.default <- function(x) { a <- 3; (function(x) get('a', envir = parent.frame(x)))(x) }; v <- 1; class(v) <- 'foo'; f(v); v <- 2; class(v) <- 'foo'; f(v)
parent.frame()
{ f <- function() parent.frame() }
{ f <- function() parent.frame() ; g <- function() { n <- 100; f() }; r <- g(); ls(r) }
{ f <- function() parent.frame(2); g <- function() f(); g() }
{ f <- function() parent.frame(3); g <- function() f(); g() }
parent.frame(0)
parent.frame(-1)
{ f <- function(frame) frame; g <- function() f(parent.frame()); g() }
{ f <- function(frame) frame; g <- function() f(parent.frame(3)); g() }
{ foo <- function(x) sapply(1:7, function(fr) sort(tolower(ls(parent.frame(fr)))));boo <- function(bo) bar(bo);callboo <- function(cb) do.call('boo', list(cb));fun <- function(f) callboo(f);fun(42);}
