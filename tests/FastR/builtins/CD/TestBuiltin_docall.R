{ x<-list(c(1,2)); do.call("as.matrix", x) }
{ do.call(quote, list(quote(1)))}
{ do.call(quote, list(quote(x)))}
{ do.call(quote, list(quote(x+1)))}
{ f <- function(x) x; do.call(f, list(quote(y)))}
{ f <- function(x) x; do.call(f, list(quote(y + 1)))}
{ do.call("+", list(quote(1), 2))}
v1 <- as.numeric_version('3.0.0'); v2 <- as.numeric_version('3.1.0'); do.call('<', list(v1, v2))
v1 <- as.numeric_version('3.0.0'); v2 <- as.numeric_version('3.1.0'); do.call('<', list(quote(v1), quote(v2)))
typeof(do.call(function(x) x, list(as.symbol('foo'))))
typeof(do.call(function(x) x, list(as.symbol('foo')), quote=TRUE))
{ foo <- function() ls(parent.frame()); bar <- function(a,b,c) do.call('foo', list()); bar(a=1,b=2,c=3); }
{ foo <- function() ls(parent.frame()); bar <- function(a,b,c) do.call('foo', list(), envir=globalenv()); bar(a=1,b=2,c=3) }
{ foo <- function(a,b)  list(a=a,b=b); e <- new.env(); assign('a', 2); assign('b', 3); a<-0; b<-1; do.call('foo', list(a,b), env=e); }
{ foo <- function(a,b)  list(a=a,b=b); e <- new.env(); assign('a', 2); assign('b', 3); a<-0; b<-1; do.call('foo', list(a=as.name('a'),as.name('b')), env=e) }
{ foo <- function(a,b,c) { cat('foo called.'); list(a=a,b=b,c=c); }; side <- function() { cat('side effect!'); 42 }; do.call('foo', list(parse(text='side()')[[1]], 0, 0)); }
{ e <- new.env(); assign('a', 42, e); a <- 1; foo <- function(x) force(x); do.call('foo', list(as.name('a')), envir=e); }
{ e <- new.env(); assign('a', 42, e); a <- 1; foo <- function(x) force(x); do.call('foo', list(as.name('a')), envir=e, quote=T); }
{ e <- new.env(); assign('foo', function() 42, e); foo <- function(x) 1; do.call('foo', list(), envir=e); }
{ e <- new.env(); assign('foo', 42, e); foo <- function(x) 1; do.call('foo', list(), envir=e); }
{ do.call('+', list(data.frame(1), data.frame(2)), envir = new.env()); do.call('assign', list('a',2,new.env()), envir = new.env()); }
{ boo <- function(c) ls(parent.frame(2)); foo <- function(a,b) boo(a); bar <- function(x,z) do.call('foo', list(1,2)); bar() }
{ boo <- function(c) ls(parent.frame(2)); foo <- function(a,b) boo(a); bar <- function(x,z) do.call('foo', list(parse(text='goo()'),2)); bar() }
{ boo <- function(c) ls(parent.frame(3)); foo <- function(a,b) boo(a); bar <- function(x,z) do.call('foo', list(parse(text='goo()'),2)); baz <- function(bazX) bar(bazX,1); baz(); }
{ f1 <- function(a) ls(parent.frame(2)); f2 <- function(b) f1(b); f3 <- function(c) f2(c); f4 <- function(d) do.call('f3', list(d)); f4(42); }
do.call('c', list())
{ f <- function() typeof(sys.call(0)[[1]]); do.call('f', list()); }
