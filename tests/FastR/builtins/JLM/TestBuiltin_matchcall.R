{ fxy <- function(x, y) match.call(); fxy() }
{ fxy <- function(x, y) match.call(); fxy(1, 2) }
{ fxy <- function(x, y) match.call(); fxy(x=1, y=2) }
{ fxy <- function(x, y) match.call(); fxy(y=2, x=1) }
{ fd <- function(...) match.call(); fd() }
{ fd <- function(...) match.call(); fd(1, 2) }
{ fd <- function(...) match.call(); fd(x=1,y=2) }
{ fd <- function(...) match.call(); fd(y=2, x=1) }
{ fdx <- function(x, ...) match.call(); fdx() }
{ fdx <- function(x, ...) match.call(); fdx(1, 2) }
{ fdx <- function(x, ...) match.call(); fdx(x=1,y=2) }
{ fdx <- function(x, ...) match.call(); fdx(y=2, x=1) }
{ fdf <- function(...) match.call(expand.dots=F); fdf() }
{ fdf <- function(...) match.call(expand.dots=F); fdf(1, 2) }
{ fdf <- function(...) match.call(expand.dots=F); fdf(x=1,y=2) }
{ fdf <- function(...) match.call(expand.dots=F); fdf(y=2, x=1) }
{ fdxf <- function(x, ...) match.call(expand.dots=F); fdxf() }
{ fdxf <- function(x, ...) match.call(expand.dots=F); fdxf(1, 2) }
{ fdxf <- function(x, ...) match.call(expand.dots=F); fdxf(x=1,y=2) }
{ fdxf <- function(x, ...) match.call(expand.dots=F); fdxf(y=2, x=1) }
{ fdxy <- function(x, ..., y) match.call(); fdxy() }
{ fdxy <- function(x, ..., y) match.call(); fdxy(1, 2, 3) }
{ fdxy <- function(x, ..., y) match.call(); fdxy(2, 3, x=1) }
{ fdxy <- function(x, ..., y) match.call(); fdxy(y=4, 1, 2, 3) }
{ fdxy <- function(x, ..., y) match.call(); fdxy(y=4, 2, 3, x=1) }
{ fdxyf <- function(x, ..., y) match.call(expand.dots=F); fdxyf() }
{ fdxyf <- function(x, ..., y) match.call(expand.dots=F); fdxyf(1, 2, 3) }
{ fdxyf <- function(x, ..., y) match.call(expand.dots=F); fdxyf(2, 3, x=1) }
{ fdxyf <- function(x, ..., y) match.call(expand.dots=F); fdxyf(y=4, 1, 2, 3) }
{ fdxyf <- function(x, ..., y) match.call(expand.dots=F); fdxyf(y=4, 2, 3, x=1) }
{ f1<-function(...) { dots <- match.call(expand.dots = FALSE)$...; dots }; f2<-function(...) f1(...); f2("a") }
{ f1<-function(...) { dots <- match.call(expand.dots = FALSE)$...; dots }; f2<-function(...) f1(...); f2(c("a")) }
{ f1<-function(...) { dots <- match.call(expand.dots = FALSE)$...; dots }; f2<-function(...) f1(...); f2(c("a"), b="b") }
{ f1<-function(...) { dots <- match.call(expand.dots = FALSE)$...; dots }; f2<-function(...) f1(...); f2(c("a"), c("b")) }
{ f1<-function(...) { dots <- match.call(expand.dots = FALSE)$...; dots }; f2<-function(...) f1(...); typeof(f2("a")[[1]]) }
{ f1<-function(...) { dots <- match.call(expand.dots = FALSE)$...; dots }; f2<-function(...) f1(...); typeof(f2(c("a"))[[1]]) }
{ f1<-function(...) { dots <- match.call(expand.dots = FALSE)$...; dots }; f2<-function(x, ...) f1(x, ...); f2("a") }
{ f1<-function(...) { dots <- match.call(expand.dots = FALSE)$...; dots }; f2<-function(x, ...) f1(x, ...); f2(c("a")) }
{ f1<-function(...) { dots <- match.call(expand.dots = FALSE)$...; dots }; f2<-function(x, ...) f1(x, ...); f2(c("a"), x="b") }
{ f1<-function(...) { dots <- match.call(expand.dots = FALSE)$...; dots }; f2<-function(x, ...) f1(x, ...); f2(c("a"), c("b")) }
{ f1<-function(...) { dots <- match.call(expand.dots = FALSE)$...; dots }; f2<-function(x, ...) f1(x, ...); typeof(f2("a")[[1]]) }
{ f1<-function(...) { dots <- match.call(expand.dots = FALSE)$...; dots }; f2<-function(x, ...) f1(x, ...); typeof(f2(c("a"))[[1]]) }
{ f1<-function(...) { match.call(expand.dots=FALSE)$... }; f1() }
fn3 <- function(...) { (function(...) match.call(cat, call("cat", "abc", p=3,as.symbol("...")), expand.dots = FALSE))(...) }; fn3(sep=x,lab="b",fill=13)
fn3 <- function(...) { (function(...) match.call(cat, call("cat", "abc", p=3,as.symbol("...")), expand.dots = TRUE))(...) }; fn3(sep=x,lab="b",fill=13)
{ foo<-function(...) match.call(expand.dots=F); bar<-function(x) x; y<-42; foo(bar(y), 7) }
{ f <- function(a, ...) { UseMethod('f1', a) };f1.default <- function(a, b=2, c=3, d=4, e=5, ...) { match.call() };f(a=1); f(a=1, b=2); f(a=1, b=2, c=3);f(a=1, b=2, d=4);f(a=1, c=3, d=4, e=5) }
{ f <- function(a, b, c, d, e) { UseMethod('f1', a) };f1.default <- function(a, b=2, c=3, d=4, e=5) { match.call() };f(a=1); f(a=1, b=2); f(a=1, b=2, c=3);f(a=1, b=2, d=4);f(a=1, c=3, d=4, e=5) }
{foo.default<-function(a,b,...,c)match.call(); foo<-function(x,...)UseMethod('foo'); foo(2,3,c=4);}
