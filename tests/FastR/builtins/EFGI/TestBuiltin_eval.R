{ eval(2 ^ 2 ^ 3)}
{ a <- 1; eval(a) }
{ a <- 1; eval(a + 1) }
{ a <- 1; eval(expression(a + 1)) }
{ f <- function(x) { eval(x) }; f(1) }
{ eval(x <- 1); ls() }
{ ne <- new.env(); eval(x <- 1, ne); ls() }
{ ne <- new.env(); evalq(x <- 1, ne); ls(ne) }
{ ne <- new.env(); evalq(envir=ne, expr=x <- 1); ls(ne) }
{ e1 <- new.env(); assign("x", 100, e1); e2 <- new.env(parent = e1); evalq(x, e2) }
{ f <- function(z) {z}; e<-as.call(c(expression(f), 7)); eval(e) }
{ f<-function(...) { substitute(list(...)) }; eval(f(c(1,2))) }
{ f<-function(...) { substitute(list(...)) }; x<-1; eval(f(c(x,2))) }
{ f<-function(...) { substitute(list(...)) }; eval(f(c(x=1,2))) }
{ g<-function() { f<-function() { 42 }; substitute(f()) } ; eval(g()) }
{ g<-function(y) { f<-function(x) { x }; substitute(f(y)) } ; eval(g(42)) }
{ eval({ xx <- pi; xx^2}) ; xx }
eval('foo')
eval(as.symbol('foo'))
eval(as.symbol('baseenv'))
eval({ xx <- pi; xx^2}) ; xx
{ l <- list(a=1, b=2); eval(quote(a), l)}
a <- 1; lang <- quote(list(a)); eval(lang, data.frame(), NULL)
a <- 1; lang <- quote(list(a)); eval(lang, NULL, NULL)
a <- 1; lang <- quote(list(a)); eval(lang, new.env(), new.env())
y <- 2; x <- 2 ; eval(quote(x+y), c(-1, -2))
{ df <- list(a=c(1,2,3), b=c(3,4,5)); df$c <- with(df, a^2); df; }
f1 <- function(x) { eval(quote(if(x>2){return()}else 1)); 10 };f1(5);f1(0)
eval(parse(text='x<-1'))
eval(parse(text='1+1'))
