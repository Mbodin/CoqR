{ lapply(1:3, function(x) { 2*x }) }
{ lapply(1:3, function(x,y) { x*y }, 2) }
{ x<-c(1,3,4);attr(x,"names")<-c("a","b","c");lapply(x, function(x,y) { as.character(x*y) }, 2) }
{ f <- function() { lapply(c(X="a",Y="b"), function(x) { c(a=x) })  } ; f() }
{ lapply(1:3, function(x,y,z) { as.character(x*y+z) }, 2,7) }
{ f <- function(x) 2 * x ; lapply(1:3, f) }
{ f <- function(x, y) x * y ; lapply(1:3, f, 2) }
{ lapply(1:3, sum) }
{ lapply(1:3, sum, 2) }
{ x <- list(a=1:10, b=1:20) ; lapply(x, sum) }
{ l <- list(list(1),list(2),list(3)); f <- function(a) { lapply(a, function(x) lapply(x, function(y) print(y))) }; f(l)}
{ .Internal(lapply(1:4, 42)) }
lapply(NULL, function(x){x})
lapply(NA, FUN=function(x){x})
lapply(FUN=function(x){x})
lapply(1:4, NULL)
lapply(1:4, NA)
lapply(X=1:4)
lapply(X=function() {print('test')}, FUN=function(x){x})
lapply(X=c(function() {print("test1")}, function() {print("test2")}), FUN=function(x){x})
lapply(X=environment(), FUN=function(x){x})
f <- function(...) { .Internal(lapply(NULL, function(x){x})) }; f()
f <- function(...) { .Internal(lapply(NA, FUN=function(x){x})) }; f()
f <- function(...) { .Internal(lapply(FUN=function(x){x})) }; f()
f <- function(...) { .Internal(lapply(1:4, NULL)) }; f()
f <- function(...) { .Internal(lapply(1:4, NA)) }; f()
f <- function(...) { .Internal(lapply(X=1:4)) }; f()
f <- function(...) { .Internal(lapply(X=function() {print('test')}, FUN=function(x){x})) }; f()
f <- function(...) { .Internal(lapply(X=c(function() {print('test1')}, function() {print('test2')}), FUN=function(x){x})) }; f()
f <- function(...) { .Internal(lapply(X=environment(), FUN=function(x){x})) }; f()
{ ind <- list(c(1, 2, 2), c("A", "A", "B")) ; tapply(1:3, ind) }
{ n <- 17 ; fac <- factor(rep(1:3, length = n), levels = 1:5) ; tapply(1:n, fac, sum) }
{ ind <- list(c(1, 2, 2), c("A", "A", "B")) ; tapply(1:3, ind, sum) }
{ f <- function() { sapply(1:3,function(x){x*2L}) }; f() + f() }
{ f <- function() { sapply(c(1,2,3),function(x){x*2}) }; f() + f() }
{ h <- new.env() ; assign("a",1,h) ; assign("b",2,h) ; sa <- sapply(ls(h), function(k) get(k,h,inherits=FALSE)) ; names(sa) }
{ sapply(1:3, function(x) { if (x==1) { list(1) } else if (x==2) { list(NULL) } else { list() } }) }
{ f<-function(g) { sapply(1:3, g) } ; f(function(x) { x*2 }) }
{ f<-function() { x<-2 ; sapply(1, function(i) { x }) } ; f() }
{ sapply(1:3,function(x){x*2L}) }
{ sapply(c(1,2,3),function(x){x*2}) }
{ sapply(1:3, length) }
{ f<-length; sapply(1:3, f) }
{ sapply(list(1,2,3),function(x){x*2}) }
{ sapply(1:3, function(x) { if (x==1) { 1 } else if (x==2) { integer() } else { TRUE } }) }
{ f<-function(g) { sapply(1:3, g) } ; f(function(x) { x*2 }) ; f(function(x) { TRUE }) }
{ sapply(1:2, function(i) { if (i==1) { as.raw(0) } else { 5+10i } }) }
{ sapply(1:2, function(i) { if (i==1) { as.raw(0) } else { as.raw(10) } }) }
{ sapply(1:2, function(i) { if (i==1) { as.raw(0) } else { "hello" }} ) } 
{ sapply(1:3, function(x) { if (x==1) { list(1) } else if (x==2) { list(NULL) } else { list(2) } }) }
{ sapply(1:3, `-`, 2) }
{ sapply(1:3, "-", 2) }
{ sapply(1:3, function(i) { list(1,2) }) }
{ sapply(1:3, function(i) { if (i < 3) { list(1,2) } else { c(11,12) } }) }
{ sapply(1:3, function(i) { if (i < 3) { c(1+1i,2) } else { c(11,12) } }) }
{ (sapply(1:3, function(i) { if (i < 3) { list(xxx=1) } else {list(zzz=2)} })) }
{ (sapply(1:3, function(i) { list(xxx=1:i) } )) }
{ sapply(1:3, function(i) { if (i < 3) { list(xxx=1) } else {list(2)} }) }
{ (sapply(1:3, function(i) { if (i < 3) { c(xxx=1) } else {c(2)} })) }
{ f <- function() { sapply(c(1,2), function(x) { c(a=x) })  } ; f() }
{ f <- function() { sapply(c(X=1,Y=2), function(x) { c(a=x) })  } ; f() }
{ f <- function() { sapply(c("a","b"), function(x) { c(a=x) })  } ; f() }
{ f <- function() { sapply(c(X="a",Y="b"), function(x) { c(a=x) })  } ; f() }
{ sapply(c("a","b","c"), function(x) { x }) }
{ f <- function(v) { sapply(1:3, function(k) v)}; f(1); f(2) }
