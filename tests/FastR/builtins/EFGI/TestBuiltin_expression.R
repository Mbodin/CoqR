{ f <- function(z) {z}; e<-c(expression(f), 7); eval(e) }
{ f <- function(z) {z}; e<-expression(f); e2<-c(e, 7); eval(e2) }
{ x<-expression(1); y<-c(x,2); typeof(y[[2]]) }
{ class(expression(1)) }
{ x<-expression(1); typeof(x[[1]]) }
{ x<-expression(a); typeof(x[[1]]) }
{ x<-expression(1); y<-c(x,2); typeof(y[[1]]) }
