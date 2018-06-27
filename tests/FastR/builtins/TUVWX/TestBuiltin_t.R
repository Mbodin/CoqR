argv <- structure(list(x = c(-2.13777446721376, 1.17045456767922,     5.85180137819007)), .Names = 'x');do.call('t', argv)
{ m <- matrix(1:49, nrow=7) ; sum(m * t(m)) }
{ m <- matrix(1:81, nrow=9) ; sum(m * t(m)) }
{ m <- matrix(-5000:4999, nrow=100) ; sum(m * t(m)) }
{ m <- matrix(c(rep(1:10,100200),100L), nrow=1001) ; sum(m * t(m)) }
{ m <- double() ; dim(m) <- c(0,4) ; t(m) }
{ t(1:3) }
{ t(t(t(1:3))) }
{ x <- 1:3; names(x) <- c('a', 'b'); t(x) }
{ t(matrix(1:6, nrow=2)) }
{ t(t(matrix(1:6, nrow=2))) }
{ t(matrix(1:4, nrow=2)) }
{ t(t(matrix(1:4, nrow=2))) }
{ x<-matrix(1:2, ncol=2, dimnames=list("a", c("b", "c"))); t(x) }
t(new.env())
v <- as.complex(1:50); dim(v) <- c(5,10); dimnames(v) <- list(as.character(40:44), as.character(10:19)); t(v)
t(1)
t(TRUE)
t(as.raw(c(1,2,3,4)))
t(matrix(1:6, 3, 2, dimnames=list(x=c("x1","x2","x3"),y=c("y1","y2"))))
{ m <- matrix(1:64, 8, 8) ; sum(m * t(m)) }
{ m <- matrix(seq(0.01,0.64,0.01), 8, 8) ; sum(m * t(m)) }
{ m <- matrix(c(T, T, F, F), 2, 2); t(m) }
{ m <- matrix(c('1', '2', '3', '4'), 2, 2); t(m) }
{ m <- matrix(as.raw(c(1,2,3,4)), 2, 2); t(m) }
{ m <- matrix(list(a=1,b=2,c=3,d=4), 2, 2); t(m) }
{ m <- matrix(1:8, 2, 4) ; t(m) }
{ m <- matrix(seq(0.1,0.8,0.1), 2, 4) ; t(m) }
{ m <- matrix(c(T, F, F, F, T, F, F, T), 2, 4); t(m) }
{ m <- matrix(c('1', '2', '3', '4', '5', '6', '7', '8'), 2, 4); t(m) }
{ m <- matrix(as.raw(c(1:8)), 2, 4); t(m) }
{ m <- matrix(list(a=1,b=2,c=3,d=4,e=5,f=6,g=7,h=8), 2, 4); t(m) }
