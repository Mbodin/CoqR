{  x<-c(1,2); mode(x)<-"character"; x }
{ a<-c("a", "b", "c");  t<-table(a, sample(a)); dimnames(t) }
{ integer() }
{ double() }
{ logical() }
{ double(3) }
{ logical(3L) }
{ character(1L) }
{ raw() }
{ as.complex(as.character(c(1+1i,1+1i))) }
{ as.complex(as.integer(c(1+1i,1+1i))) }
{ as.complex(as.logical(c(1+1i,1+1i))) }
{ as.double(as.logical(c(10,10))) }
{ as.integer(as.logical(-1:1)) }
{ as.raw(as.logical(as.raw(c(1,2)))) }
{ as.character(as.double(1:5)) }
{ as.character(as.complex(1:2)) }
{ m<-matrix(1:6, nrow=3) ; as.integer(m) }
{ m<-matrix(1:6, nrow=3) ; as.vector(m, "any") }
{ m<-matrix(1:6, nrow=3) ; as.vector(mode = "integer", x=m) }
{ m<-matrix(c(1,2,3,4), nrow=2) ; as.vector(m, mode = "double") }
{ m<-matrix(c(1,2,3,4), nrow=2) ; as.vector(m, mode = "numeric") }
{ m<-matrix(c(1,2,3,4), nrow=2) ; as.vector(m) }
{ m<-matrix(c(TRUE,FALSE,FALSE,TRUE), nrow=2) ; as.vector(m) }
{ m<-matrix(c(1+1i,2+2i,3-3i,4-4i), nrow=2) ; as.vector(m) }
{ m<-matrix(c("a","b","c","d"), nrow=2) ; as.vector(m) }
{ m<-matrix(as.raw(c(1,2,3,4)), nrow=2) ; as.vector(m) }
{ m <- matrix(1:6, nrow=2) ; as.double(m) }
{ m <- matrix(c(1,2,3,4,5,6), nrow=2) ; as.integer(m) }
{ m <- matrix(c(1,2,3,4,5,6), nrow=2) ; as.logical(m) }
{ x <- c(0,2); names(x) <- c("hello","hi") ; as.logical(x) }
{ x <- 1:2; names(x) <- c("hello","hi") ; as.double(x) }
{ x <- c(1,2); names(x) <- c("hello","hi") ; as.integer(x) }
{ m<-matrix(c(1,0,1,0), nrow=2) ; as.vector(m, mode = "logical") }
{ m<-matrix(c(1,2,3,4), nrow=2) ; as.vector(m, mode = "complex") }
{ m<-matrix(c(1,2,3,4), nrow=2) ; as.vector(m, mode = "character") }
{ m<-matrix(c(1,2,3,4), nrow=2) ; as.vector(m, mode = "raw") }
{ as.vector(list(1,2,3), mode="integer") }
{ k <- as.list(3:6) ; l <- as.list(1) ; list(k,l) }
{ as.list(list(1,2,"eep")) }
{ as.list(c(1,2,3,2,1)) }
{ as.list(3:6) }
{ l <- list(1) ; attr(l, "my") <- 1; as.list(l) }
{ l <- 1 ; attr(l, "my") <- 1; as.list(l) }
{ l <- c(x=1) ; as.list(l) }
{ x<-7; as.list(environment()) }
{ x<-7; .y<-42; as.list(environment()) }
{ env <- new.env(); env$x<-7; env$.y<-42; length(as.list(env, all.names=TRUE)) }
{ x<-7; f<-function() x<<-42; f_copy<-as.list(environment())[["f"]]; f_copy(); x }
{ as.matrix(1) }
{ as.matrix(1:3) }
{ x <- 1:3; z <- as.matrix(x); x }
{ x <- 1:3 ; attr(x,"my") <- 10 ; attributes(as.matrix(x)) }
{ as.complex(as.double(c(1+1i,1+1i))) }
{ as.complex(as.raw(c(1+1i,1+1i))) }
{ outer(c(1,2,3),c(1,2),"-") }
{ outer(c(1,2,3),c(1,2),"*") }
{ outer(1, 3, "-") }
{ foo <- function (x,y) { x + y * 1i } ; outer(3,3,foo) }
{ foo <- function (x,y) { x + y * 1i } ; outer(1:3,1:3,foo) }
{ outer(c(1,2,3),c(1,2),"+") }
{ outer(1:3,1:2) }
{ outer(1:3,1:2,"*") }
{ outer(1:3,1:2, function(x,y,z) { x*y*z }, 10) }
{ outer(1:2, 1:3, "<") }
{ outer(1:2, 1:3, '<') }
{ foo <- function (x,y) { x + y * 1i } ; outer(3,3,"foo") }
{ m <- matrix(1:6, nrow=2) ;  upper.tri(m, diag=TRUE) }
{ m <- matrix(1:6, nrow=2) ;  upper.tri(m, diag=FALSE) }
{ upper.tri(1:3, diag=TRUE) }
{ upper.tri(1:3, diag=FALSE) }
{ m <- matrix(1:6, nrow=2) ;  lower.tri(m, diag=TRUE) }
{ m <- matrix(1:6, nrow=2) ;  lower.tri(m, diag=FALSE) }
{ lower.tri(1:3, diag=TRUE) }
{ lower.tri(1:3, diag=FALSE) }
{ m <- { matrix( as.character(1:6), nrow=2 ) } ; diag(m) <- c(1,2) ; m }
{ m <- { matrix( (1:6) * (1+3i), nrow=2 ) } ; diag(m) <- c(1,2) ; m }
{ m <- { matrix( as.raw(11:16), nrow=2 ) } ; diag(m) <- c(as.raw(1),as.raw(2)) ; m }
{ is.array(as.array(1)) }
{ is.atomic(integer()) }
{ is.data.frame(as.data.frame(1)) }
{ is.matrix(as.matrix(1)) }
{ e <- expression(x + 1); class(e) <- "foo"; is.object(e) }
{ is.numeric(1:6) }
{ sub <- function(x,y) { x - y }; sub(10,5) }
{ r <- eigen(matrix(rep(1,4), nrow=2), only.values=FALSE) ; round( r$vectors, digits=5 ) }
{ r <- eigen(matrix(rep(1,4), nrow=2), only.values=FALSE) ; round( r$values, digits=5 ) }
{ eigen(10, only.values=FALSE) }
{ r <- eigen(matrix(c(1,2,2,3), nrow=2), only.values=FALSE); round( r$vectors, digits=5 ) }
{ r <- eigen(matrix(c(1,2,2,3), nrow=2), only.values=FALSE); round( r$values, digits=5 ) }
{ r <- eigen(matrix(c(1,2,3,4), nrow=2), only.values=FALSE); round( r$vectors, digits=5 ) }
{ r <- eigen(matrix(c(1,2,3,4), nrow=2), only.values=FALSE); round( r$values, digits=5 ) }
{ r <- eigen(matrix(c(3,-2,4,-1), nrow=2), only.values=FALSE); round( r$vectors, digits=5 ) }
{ r <- eigen(matrix(c(3,-2,4,-1), nrow=2), only.values=FALSE); round( r$values, digits=5 ) }
{ rev.mine <- function(x) { if (length(x)) x[length(x):1L] else x } ; rev.mine(1:3) }
{ kk <- local({k <- function(x) {x*2}}); kk(8)}
{ ne <- new.env(); local(a <- 1, ne); ls(ne) }
{ f <- function() { stop("hello","world") } ; f() }
{ cur <- getwd(); cur1 <- setwd(getwd()) ; cur2 <- getwd() ; cur == cur1 && cur == cur2 }
{ setwd(1) }
{ setwd(character()) }
{ cur <- getwd(); cur1 <- setwd(c(cur, "dummy")) ; cur2 <- getwd() ; cur == cur1  }
{ call("f") }
{ call("f", 2, 3) }
{ call("f", quote(A)) }
{ f <- "f" ; call(f, quote(A)) }
{ f <- round ; call(f, quote(A)) }
{ f <- function() 23 ; cl <- call("f") ; eval(cl) }
{ f <- function(a, b) { a + b } ; l <- call("f", 2, 3) ; eval(l) }
{ f <- function(a, b) { a + b } ; x <- 1 ; y <- 2 ; l <- call("f", x, y) ; x <- 10 ; eval(l) }
{ cl <- call("f") ; typeof(cl) }
{ cl <- call("f") ; class(cl) }
{ x <- 200 ; rm("x") ; x }
{ rm("ieps") }
{ rm("sum", envir=getNamespace("stats")) }
{ x <- 200 ; rm("x") }
{ x<-200; y<-100; rm("x", "y"); x }
{ x<-200; y<-100; rm("x", "y"); y }
{ a = array(1,c(3,3,3)); (a[1,2,3] = 3) }
{x<-gl(2, 8, labels = c("Control", "Treat")); print(x)}
{x<-gl(2, 1, 20); print(x)}
{x<-gl(2, 2, 20); print(x)}
{ a <- gl(2, 4, 8) ; print(a) }
{ b <- gl(2, 2, 8, labels = c("ctrl", "treat")) ; print(b) }
{ x<-as.character(list(a="0", b="0", c="0.3")); type.convert(x, as.is=FALSE) }
