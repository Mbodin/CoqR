as.function(c(alist(a=1+14, b=foo(x),c=), quote(a+foo(c)*b)))
f <- function() a+foo(c)*b; as.function(c(alist(a=1+14, b=foo(x),c=), body(f)))
foo <- function(x) x*2; as.function(c(alist(a=1+14, b=foo(x),c=), quote(a+foo(c)*b)))(c=3,b=1)
foo <- function(x) x*2; f <- function() a+foo(c)*b; as.function(c(alist(a=1+14, b=foo(x),c=), body(f)))(c=3,b=1)
{ as.function(alist(42))() }
{ as.function(alist(42L))() }
{ as.function(alist(TRUE))() }
{ as.function(alist("foo"))() }
{ as.function(alist(7+42i))() }
{ as.function(alist(as.raw(7)))() }
{ .Internal(as.function.default(alist(a+b), "foo")) }
{ .Internal(as.function.default(function() 42, parent.frame())) }
