{ sys.parents() }
{ f <- function() sys.parents() ; f() }
{ f <- function() sys.parents() ; g <- function() f() ; g() }
{ f <- function() sys.parents() ; g <- function() f() ; h <- function() g() ; h() }
{ f <- function(x=sys.parents()) x ; g <- function() f() ; h <- function() g() ; h() }
{ f <- function(x) x ; g <- function(y) f(y) ; h <- function(z=sys.parents()) g(z) ; h() }
{ f4 <- function() sys.parents(); f3 <- function(y) y; f2 <- function(x) x; f1 <- function() f2(f3(f4())); f1(); }
{ u <- function() sys.parents(); g <- function(y) y; h <- function(z=u()) g(z); h(); }
{ u <- function() sys.parents(); g <- function(y) y; h <- function(z) g(z); h(u()); }
{ u <- function() sys.parents() ; f <- function(x) x ; g <- function(y) f(y) ; h <- function(z=u()) g(z) ; h() }
{ foo <- function(x) sys.parents();" + SYS_PARENT_SETUP + "}
