{ sys.nframe() }
{ f <- function() sys.nframe() ; f() }
{ f <- function() sys.nframe() ; g <- function() f() ; g() }
{ f <- function() sys.nframe() ; g <- function() f() ; h <- function() g() ; h() }
{ f <- function(x=sys.nframe()) x ; g <- function() f() ; h <- function() g() ; h() }
{ f <- function(x) x ; g <- function(y) f(y) ; h <- function(z=sys.nframe()) g(z) ; h() }
{ u <- function() sys.nframe() ; f <- function(x) x ; g <- function(y) f(y) ; h <- function(z=u()) g(z) ; h() }
