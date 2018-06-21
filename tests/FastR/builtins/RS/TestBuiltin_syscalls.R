sys.calls()
{ f <- function(x) sys.calls(); g <- function() f(x); g() }
{ f <- function(x) sys.calls(); g <- function() f(x); length(try(g())) }
{ f <- function(x) x; g <- function() f(sys.calls()); g() }
{ f <- function(x) x; g <- function() f(sys.calls()); length(try(g())) }
{ v <- function() sys.calls() ; u<- function() v(); f <- function(x) x ; g <- function(y) f(y) ; h <- function(z=u()) g(z) ; h() }
