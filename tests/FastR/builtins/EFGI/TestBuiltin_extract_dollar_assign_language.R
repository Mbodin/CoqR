{ func <- function(a, b) { mf<-match.call(); mf$a <- NULL; mf }; func('a', 'b') }
{ func <- function(a, b) { mf<-match.call(); mf$a <- 42L; mf }; func('a', 'b') }
{ func <- function(a, b) { mf<-match.call(); mf$nonexist <- NULL; mf }; func('a', 'b') }
{ func <- function(a, b) { mf<-match.call(); mf$nonexist <- 42L; mf }; func('a', 'b') }
