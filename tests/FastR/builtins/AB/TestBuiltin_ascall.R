argv <- list(list(quote(quote), c(0.568, 1.432, -1.08, 1.08)));as.call(argv[[1]]);
argv <- list(list(quote(quote), FALSE));as.call(argv[[1]]);
argv <- list(list(quote(quote), list(NULL, c('time', 'status'))));as.call(argv[[1]]);
argv <- list(structure(expression(data.frame, check.names = TRUE, stringsAsFactors = TRUE), .Names = c('', 'check.names', 'stringsAsFactors')));as.call(argv[[1]]);
argv <- list(list(quote(quote), 80L));as.call(argv[[1]]);
argv <- list(list(quote(quote), NA));as.call(argv[[1]]);
{ l <- list(f) ; as.call(l) }
{ l <- list(f, 2, 3) ; as.call(l) }
{ g <- function() 23 ; l <- list(f, g()) ; as.call(l) }
{ f <- round ; g <- as.call(list(f, quote(A))) }
{ f <- function() 23 ; l <- list(f) ; cl <- as.call(l) ; eval(cl) }
{ f <- function(a,b) a+b ; l <- list(f,2,3) ; cl <- as.call(l) ; eval(cl) }
{ f <- function(x) x+19 ; g <- function() 23 ; l <- list(f, g()) ; cl <- as.call(l) ; eval(cl) }
{ f <- function(x) x ; l <- list(f, 42) ; cl <- as.call(l); typeof(cl[[1]]) }
{ f <- function(x) x ; l <- list(f, 42) ; cl <- as.call(l); typeof(cl[[2]]) }
{ as.call(42) }
typeof(as.call(list(substitute(graphics::par))))
e <- substitute(a$b(c)); as.call(lapply(e, function(x) x))
e <- expression(function(a) b); as.call(list(e[[1]][[1]]))
e <- expression(function(a) b); as.call(list(e[[1]][[2]]))
call('foo')
invisible(call('function', 'a'))
length(call('function', 'a'))
call('function', pairlist(a=1))
call('function', pairlist(a=1), 3)
call('function', pairlist(a=1), 5,3)
call('function', pairlist(a=1), 5)
as.call(list('function', pairlist(a=1), 5))
as.call(list(as.symbol('function'), pairlist(a=1), 5))
as.call(list(as.symbol('function'), pairlist(a=1)))
as.call(list(as.symbol('function')))
call('function')
{ cl <- quote(fun(3)); as.call(cl) }
