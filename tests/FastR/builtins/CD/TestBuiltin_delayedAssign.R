{ delayedAssign("x", y); y <- 10; x }
{ delayedAssign("x", a+b); a <- 1 ; b <- 3 ; x }
{ f <- function() { delayedAssign("x", y); y <- 10; x  } ; f() }
{ delayedAssign("x", y); delayedAssign("y", x) ; x }
{ f <- function() { delayedAssign("x", y); delayedAssign("y", x) ; x } ; f() }
{ f <- function() { delayedAssign("x", 3); delayedAssign("x", 2); x } ; f() }
{ f <- function(...) { delayedAssign("x", ..1) ; y <<- x } ; f(10) ; y }
{ f <- function() print ("outer");  g <- function() { delayedAssign("f", 1); f() }; g()}
{ f <- function() { delayedAssign("x",y); delayedAssign("y",x); g(x, y)}; g <- function(x, y) { x + y }; f() }
{ f <- function() { delayedAssign("x",y); delayedAssign("y",x); list(x, y)}; f() }
{ f <- function() { delayedAssign("x",y); delayedAssign("y",x); paste(x, y)}; f() }
{ f <- function() { delayedAssign("x",y); delayedAssign("y",x); print(x, y)}; f() }
{ f <- function() { p <- 0; for (i in 1:10) { if (i %% 2 == 0) { delayedAssign("a", p + 1); } else { a <- p + 1; }; p <- a; }; p }; f() }
{ f <- function() { x <- 4 ; delayedAssign("x", y); y <- 10; x  } ; f() }
{ h <- new.env(parent=emptyenv()) ; delayedAssign("x", y, h, h) ; assign("y", 2, h) ; get("x", h) }
{ h <- new.env(parent=emptyenv()) ; assign("x", 1, h) ; delayedAssign("x", y, h, h) ; assign("y", 2, h) ; get("x", h) }
