# @line
# Tests about subset.

# pairlists


# vectorlists

l <- list (a = 1) ; l$a
l <- list (1, a = 2, 3) ; l$a
l <- list (ab = 1, b = 2) ; l$ab ; l$a
l <- list (ab = 1, abc = 2) ; l$ab ; l$abc ; l$a
l <- list () ; l$a
l <- 2 ; l$a
l <- "a" ; l$a
list (a = 3, b = 5) $ a ; list (a = 3, b = 5) $ c ; list (ab = 3, b = 4) $ a ; list (ab = 3, abc = 4) $ a ; list (ab = 3, abc = 4) $ ab
l <- list (a = 5) ; l$a
l <- list (ab = 5) ; l$a
l <- list (ab = 5, abc = 3) ; l$a ; l$ab ; l$abc 

# environment

environment()$a
a <- 3; environment()$b
environment()$a; a <- 1; environment()$a
ab <- 1; abc <- 3; environment()$a; environment()$ab ; environment()$abc

x <- 1 ; globalenv () $ x ; parent.frame () $ x ; emptyenv () $ x ; baseenv () $ x
x <- 1 ; f <- function (x) globalenv () $ x ; f () ; f (2) ; x <- 3 ; f (4)
f <- function () globalenv () $ x ; x <- 1 ; f () ; (function (x) f ()) (2) ; (function (x) f ()) () ; (function () { x <- 3 ; f () }) ()
x <- 1 ; f <- function (x) parent.frame () $ x ; f () ; f (2) ; x <- 3 ; f (4)
f <- function () parent.frame () $ x ; x <- 1 ; f () ; (function (x) f ()) (2) ; (function (x) f ()) () ; (function () { x <- 3 ; f () }) ()
x <- 1 ; f <- function (x) emptyenv () $ x ; f () ; f (2) ; x <- 3 ; f (4)
x <- 1 ; f <- function (x) baseenv () $ x ; f () ; f (2) ; x <- 3 ; f (4)

