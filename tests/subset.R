# @line
# Tests about subset.

# pairlists


# vectorlists

list (a = 1)$a
list (1, a = 2, 3)$a
list (ab = 1, b = 2)$ab ; list (ab = 1, b = 2)$a
list (ab = 1, abc = 2)$ab ; list (ab = 1, abc = 2)$abc ; list (ab = 1, abc = 2)$a
list ()$a
2$a
"a"$a
list (a = 3, b = 5) $ a ; list (a = 3, b = 5) $ c ; list (ab = 3, b = 4) $ a ; list (ab = 3, abc = 4) $ a ; list (ab = 3, abc = 4) $ ab
list (a = 5)$a
list (ab = 5)$a
list (ab = 5, abc = 3)$a ; list (ab = 5, abc = 3)$ab ; list (ab = 5, abc = 3)$abc

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
