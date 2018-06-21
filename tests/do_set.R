# @line
# Tests about assignments.
x <- y <- 2 ; x ; y
x <- 2 -> y ; x ; y
x <- 2 ; x <- x <- x + 1 ; x
x <- 2 ; x <- x + 1 -> x ; x
x <- 2 ; y <- x <- x + 1 ; y ; x
x <- 2 ; y <- x + 1 -> x ; y ; x
x <- 1 ; y <- x ; x <- 2 ; y
(x <- 1) + (x <- 2) ; x
x <- 0 ; (x <- x + 1) + (x <- x + 1) ; x
x <- 1 ; x <- NULL ; x ; x <- NA ; x ; x <- NaN ; x
x <- 1 ; "x" <- 2 ; x ; 'x' <- 3 ; x
y <- 1 ; x <- 'y' ; x <- 2 ; y ; x
x <- 1 ; y <- x ; x <- 2 ; y ; x
c ('a', "b") <- 1 ;
"<-" (x, 1) ; x
# T <- 1 ; F <- 2 ; T ; F ; TRUE <- 1
NA <- 1
"NA" <- 1 ; NA
"TRUE" <- 1 ; "FALSE" <- 2 ; TRUE ; FALSE
f <- function (x) x <- 1 ; x <- 2 ; f (3) ; x
x <- 2 ; f <- function (x) x <- 1 ; x ; f (3) ; x
f <- function (x) function (y) x <- 1 ; x <- 2 ; f (3) (4) ; x
x <<- y <<- 2 ; x ; y
x <<- 2 ->> y ; x ; y
x <<- 2 ; x <<- x <<- x + 1 ; x
x <<- 2 ; x <<- x + 1 ->> x ; x
x <<- 2 ; y <<- x <<- x + 1 ; y ; x
x <<- 2 ; y <<- x + 1 ->> x ; y ; x
x <<- 1 ; y <<- x ; x <<- 2 ; y
(x <<- 1) + (x <<- 2) ; x
x <<- 0 ; (x <<- x + 1) + (x <<- x + 1) ; x
x <<- 1 ; x <<- NULL ; x ; x <<- NA ; x ; x <<- NaN ; x
x <<- 1 ; "x" <<- 2 ; x ; 'x' <<- 3 ; x
y <<- 1 ; x <<- 'y' ; x <<- 2 ; y ; x
x <<- 1 ; y <<- x ; x <<- 2 ; y ; x
c ('a', "b") <<- 1 ;
"<<-" (x, 1) ; x
T <<- 1 ; F <<- 2 ; T ; F ; TRUE <<- 1
NA <<- 1
"NA" <<- 1 ; NA
"TRUE" <<- 1 ; "FALSE" <<- 2 ; TRUE ; FALSE
f <<- function (x) x <<- 1 ; x <<- 2 ; f (3) ; x
f <<- function (x) function (y) x <<- 1 ; x <<- 2 ; f (3) (4) ; x
f <- function (x) x <<- 1 ; x <- 2 ; f (3) ; x
f <- function (x) function (y) x <<- 1 ; x <- 2 ; f (3) (4) ; x
x = y = 2 ; x ; y
x = 2 ; x = x = x + 1 ; x
x = 2 ; y = x = x + 1 ; y ; x
x = 0 ; (x = x + 1) + (x = x + 1) ; x
x = 1 ; x = NULL ; x ; x = NA ; x ; x = NaN ; x
x = 1 ; "x" = 2 ; x ; 'x' = 3 ; x
y = 1 ; x = 'y' ; x = 2 ; y ; x
x = 1 ; y = x ; x = 2 ; y ; x
c ('a', "b") = 1 ;
"=" (x, 1) ; x
T = 1 ; F = 2 ; T ; F ; TRUE = 1
NA = 1
"NA" = 1 ; NA
"TRUE" = 1 ; "FALSE" = 2 ; TRUE ; FALSE
f = function (x) x = 1 ; x = 2 ; f (3) ; x
f = function (x) function (y) x = 1 ; x = 2 ; f (3) (4) ; x
a <- b = 2
a = b <- 1 ; a ; b
"<-<-" <- function (a, b, value) c (a, b, value) ; a <- b = 2 ; a ; b
f <- function (x) { g <- function (y) x <- 1 ; g () ; x } ; x <- 2 ; f (3) ; x
f <- function (x) { g <- function (y) x = 1 ; g () ; x } ; x <- 2 ; f (3) ; x
f <- function (x) { g <- function (y) x <<- 1 ; g () ; x } ; x <- 2 ; f (3) ; x
f <- function (x) { g <- function (y) x <- 1 ; g () ; x } ; x <- 2 ; f (x) ; x
f <- function (x) { g <- function (y) x = 1 ; g () ; x } ; x <- 2 ; f (x) ; x
f <- function (x) { g <- function (y) x <<- 1 ; g () ; x } ; x <- 2 ; f (x) ; x
f <- function () { g <- function (y) x <- 1 ; g () ; x } ; x <- 2 ; f () ; x
f <- function () { g <- function (y) x = 1 ; g () ; x } ; x <- 2 ; f () ; x
f <- function () { g <- function (y) x <<- 1 ; g () ; x } ; x <- 2 ; f () ; x

a <- 1 ; `a` ; `a` <- 2 ; a ; `a` ; ` ` <- 3 ; ` ` ; `\`` <- 4 ; `\`` ; `'` <- 5 ; `'` ; `\'` ; `"` <- 6 ; `"` ; `\"`
1 -> a ; `a` ; 2 -> `a` ; a ; `a` ; 3 -> ` ` ; ` ` ; 4 -> `\`` ; `\`` ; 5 -> `'` ; `'` ; `\'` ; 6 -> `"` ; `"` ; `\"`
`` <- 1
2 -> ``
a = 1 ; `a` ; `a` = 2 ; a ; `a` ; ` ` = 3 ; ` ` ; `\`` = 4 ; `\`` ; `'` = 5 ; `'` ; `\'` ; `"` = 6 ; `"` ; `\"`
`` = 1
a <<- 1 ; `a` ; `a` <<- 2 ; a ; `a` ; ` ` <<- 3 ; ` ` ; `\`` <<- 4 ; `\`` ; `'` <<- 5 ; `'` ; `\'` ; `"` <<- 6 ; `"` ; `\"`
`` <<- 1
1 ->> a ; `a` ; 2 ->> `a` ; a ; `a` ; 3 ->> ` ` ; ` ` ; 4 ->> `\`` ; `\`` ; 5 ->> `'` ; `'` ; `\'` ; 6 ->> `"` ; `"` ; `\"`
2 ->> ``
. <- 1 ; . ; 2 -> . ; . ; .. <- 1 ; .. ; 2 -> .. ; ..
