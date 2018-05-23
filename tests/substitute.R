# @line

substitute()
substitute(NULL)
substitute(NULL, NULL)

substitute(a)
# global env vars are not replaced
a <- 3; substitute(a)
substitute(a, list(a = 1)); a <- 3; substitute(a, list(a = 1))

# eval env
substitute(a, list())

a <- 3; substitute(a, list(a = a + 1))
substitute(a + b, list(a = 2))
substitute(x + x, list(x = 3))
substitute(a, list(b = 3))
b <- 1; substitute(a, list(a = b + 1))


f <- function (x) x; b <- 3; substitute(a, list(a = f(b)))
f <- function(x = 3) environment(); substitute(x, f())
f <- function(x = 3) environment(); substitute(y, f())
f <- function(x = 3) environment(); substitute(x + x, f())

substitute(function(x) { x + y }, list(x = function () {NULL}, y = environment()))

substitute(x <- x + 1, list(x = 1))
substitute(1 + 2, list("+"=3))
substitute(substitute())
substitute(substitute(a, list(a = exp)), list(exp = 4))

substitute("hola", list("h"=1))
substitute(a + b, list(a="h"))
substitute(list(x = 2, y = x, substitute(x, list(x=3))), list(x = 2))

substitute(...)
substitute(..., GlobalEnv)
substitute(..., list(x = 1, y = 2))
f <- function(...) substitute(..., NULL); f()
f <- function(...) substitute(..., NULL); f(NULL)
f <- function(...) substitute(...); f()
f <- function(...) substitute(...); f(NULL)
f <- function(...) substitute(..., environment()); f(NULL)
f <- function(...) substitute(..., list(x = 1)); f(NULL)
f <- function (..., y) substitute (y, ...); f()
f <- function () { a <- 1; substitute(a) }; f()
typeof <- function (x) .Internal (typeof (x)); f1 <- function(x, y = x) { x <- x + 1; y }; s1 <- function(x, y = substitute(x)) { x <- x + 1; y }; s2 <- function(x, y) { if(missing(y)) y <- substitute(x); x <- x + 1; y }; a <- 10; f1(a); s1(a); s2(a); typeof(s2(a))


substitute(a);substitute(a)
substitute(1, environment()); substitute(1, environment())
substitute(1); substitute(1)
substitute(NULL); substitute(NULL)


f <- function (x) substitute(x); f(NULL); f(NULL)
f <- function (x) substitute(x, list(x=NA)); f(NULL); f(NULL)
f <- function (x) substitute(x, environment()); f(NULL); f(NULL)
e <- environment(); f <- function () substitute(x, e); f(); f()
f <- function () { substitute (x); substitute(x) }; f(); f()

f <- function (x) {a <- x(); substitute(a)}; g <- function () {1}; f(g) ; f(g)
g <- function (x) {substitute(a + 1, list(a = x))}; f <- function (x) {x(3)}; f(g); f(g)

typeof <- function (x) .Internal (typeof (x)); typeof(substitute(substitute()))
typeof <- function (x) .Internal (typeof (x)); typeof(substitute(function () substitute(x), list(x=2)))
typeof <- function (x) .Internal (typeof (x)); typeof(substitute(x))

# Error messages
substitute(a + 1, 1)
substitute(b, function(x) x)
