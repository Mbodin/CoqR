# @line

substitute()
substitute(a)

# global env vars are not replaced
a <- 3; substitute(a)
substitute(a, list(a = 1)); a <- 3; substitute(a, list(a = 1))
a <- 3; substitute(a, list(a = a + 1))
substitute(a, list())
substitute(a, list(b = 3))
b <- 1; substitute(a, list(a = b + 1))
substitute(a + b, list(a = 2))
substitute(function(x) { x + y }, list(x = function () {NULL}, y = environment())

f <- function (x) x; b <- 3; substitute(a, list(a = f(b)))

substitute(substitute())
substitute(substitute(a, list(a = exp)), list(exp = 4))

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
