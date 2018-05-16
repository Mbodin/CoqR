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
f <- function (x) x; b <- 3; substitute(a, list(a = f(b)))

substitute(substitute())
substitute(substitute(a, list(a = exp)), list(exp = 4))

substitute(a);substitute(a)
substitute(1, environment()); substitute(1, environment())
substitute(1); substitute(1)
substitute(NULL); substitute(NULL)
f <- function (x) substitute(x); f(NULL); f(NULL)
f <- function (x) substitute(x, environment()); f(NULL); f(NULL)
e <- environment(); f <- function () substitute(x, e); f(); f()


typeof <- function (x) .Internal (typeof (x)); typeof(substitute(substitute()))
typeof <- function (x) .Internal (typeof (x)); typeof(substitute(function () substitute(x), list(x=2)))
typeof <- function (x) .Internal (typeof (x)); typeof(substitute(x))
