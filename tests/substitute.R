# line

substitute()
substitute(a)

# global env vars are not replaced
a <- 3; substitute(a)
substitute(a, list(a = 1))); a <- 3; substitute(a, list(a = 1))
a <- 3; substitute(a, list(a = a + 1))
substitute(a, list())
substitute(a, list(b = 3))
b <- 1; substitute(a, list(a = b + 1))
f <- function (x) x; b <- 3; substitute(a, list(a = f(b)))
substitute(substitute(a, list(a = exp)), list(exp = 4))


substitute(a, 1)
substitute(a, c(a = 1))
