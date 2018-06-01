# @line

.Internal(eval(NULL, environment(), environment()))

.Internal(eval(substitute(""), environment(), environment()))
.Internal(eval(substitute(1), environment(), environment()))
.Internal(eval(substitute(NULL), environment(), environment()))


# Symbol
.Internal(eval(substitute(x), environment(), NULL))
.Internal(eval(substitute(x), environment(), environment()))
.Internal(eval(substitute(x), environment(), list()))

.Internal(eval(substitute(x), NULL, NULL))
.Internal(eval(substitute(x), NULL, environment()))
.Internal(eval(substitute(x), list(1), environment()))
.Internal(eval(substitute(x), list(x=1), environment()))
x <- 1; .Internal(eval(substitute(x), environment(), environment()))
.Internal(eval(substitute(x), list(y=1), environment()))
.Internal(eval(substitute(x), list(y=2, x=1), environment()))
.Internal(eval(substitute(x), list(x=1, 3), environment()))

.Internal(eval(substitute(x), 1, environment()))
.Internal(eval(substitute(x), 1:2, environment()))
.Internal(eval(substitute(x), NA, environment()))

.Internal(eval(substitute(x), "Hey", environment()))
.Internal(eval(substitute(x), substitute(x, list(x=1)), environment()))
.Internal(eval(substitute(1), substitute(x, list(x=1)), environment()))

# Lang

.Internal(eval(substitute(a + b), environment(), NULL))
.Internal(eval(substitute(a + b), environment(), environment()))
.Internal(eval(substitute(a + b), environment(), list()))

.Internal(eval(substitute(a + b), NULL, NULL))
.Internal(eval(substitute(a + b), NULL, environment()))
.Internal(eval(substitute(a + b), list(1), environment()))
.Internal(eval(substitute(a + b), list(a=1, b = 2), environment()))
a <- 1; b <- 2; .Internal(eval(substitute(a + b), environment(), environment()))
.Internal(eval(substitute(a + b), list(y=1), environment()))
.Internal(eval(substitute(a + b), list(y=2, a=1), environment()))
a <- 1; .Internal(eval(substitute(a + b), environment(), environment()))
.Internal(eval(substitute(a + b), list(a=1, b = 2, 3), environment()))

.Internal(eval(substitute(a + b), 1, environment()))
.Internal(eval(substitute(a + b), 1:2, environment()))
.Internal(eval(substitute(a + b), NA, environment()))

.Internal(eval(substitute(a + b), "Hey", environment()))
.Internal(eval(substitute(a + b), substitute(a, list(a=1)), environment()))
