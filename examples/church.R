
zero <- function (f) function (x) x

succ <- function (n) function (f) function (x) n (f) (f (x))

add <- function (n, m) function (f) function (x) n (f) (m (f) (x))

mult <- function (n, m) function (f) n (m (f))

exp <- function (n, m) m (n)

pair <- function (a, b) function (c) c (a) (b)

left <- function (a) function (b) a # Also named “K”.

right <- function (a) function (b) b # Also named “SKK”.

pred <- function (n) n (function (p) pair (p (right), succ (p (right)))) (pair (zero, zero)) (left)

sub <- function (n, m) m (pred) (n)

isZero <- function (n) n (function (p) right) (left)

le <- function (n, m) isZero (sub (m, n))

ge <- function (n, m) le (m, n)

and <- function (a, b) a (b) (right)

eq <- function (n, m) and (le (n, m), ge (n, m))

one <- succ (zero)

two <- add (one, one)

three <- succ (two)

four <- add (two, two)

five <- add (two, three)

six <- mult (three, two)

eq (sub (exp (six, two), five), add (exp (five, two), mult (two, three))) (TRUE) (FALSE)

