{ f <- function(a) { g(a) } ;  g <- function(b) { missing(b) } ; f() }
{ f <- function(a = 2) { g(a) } ; g <- function(b) { missing(b) } ; f() }
{ f <- function(a,b,c) { missing(b) } ; f(1,,2) }
{ g <- function(a, b, c) { b } ; f <- function(a,b,c) { g(a,b=2,c) } ; f(1,,2) }
{ f <- function(x) {print(missing(x)); g(x)}; g <- function(y=2) {print(missing(y)); y}; f(1) }
{ k <- function(x=2,y) { xx <- x; yy <- y; print(missing(x)); print(missing(xx)); print(missing(yy)); print(missing(yy))}; k(y=1) }
{ f <- function(a = 2 + 3) { missing(a) } ; f() }
{ f <- function(a = z) { missing(a) } ; f() }
{ f <- function(a = 2 + 3) { a;  missing(a) } ; f() }
{ f <- function(a = z) {  g(a) } ; g <- function(b) { missing(b) } ; f() }
{ f <- function(x) { missing(x) } ; f(a) }
{ f <- function(a) { g <- function(b) { before <- missing(b) ; a <<- 2 ; after <- missing(b) ; c(before, after) } ; g(a) } ; f() }
{ f <- function(...) { g(...) } ;  g <- function(b=2) { missing(b) } ; f() }
{ f <- function(x) { print(missing(x)); g(x) }; g <- function(y=3) { print(missing(y)); k(y) }; k <- function(l=4) { print(missing(l)); l }; f(1) }
{ k <- function(x=2,y) { xx <- x; yy <- y; print(missing(x)); print(missing(xx)); print(missing(yy)); print(missing(yy))}; k() }
{ f <- function(a = z, z) {  g(a) } ; g <- function(b) { missing(b) } ; f() }
{ f <- function(a) { g(a) } ; g <- function(b=2) { missing(b) } ; f() }
{ f <- function(x = y, y = x) { g(x, y) } ; g <- function(x, y) { missing(x) } ; f() }
{ f <- function(...) { missing(..2) } ; f(x + z, a * b) }
{ f <- function(x) {print(missing(x)); g(x)}; g <- function(y=2) {print(missing(y)); y}; f() }
{ f <- function(x) { print(missing(x)); g(x) }; g <- function(y=3) { print(missing(y)); k(y) }; k <- function(l=4) { print(missing(l)); l }; f() }
{ f <- function(x) { print(missing(x)) ; g(x) } ; g <- function(y=1) { print(missing(y)) ; h(y) } ; h <- function(z) { print(missing(z)) ; z } ; f() }
{ f <- function(a,b,c,d,e,env) (length(objects(env, all.names = TRUE, pattern = "^[.]__[CTA]_"))); f2 <- function(env) (length(objects(env, all.names = TRUE, pattern = "^[.]__[CTA]_"))); f(); f2() }
{ f <- function(a) { missing("a") };  f(); f(1) }
