# @line

.GlobalEnv <- environment()
parent.frame <- function(n = 1) .Internal(parent.frame(n))
eval <-
        function(expr, envir = parent.frame(),
            enclos = if(is.list(envir) || is.pairlist(envir))
              parent.frame() else baseenv())
              .Internal(eval(expr, envir, enclos))

eval.parent <- function(expr, n = 1) {
    p <- parent.frame(n + 1)
    eval(expr, p)
}
new.env <- function (hash = TRUE, parent = parent.frame(), size = 29L)
    .Internal(new.env(hash, parent, size))

local <- function (expr, envir = new.env()) eval.parent(substitute(eval(quote(expr), envir)))
local(NA)
local(NULL)
local(1)
local(TRUE)
f <- function (expr, envir = new.env()) eval.parent(substitute(eval(quote(expr), envir))); f(NULL); f(NULL)

#### parent.frame ####

parent.frame()
parent.frame(0)
parent.frame(1)
parent.frame(-1)
parent.frame(2147483646)
parent.frame(2147483647)
parent.frame(2147483648)

parent.frame(-2147483646)
parent.frame(-2147483647)
parent.frame(-2147483648)

parent.frame(9999999999999)

f <- function () parent.frame(); f()
ff <- function(x) gg(x); gg <- function(y) parent.frame(); ff(1)
gg <- function(y) {ggg <- function() { parent.frame()}; if(y > 0) gg(y-1) else ggg()}; gg(10)


#### eval ####

eval(quote(1), environment())
eval(quote(NULL), environment())
eval(quote(), environment())
eval(substitute(x))
eval(substitute(x), list(x = 3))

#### eval.parent ####

eval.parent()
eval.parent(1)
eval.parent(substitute(a, list(a=2)))
eval.parent(substitute(eval(quote(), environment())))
eval.parent(substitute(eval(quote(), parent.frame())))
eval.parent(substitute(eval(quote(NULL), new.env())))
f <- function(x) eval.parent(substitute(x)); f(NULL); f(NULL)

#### new.env ####

new.env()
new.env(FALSE)
new.env(FALSE, list())
new.env(TRUE, list())
new.env(TRUE, environment())
f <- function() {new.env(parent=parent.frame())}; f()

#### local ####

local(NA)
local(NULL)
local(1)
local(TRUE)
f <- function (expr, envir = new.env()) expr ; f(NULL)
f <- function (expr, envir = new.env()) quote(expr) ; f(NULL)
f <- function (expr, envir = new.env()) eval(expr, envir) ; f(NULL)
f <- function (expr, envir = new.env()) eval(quote(expr), envir) ; f(NULL)
f <- function (expr, envir = new.env()) substitute(eval(quote(expr), envir)) ; f(NULL)
f <- function (expr, envir = new.env()) eval.parent(substitute(eval(quote(expr), envir))); f(NULL)
