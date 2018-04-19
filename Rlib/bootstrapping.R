
# From file src/library/base/baseloader.R of R.

`parent.env<-` <- function (env, value) .Internal(`parent.env<-`(env, value))
existsInFrame <- function (x, env) .Internal(exists(x, env, "any", FALSE))
getFromFrame <- function (x, env) .Internal(get(x, env, "any", FALSE))
set <- function (x, value, env) .Internal(assign(x, value, env, FALSE))
environment <- function () .Internal(environment(NULL))
mkenv <- function() .Internal(new.env(TRUE, baseenv(), 29L))

