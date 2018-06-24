# apply.R
apply <- function(X, MARGIN, FUN, ...)
{
    FUN <- match.fun(FUN)

    ## Ensure that X is an array object
    dl <- length(dim(X))
    if(!dl) stop("dim(X) must have a positive length")
    if(is.object(X))
	X <- if(dl == 2L) as.matrix(X) else as.array(X)
    ## now record dim as coercion can change it
    ## (e.g. when a data frame contains a matrix).
    d <- dim(X)
    dn <- dimnames(X)
    ds <- seq_len(dl)

    ## Extract the margins and associated dimnames

    if (is.character(MARGIN)) {
        if(is.null(dnn <- names(dn))) # names(NULL) is NULL
           stop("'X' must have named dimnames")
        MARGIN <- match(MARGIN, dnn)
        if (anyNA(MARGIN))
            stop("not all elements of 'MARGIN' are names of dimensions")
    }
    s.call <- ds[-MARGIN]
    s.ans  <- ds[MARGIN]
    d.call <- d[-MARGIN]
    d.ans <- d[MARGIN]
    dn.call <- dn[-MARGIN]
    dn.ans <- dn[MARGIN]
    ## dimnames(X) <- NULL

    ## do the calls

    d2 <- prod(d.ans)
    if(d2 == 0L) {
        ## arrays with some 0 extents: return ``empty result'' trying
        ## to use proper mode and dimension:
        ## The following is still a bit `hackish': use non-empty X
        newX <- array(vector(typeof(X), 1L), dim = c(prod(d.call), 1L))
        ans <- forceAndCall(1, FUN, if(length(d.call) < 2L) newX[,1] else
                   array(newX[, 1L], d.call, dn.call), ...)
        return(if(is.null(ans)) ans else if(length(d.ans) < 2L) ans[1L][-1L]  else array(ans, d.ans, dn.ans))
    }
    ## else
    newX <- aperm(X, c(s.call, s.ans))
    dim(newX) <- c(prod(d.call), d2)
    ans <- vector("list", d2)
    if(length(d.call) < 2L) {# vector
        if (length(dn.call)) dimnames(newX) <- c(dn.call, list(NULL))
        for(i in 1L:d2) {
            tmp <- forceAndCall(1, FUN, newX[,i], ...)
            if(!is.null(tmp)) ans[[i]] <- tmp
        }
    } else {
       for(i in 1L:d2) {
           tmp <- forceAndCall(1, FUN, array(newX[,i], d.call, dn.call), ...)
           if(!is.null(tmp)) ans[[i]] <- tmp
        }
    }
    ## answer dims and dimnames

    ans.list <- is.recursive(ans[[1L]])
    l.ans <- length(ans[[1L]])

    ans.names <- names(ans[[1L]])
    if(!ans.list)
	ans.list <- any(lengths(ans) != l.ans)
    if(!ans.list && length(ans.names)) {
        all.same <- vapply(ans, function(x) identical(names(x), ans.names), NA)
        if (!all(all.same)) ans.names <- NULL
    }
    len.a <- if(ans.list) d2 else length(ans <- unlist(ans, recursive = FALSE))
    if(length(MARGIN) == 1L && len.a == d2) {
	names(ans) <- if(length(dn.ans[[1L]])) dn.ans[[1L]] # else NULL
	ans
    } else if(len.a == d2) {
	    array(ans, d.ans, dn.ans)
    } else if(len.a && len.a %% d2 == 0L) {
        if(is.null(dn.ans)) dn.ans <- vector(mode="list", length(d.ans))
	dn1 <- list(ans.names)
	if(length(dn.call) && !is.null(n1 <- names(dn <- dn.call[1])) &&
	   nzchar(n1) && length(ans.names) == length(dn[[1]]))
	    names(dn1) <- n1
	dn.ans <- c(dn1, dn.ans)
	array(ans, c(len.a %/% d2, d.ans),
	      if(!is.null(names(dn.ans)) || !all(vapply(dn.ans, is.null, NA)))
		  dn.ans)
    } else	ans
}

# det.R
det <- function(x, ...)
{
    z <- determinant(x, logarithm = TRUE, ...)
    c(z$sign * exp(z$modulus))
}

determinant <- function(x, logarithm = TRUE, ...) UseMethod("determinant")

# bessel.R
besselI <- function(x, nu, expon.scaled = FALSE)
{
    ## Oddly, this is passed as a double to fit Math3 semantics
    .Internal(besselI(x,nu, 1 + as.logical(expon.scaled)))
}
besselK <- function(x, nu, expon.scaled = FALSE)
{
    .Internal(besselK(x,nu, 1 + as.logical(expon.scaled)))
}
besselJ <- function(x, nu) .Internal(besselJ(x,nu))
besselY <- function(x, nu) .Internal(besselY(x,nu))


# assign.R
assign <-
    function (x, value, pos = -1, envir = as.environment(pos),
              inherits = FALSE, immediate = TRUE)
    .Internal(assign(x, value, envir, inherits))


# as.R
as.single <- function(x,...) UseMethod("as.single")
as.single.default <- function(x,...)
    structure(.Internal(as.vector(x,"double")), Csingle=TRUE)


as.expression <- function(x,...) UseMethod("as.expression")
as.expression.default <- function(x,...) .Internal(as.vector(x, "expression"))

as.list <- function(x,...) UseMethod("as.list")
## This if() avoid dispatch on methods for as.vector.
as.list.default <- function (x, ...)
    if (typeof(x) == "list") x else .Internal(as.vector(x, "list"))

as.list.function <- function (x, ...) c(formals(x), list(body(x)))

## FIXME: as.vector(., "list")  should work for data.frames!
as.list.data.frame <- function(x,...) {
    x <- unclass(x)
    attr(x,"row.names") <- NULL
    x
}

as.list.environment <- function(x, all.names=FALSE, sorted=FALSE, ...)
    .Internal(env2list(x, all.names, sorted))

## NB: as.vector is used for several other as.xxxx, including
## as.expression, as.list, as.pairlist, as.single, as.symbol.
## as.vector dispatches internally so no need for a generic
as.vector <- function(x, mode = "any") .Internal(as.vector(x, mode))

as.matrix <- function(x, ...) UseMethod("as.matrix")
as.matrix.default <- function(x, ...) {
    if (is.matrix(x)) x
    else
	array(x, c(length(x), 1L),
	      if(!is.null(names(x))) list(names(x), NULL) else NULL)
}
as.null <- function(x,...) UseMethod("as.null")
as.null.default <- function(x,...) NULL

as.function <- function(x,...) UseMethod("as.function")
as.function.default <- function (x, envir = parent.frame(), ...)
    if (is.function(x)) x else .Internal(as.function.default(x, envir))

as.array <- function(x, ...) UseMethod("as.array")
as.array.default <- function(x, ...)
{
    if(is.array(x)) return(x)
    n <- names(x)
    dim(x) <- length(x)
    if(length(n)) dimnames(x) <- list(n)
    return(x)
}

as.symbol <- function(x) .Internal(as.vector(x, "symbol"))
as.name <- as.symbol
## would work too: as.name <- function(x) .Internal(as.vector(x, "name"))


all.equal <- function(target, current, ...) UseMethod("all.equal")

all.equal.numeric <-
    function(target, current, tolerance = sqrt(.Machine$double.eps),
             scale = NULL, ..., check.attributes = TRUE)
{
    if (!is.numeric(tolerance))
        stop("'tolerance' should be numeric")
    if (!is.numeric(scale) && !is.null(scale))
        stop("'scale' should be numeric or NULL")
    if (!is.logical(check.attributes))
        stop(gettextf("'%s' must be logical", "check.attributes"), domain = NA)
    msg <- if(check.attributes)
	attr.all.equal(target, current, tolerance = tolerance, scale = scale,
                       ...)
    if(data.class(target) != data.class(current)) {
	msg <- c(msg, paste0("target is ", data.class(target), ", current is ",
                             data.class(current)))
	return(msg)
    }

    lt <- length(target)
    lc <- length(current)
    cplx <- is.complex(target) # and so current must be too.
    if(lt != lc) {
	## *replace* the 'Lengths' msg[] from attr.all.equal():
	if(!is.null(msg)) msg <- msg[- grep("\\bLengths\\b", msg)]
	msg <- c(msg, paste0(if(cplx) "Complex" else "Numeric",
                             ": lengths (", lt, ", ", lc, ") differ"))
	return(msg)
    }
    ## remove atttributes (remember these are both numeric or complex vectors)
    ## one place this is needed is to unclass Surv objects in the rpart test suite.
    target <- as.vector(target)
    current <- as.vector(current)
    out <- is.na(target)
    if(any(out != is.na(current))) {
	msg <- c(msg, paste("'is.NA' value mismatch:", sum(is.na(current)),
			    "in current", sum(out), "in target"))
	return(msg)
    }
    out <- out | target == current
    if(all(out)) return(if(is.null(msg)) TRUE else msg)

    target <- target[!out]
    current <- current[!out]
    if(is.integer(target) && is.integer(current)) target <- as.double(target)
    xy <- mean(abs(target - current)) ## abs(z) == Mod(z) for complex
    what <-
	if(is.null(scale)) {
	    xn <- mean(abs(target))
	    if(is.finite(xn) && xn > tolerance) {
		xy <- xy/xn
		"relative"
	    } else "absolute"
	} else {
	    xy <- xy/scale
	    if(scale == 1) "absolute" else "scaled"
	}

    if (cplx) what <- paste(what, "Mod") # PR#10575
    if(is.na(xy) || xy > tolerance)
        msg <- c(msg, paste("Mean", what, "difference:", format(xy)))

    if(is.null(msg)) TRUE else msg
}


all.equal.character <-
    function(target, current, ..., check.attributes = TRUE)
{
    if (!is.logical(check.attributes))
        stop(gettextf("'%s' must be logical", "check.attributes"), domain = NA)
    msg <-  if(check.attributes) attr.all.equal(target, current, ...)
    if(data.class(target) != data.class(current)) {
	msg <- c(msg, paste0("target is ", data.class(target), ", current is ",
                             data.class(current)))
	return(msg)
    }
    lt <- length(target)
    lc <- length(current)
    if(lt != lc) {
	if(!is.null(msg)) msg <- msg[- grep("\\bLengths\\b", msg)]
	msg <- c(msg,
                 paste0("Lengths (", lt, ", ", lc,
                        ") differ (string compare on first ",
                        ll <- min(lt, lc), ")"))
	ll <- seq_len(ll)
	target <- target[ll]
	current <- current[ll]
    }
    nas <- is.na(target); nasc <- is.na(current)
    if (any(nas != nasc)) {
	msg <- c(msg, paste("'is.NA' value mismatch:", sum(nasc),
                            "in current", sum(nas), "in target"))
	return(msg)
    }
    ne <- !nas & (target != current)
    if(!any(ne) && is.null(msg)){
        TRUE
    } else if(sum(ne) == 1L){
        c(msg, paste("1 string mismatch"))
    } else if(sum(ne) > 1L){
        c(msg, paste(sum(ne), "string mismatches"))
    } else msg
}

all.equal.factor <- function(target, current, ..., check.attributes = TRUE)
{
    if(!inherits(target, "factor"))
	return("'target' is not a factor")
    if(!inherits(current, "factor"))
	return("'current' is not a factor")
    msg <-  if(check.attributes) attr.all.equal(target, current, ...)
    n <- all.equal(as.character(target), as.character(current),
                   check.attributes = check.attributes, ...)
    if(is.character(n)) msg <- c(msg, n)
    if(is.null(msg)) TRUE else msg
}

all.equal.raw <-
    function(target, current, ..., check.attributes = TRUE)
{
    if (!is.logical(check.attributes))
        stop(gettextf("'%s' must be logical", "check.attributes"), domain = NA)
    msg <-  if(check.attributes) attr.all.equal(target, current, ...)
    if(data.class(target) != data.class(current)) {
	msg <- c(msg, paste0("target is ", data.class(target), ", current is ",
                             data.class(current)))
	return(msg)
    }
    lt <- length(target)
    lc <- length(current)
    if(lt != lc) {
	if(!is.null(msg)) msg <- msg[- grep("\\bLengths\\b", msg)]
	msg <- c(msg, paste0("Lengths (", lt, ", ", lc,
                             ") differ (comparison on first ",
                             ll <- min(lt, lc), " components)"))
	ll <- seq_len(ll)
	target <- target[ll]
	current <- current[ll]
    }
    # raws do not have NAs, but logicals do
    nas <- is.na(target); nasc <- is.na(current)
    if (any(nas != nasc)) {
	msg <- c(msg, paste("'is.NA' value mismatch:", sum(nasc),
                            "in current", sum(nas), "in target"))
	return(msg)
    }
    ne <- !nas & (target != current)
    if(!any(ne) && is.null(msg)){
        TRUE
    } else if(sum(ne) == 1L) {
        c(msg, paste("1 element mismatch"))
    } else if(sum(ne) > 1L) {
        c(msg, paste(sum(ne), "element mismatches"))
    } else msg
}

all.equal.POSIXt <- function(target, current, ..., tolerance = 1e-3, scale)
{
    target <- as.POSIXct(target); current <- as.POSIXct(current)
    check_tzones(target, current)
    attr(target, "tzone") <- attr(current, "tzone") <- NULL
    all.equal.numeric(target, current, ..., tolerance = tolerance, scale = 1)
}

# formals.R
formals <- function(fun = sys.function(sys.parent())) {
    if(is.character(fun))
	fun <- get(fun, mode = "function", envir = parent.frame())
    .Internal(formals(fun))
}

alist <- function (...) as.list(sys.call())[-1L]

body <- function(fun = sys.function(sys.parent())) {
    if(is.character(fun))
	fun <- get(fun, mode = "function", envir = parent.frame())
    .Internal(body(fun))
}

# mode.R
mode <- function(x) {
    if(is.expression(x)) return("expression")
    if(is.call(x))
	return(switch(deparse(x[[1L]])[1L],
		      "(" = "(",
		      ## otherwise
		      "call"))
    if(is.name(x)) "name" else
    switch(tx <- typeof(x),
	   double =, integer = "numeric", # 'real=' dropped, 2000/Jan/14
	   closure =, builtin =, special = "function",
	   ## otherwise
	   tx)
}


try <- function(expr, silent = FALSE,
                outFile = getOption("try.outFile", default = stderr())) {
    tryCatch(expr, error = function(e) {
        call <- conditionCall(e)
        if (! is.null(call)) {
            ## Patch up the call to produce nicer result for testing as
            ## try(stop(...)).  This will need adjusting if the
            ## implementation of tryCatch changes.
            ## Use identical() since call[[1L]] can be non-atomic.
            if (identical(call[[1L]], quote(doTryCatch)))
                call <- sys.call(-4L)
            dcall <- deparse(call)[1L]
            prefix <- paste("Error in", dcall, ": ")
            LONG <- 75L # to match value in errors.c
            msg <- conditionMessage(e)
            sm <- strsplit(msg, "\n")[[1L]]
            w <- 14L + nchar(dcall, type="w") + nchar(sm[1L], type="w")
            ## this could be NA if any of this is invalid in a MBCS
            if(is.na(w))
                w <-  14L + nchar(dcall, type="b") + nchar(sm[1L], type="b")
            if (w > LONG)
                prefix <- paste0(prefix, "\n  ")
        }
        else prefix <- "Error : "
        msg <- paste0(prefix, conditionMessage(e), "\n")
        ## Store the error message for legacy uses of try() with
        ## geterrmessage().
        .Internal(seterrmessage(msg[1L]))
        if (! silent && identical(getOption("show.error.messages"), TRUE)) {
            cat(msg, file = outFile)
            .Internal(printDeferredWarnings())
        }
        invisible(structure(msg, class = "try-error", condition = e))
    })
}

comment <- function(x) .Internal(comment(x))
`comment<-` <- function(x, value) .Internal("comment<-"(x, value))

# New-Internal.R

logb <- function(x, base=exp(1)) if(missing(base)) log(x) else log(x, base)

atan2 <- function(y, x) .Internal(atan2(y, x))

beta <- function(a, b) .Internal( beta(a, b))
lbeta <- function(a, b) .Internal(lbeta(a, b))

psigamma <- function(x, deriv = 0L) .Internal(psigamma(x, deriv))


choose <- function(n, k) .Internal(choose(n, k))
lchoose <- function(n, k) .Internal(lchoose(n, k))

##-- 2nd part --



args <- function(name) .Internal(args(name))

cbind <- function(..., deparse.level = 1)
    .Internal(cbind(deparse.level, ...))

rbind <- function(..., deparse.level = 1)
    .Internal(rbind(deparse.level, ...))

## for methods:::bind_activation
.__H__.cbind <- cbind
.__H__.rbind <- rbind


# convert deparsing options to bitmapped integer

deparse <-
    function(expr, width.cutoff = 60L,
	     backtick = mode(expr) %in% c("call", "expression", "(", "function"),
	     control = c("keepInteger", "showAttributes", "keepNA"),
             nlines = -1L)
    .Internal(deparse(expr, width.cutoff, backtick,
                      .deparseOpts(control), nlines))

do.call <- function(what, args, quote = FALSE, envir = parent.frame())
{
    if (!is.list(args))
	stop("second argument must be a list")
    if (quote)
	args <- lapply(args, enquote)
    .Internal(do.call(what, args, envir))
}

drop <- function(x) .Internal(drop(x))

format.info <- function(x, digits = NULL, nsmall = 0L)
    .Internal(format.info(x, digits, nsmall))

gc <- function(verbose = getOption("verbose"),	reset=FALSE)
{
    res <- .Internal(gc(verbose, reset))
    res <- matrix(res, 2L, 7L,
		  dimnames = list(c("Ncells","Vcells"),
		  c("used", "(Mb)", "gc trigger", "(Mb)",
		    "limit (Mb)", "max used", "(Mb)")))
    if(all(is.na(res[, 5L]))) res[, -5L] else res
}
gcinfo <- function(verbose) .Internal(gcinfo(verbose))
gctorture <- function(on = TRUE) .Internal(gctorture(on))
gctorture2 <- function(step, wait = step, inhibit_release = FALSE)
    .Internal(gctorture2(step, wait, inhibit_release))

is.unsorted <- function(x, na.rm = FALSE, strictly = FALSE)
{
    if(length(x) <= 1L) return(FALSE)
    if(!na.rm && anyNA(x))
	return(NA)
    ## else
    if(na.rm && any(ii <- is.na(x)))
	x <- x[!ii]
    .Internal(is.unsorted(x, strictly))
}

nchar <- function(x, type = "chars", allowNA = FALSE, keepNA = NA)
    .Internal(nchar(x, type, allowNA, keepNA))

polyroot <- function(z) .Internal(polyroot(z))


search <- function() .Internal(search())


sprintf <- function(fmt, ...) .Internal(sprintf(fmt, ...))

##-- DANGER ! ---   substitute(list(...))  inside functions !!!
##substitute <- function(expr, env=baseenv()) .Internal(substitute(expr, env))

t.default <- function(x) .Internal(t.default(x))
typeof <- function(x) .Internal(typeof(x))



inherits <- function(x, what, which = FALSE)
	.Internal(inherits(x, what, which))

NextMethod <- function(generic=NULL, object=NULL, ...)
    .Internal(NextMethod(generic, object,...))

data.class <- function(x) {
    if (length(cl <- oldClass(x))) {
	cl[1L]
    } else {
	l <- length(dim(x))
        if (l == 2L) "matrix" else if(l) "array" else mode(x)
    }
}




iconv <- function(x, from = "", to = "", sub = NA, mark = TRUE, toRaw = FALSE)
{
    if(! (is.character(x) || (is.list(x) && is.null(oldClass(x)))))
        x <- as.character(x)
    .Internal(iconv(x, from, to, as.character(sub), mark, toRaw))
}

iconvlist <- function()
{
    int <- .Internal(iconv(NULL, "", "", "", TRUE, FALSE))
    if(length(int)) return(sort.int(int))
    icfile <- system.file("iconvlist", package="utils")
    if(!nchar(icfile, type="bytes"))
        stop("'iconvlist' is not available on this system")
    ext <- readLines(icfile)
    if(!length(ext)) stop("'iconvlist' is not available on this system")
    ## glibc has lines ending //, some versions with a header and some without.
    ## libiconv has lines with multiple entries separated by spaces
    cnt <- grep("//$", ext)
    if(length(cnt)/length(ext) > 0.5) {
        ext <- grep("//$", ext, value = TRUE)
        ext <- sub("//$", "", ext)
    }
    sort.int(unlist(strsplit(ext, "[[:space:]]")))
}



Encoding <- function(x) .Internal(Encoding(x))
`Encoding<-` <- function(x, value) .Internal(setEncoding(x, value))






lengths <- function(x, use.names=TRUE) .Internal(lengths(x, use.names))


## base has no S4 generics
.noGenerics <- TRUE


# constants.R
pi <- 4*atan(1)


# eval.R
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

evalq <-
    function (expr, envir = parent.frame(), enclos = if (is.list(envir) ||
    is.pairlist(envir)) parent.frame() else baseenv())
      .Internal(eval(substitute(expr), envir, enclos))

new.env <- function (hash = TRUE, parent = parent.frame(), size = 29L)
    .Internal(new.env(hash, parent, size))

parent.env <- function(env)
    .Internal(parent.env(env))

`parent.env<-` <- function(env, value)
    .Internal("parent.env<-"(env, value))

local <-
    function (expr, envir = new.env())
    eval.parent(substitute(eval(quote(expr), envir)))

Recall <- function(...) .Internal(Recall(...))

with <- function(data, expr, ...) UseMethod("with")
within <- function(data, expr, ...) UseMethod("within")

with.default <- function(data, expr, ...)
    eval(substitute(expr), data, enclos=parent.frame())

within.data.frame <- function(data, expr, ...)
{
    parent <- parent.frame()
    e <- evalq(environment(), data, parent)
    eval(substitute(expr), e)
    l <- as.list(e, all.names=TRUE)
    l <- l[!vapply(l, is.null, NA, USE.NAMES=FALSE)]
    ## del: variables to *del*ete from data[]; keep non-NULL ones
    del <- setdiff(names(data), (nl <- names(l)))
    data[ nl] <- l
    data[del] <- NULL
    data
}

within.list <- function(data, expr, ...)
{
    parent <- parent.frame()
    e <- evalq(environment(), data, parent)
    eval(substitute(expr), e)
    l <- as.list(e, all.names=TRUE)
    del <- setdiff(names(data), (nl <- names(l))) # variables to delete
    data[ nl] <- l
    data[del] <- NULL
    data
}




force <- function(x) x


# cut.R
cut <- function(x, ...) UseMethod("cut")

.bincode <- function(x, breaks, right = TRUE, include.lowest = FALSE)
    .Internal(bincode(x, breaks, right, include.lowest))

# lapply.R
lapply <- function (X, FUN, ...)
{
    FUN <- match.fun(FUN)
    ## internal code handles all vector types, including expressions
    ## However, it would be OK to have attributes which is.vector
    ## disallows.
    if(!is.vector(X) || is.object(X)) X <- as.list(X)
    ## Note ... is not passed down.  Rather the internal code
    ## evaluates FUN(X[i], ...) in the frame of this function
    .Internal(lapply(X, FUN))
}

rapply <-
    function(object, f, classes = "ANY", deflt = NULL,
             how = c("unlist", "replace", "list"), ...)
{
    if(typeof(object) != "list")
        stop("'object' must be a list")
    how <- match.arg(how)
    res <- .Internal(rapply(object, f, classes, deflt, how))
    if(how == "unlist") unlist(res, recursive = TRUE) else res
}


# matrix.R

matrix <- function(data=NA, nrow=1, ncol=1, byrow=FALSE, dimnames=NULL)
{
    ## avoid copying to strip attributes in simple cases
    if (is.object(data) || !is.atomic(data)) data <- as.vector(data)
    ## NB: the defaults are not really nrow=1, ncol=1: missing values
    ## are treated differently, using length(data).
    .Internal(matrix(data, nrow, ncol, byrow, dimnames,
                     missing(nrow), missing(ncol)))
}

nrow <- function(x) dim(x)[1L]
ncol <- function(x) dim(x)[2L]


row <- function(x, as.factor=FALSE)
{
    if(as.factor) {
        labs <- rownames(x, do.NULL=FALSE, prefix="")
        res <- factor(.Internal(row(dim(x))), labels=labs)
        dim(res) <- dim(x)
        res
    } else .Internal(row(dim(x)))
}

col <- function(x, as.factor=FALSE)
{
    if(as.factor) {
        labs <- colnames(x, do.NULL=FALSE, prefix="")
        res <- factor(.Internal(col(dim(x))), labels=labs)
        dim(res) <- dim(x)
        res
    } else .Internal(col(dim(x)))
}

crossprod <- function(x, y=NULL) .Internal(crossprod(x,y))

t <- function(x) UseMethod("t")


as.pairlist <- function(x) .Internal(as.vector(x, "pairlist"))
pairlist <- function(...) as.pairlist(list(...))


# sort.R

order <- function(..., na.last = TRUE, decreasing = FALSE,
                  method = c("auto", "shell", "radix"))
{
    z <- list(...)

    method <- match.arg(method)
    if (method == "auto") {
        useRadix <- all(vapply(z, function(x) {
            (is.numeric(x) || is.factor(x) || is.logical(x)) &&
                is.integer(length(x))
        }, logical(1L)))
        method <- if (useRadix) "radix" else "shell"
    }

    if(any(unlist(lapply(z, is.object)))) {
        z <- lapply(z, function(x) if(is.object(x)) as.vector(xtfrm(x)) else x)
        if(method == "radix" || !is.na(na.last))
            return(do.call("order", c(z, na.last = na.last,
                                      decreasing = decreasing,
                                      method = method)))
    } else if(method != "radix" && !is.na(na.last)) {
        return(.Internal(order(na.last, decreasing, ...)))
    }

    if (method == "radix") {
        decreasing <- rep_len(as.logical(decreasing), length(z))
        return(.Internal(radixsort(na.last, decreasing, FALSE, TRUE, ...)))
    }

    ## na.last = NA case: remove nas
    if(any(diff((l.z <- lengths(z)) != 0L)))
        stop("argument lengths differ")
    na <- vapply(z, is.na, rep.int(NA, l.z[1L]))
    ok <- if(is.matrix(na)) rowSums(na) == 0L else !any(na)
    if(all(!ok)) return(integer())
    z[[1L]][!ok] <- NA
    ans <- do.call("order", c(z, decreasing = decreasing))
    ans[ok[ans]]
}

# rep.R

rep.int <- function(x, times) .Internal(rep.int(x, times))

# grep.R

grep <-
function(pattern, x, ignore.case = FALSE, perl = FALSE,
         value = FALSE, fixed = FALSE, useBytes = FALSE, invert = FALSE)
{
    ## when value = TRUE we return names
    if(!is.character(x)) x <- structure(as.character(x), names=names(x))
    .Internal(grep(as.character(pattern), x, ignore.case, value,
                   perl, fixed, useBytes, invert))
}
agrep <-
function(pattern, x, max.distance = 0.1, costs = NULL,
         ignore.case = FALSE, value = FALSE, fixed = TRUE,
         useBytes = FALSE)
{
    pattern <- as.character(pattern)
    if(!is.character(x)) x <- as.character(x)

    ## TRE needs integer costs: coerce here for simplicity.
    costs <- as.integer(.amatch_costs(costs))
    bounds <- .amatch_bounds(max.distance)

    .Internal(agrep(pattern, x, ignore.case, value, costs, bounds,
                    useBytes, fixed))
}


agrepl <-
function(pattern, x, max.distance = 0.1, costs = NULL,
         ignore.case = FALSE, fixed = TRUE, useBytes = FALSE)
{
    pattern <- as.character(pattern)
    if(!is.character(x)) x <- as.character(x)

    ## TRE needs integer costs: coerce here for simplicity.
    costs <- as.integer(.amatch_costs(costs))
    bounds <- .amatch_bounds(max.distance)

    .Internal(agrepl(pattern, x, ignore.case, FALSE, costs, bounds,
                     useBytes, fixed))
}


# vector.R

vector <- function(mode = "logical", length = 0L) .Internal(vector(mode, length))
logical <- function(length = 0L) .Internal(vector("logical", length))
character <- function(length = 0L) .Internal(vector("character", length))
integer <- function(length = 0L) .Internal(vector("integer", length))
numeric <- double <-
    function(length = 0L) .Internal(vector("double", length))

complex <- function(length.out = 0L,
		    real = numeric(), imaginary = numeric(),
		    modulus = 1, argument = 0) {
    if(missing(modulus) && missing(argument)) {
	## assume 'real' and 'imaginary'
	.Internal(complex(length.out, real, imaginary))
    } else {
	n <- max(length.out, length(argument), length(modulus))
	rep_len(modulus, n) * exp(1i * rep_len(argument, n))
    }
}

single <- function(length = 0L)
    structure(vector("double", length), Csingle=TRUE)


# structure.R

structure <- function (.Data, ...)
{
    if(is.null(.Data))
        warning("Calling 'structure(NULL, *)' is deprecated, as NULL cannot have attributes.\n  Consider 'structure(list(), *)' instead.")
        ## to become: stop("attempt to set an attribute on NULL")
    attrib <- list(...)
    if(length(attrib)) {
        specials <- c(".Dim", ".Dimnames", ".Names", ".Tsp", ".Label")
        replace <- c("dim", "dimnames", "names", "tsp", "levels")
	m <- match(names(attrib), specials)
	ok <- (!is.na(m) & m)
	names(attrib)[ok] <- replace[m[ok]]
        ## prior to 2.5.0 factors would deparse to double codes
	if("factor" %in% attrib[["class", exact = TRUE]]
           && typeof(.Data) == "double")
            storage.mode(.Data) <- "integer"
	attributes(.Data) <- c(attributes(.Data), attrib)
    }
    .Data
}

# match.fun.R
match.fun <- function (FUN, descend = TRUE)
{
    if ( is.function(FUN) )
        return(FUN)
    if (!(is.character(FUN) && length(FUN) == 1L || is.symbol(FUN))) {
        ## Substitute in parent
        FUN <- eval.parent(substitute(substitute(FUN)))
        if (!is.symbol(FUN))
            stop(gettextf("'%s' is not a function, character or symbol",
                          deparse(FUN)), domain = NA)
    }
    envir <- parent.frame(2)
    if( descend ) {
        FUN <- get(as.character(FUN), mode = "function", envir = envir)
    } else {
        FUN <- get(as.character(FUN), mode = "any", envir = envir)
        if( !is.function(FUN) )
           stop(gettextf("found non-function '%s'", FUN), domain = NA)
    }
    return(FUN)
}

# duplicated.R

anyDuplicated <- function(x, incomparables = FALSE, ...)
    UseMethod("anyDuplicated")

# allnames.R

all.names <- function(expr, functions = TRUE, max.names = -1L, unique = FALSE)
    .Internal(all.names(expr, functions, max.names, unique))


# attach.R

attach <- function(what, pos = 2L, name = deparse(substitute(what)),
                   warn.conflicts = TRUE)
{
    ## FIXME: ./library.R 's library() has *very* similar checkConflicts(), keep in sync
    checkConflicts <- function(env)
    {
        dont.mind <- c("last.dump", "last.warning", ".Last.value",
                       ".Random.seed", ".Last.lib", ".onDetach",
                       ".packageName", ".noGenerics", ".required",
                       ".no_S3_generics", ".requireCachedGenerics")
        sp <- search()
        for (i in seq_along(sp)) {
            if (identical(env, as.environment(i))) {
                db.pos <- i
                break
            }
        }
        ob <- names(as.environment(db.pos))
        if(.isMethodsDispatchOn()) { ## {see note in library() about this}
            these <- ob[startsWith(ob,".__T__")]
            gen  <- gsub(".__T__(.*):([^:]+)", "\\1", these)
            from <- gsub(".__T__(.*):([^:]+)", "\\2", these)
            gen <- gen[from != ".GlobalEnv"]
            ob <- ob[!(ob %in% gen)]
        }
        ipos <- seq_along(sp)[-c(db.pos, match(c("Autoloads", "CheckExEnv"), sp, 0L))]
        for (i in ipos) {
            obj.same <- match(names(as.environment(i)), ob, nomatch = 0L)
            if (any(obj.same > 0L)) {
                same <- ob[obj.same]
                same <- same[!(same %in% dont.mind)]
                Classobjs <- which(startsWith(same,".__"))
                if(length(Classobjs)) same <- same[-Classobjs]
                ## report only objects which are both functions or
                ## both non-functions.
		same.isFn <- function(where)
		    vapply(same, exists, NA,
			   where = where, mode = "function", inherits = FALSE)
		same <- same[same.isFn(i) == same.isFn(db.pos)]
                if(length(same)) {
		    pkg <- if (sum(sp == sp[i]) > 1L) # 'pos = *' needs no translation
			sprintf("%s (pos = %d)", sp[i], i) else sp[i]
		    message(.maskedMsg(sort(same), pkg, by = i < db.pos),
                            domain = NA)
		}
            }
        }
    }

    if(pos == 1L) {
        warning("*** 'pos=1' is not possible; setting 'pos=2' for now.\n",
                "*** Note that 'pos=1' will give an error in the future")
        pos <- 2L
    }
    if (is.character(what) && (length(what) == 1L)){
        if (!file.exists(what))
            stop(gettextf("file '%s' not found", what), domain = NA)
        if(missing(name)) name <- paste0("file:", what)
        value <- .Internal(attach(NULL, pos, name))
        load(what, envir = as.environment(pos))
    } else value <- .Internal(attach(what, pos, name))
    if(warn.conflicts &&
       !exists(".conflicts.OK", envir = value, inherits = FALSE)) {
        checkConflicts(value)
    }
    if (length(names(value)) && .isMethodsDispatchOn() )
        methods::cacheMetaData(value, TRUE)
    invisible(value)
}


detach <- function(name, pos = 2L, unload = FALSE, character.only = FALSE,
                   force = FALSE)
{
    if(!missing(name)) {
	if(!character.only) name <- substitute(name)
	pos <-
	    if(is.numeric(name)) name else {
                if (!is.character(name)) name <- deparse(name)
                match(name, search())
            }
	if(is.na(pos)) stop("invalid 'name' argument")
    }

    packageName <- search()[[pos]]

    ## we need to treat packages differently from other objects, so get those
    ## out of the way now
    if (!startsWith(packageName, "package:"))
        return(invisible(.Internal(detach(pos))))

    ## From here down we are detaching a package.
    pkgname <- .rmpkg(packageName)
    for(pkg in search()[-1L]) {
	if(startsWith(pkg, "package:") &&
           exists(".Depends", pkg, inherits = FALSE) &&
           pkgname %in% get(".Depends", pkg, inherits = FALSE))
            if(force) {
                warning(gettextf("package %s is required by %s, which may no longer work correctly",
				 sQuote(pkgname), sQuote(.rmpkg(pkg))),
                     call. = FALSE, domain = NA)
            } else {
                stop(gettextf("package %s is required by %s so will not be detached",
			      sQuote(pkgname), sQuote(.rmpkg(pkg))),
                     call. = FALSE, domain = NA)
            }
    }
    env <- as.environment(pos)
    libpath <- attr(env, "path")
    hook <- getHook(packageEvent(pkgname, "detach")) # might be a list
    for(fun in rev(hook)) try(fun(pkgname, libpath))
    ## some people, e.g. package g.data, have faked pakages without namespaces
    ns <- .getNamespace(pkgname)
    if(!is.null(ns) &&
       exists(".onDetach", mode = "function", where = ns, inherits = FALSE)) {
        .onDetach <- get(".onDetach",  mode = "function", pos = ns,
                         inherits = FALSE)
        if(!is.null(libpath)) {
            res <- tryCatch(.onDetach(libpath), error = identity)
            if (inherits(res, "error")) {
                warning(gettextf("%s failed in %s() for '%s', details:\n  call: %s\n  error: %s",
                                 ".onDetach", "detach", pkgname,
                                 deparse(conditionCall(res))[1L],
                                 conditionMessage(res)),
                        call. = FALSE, domain = NA)
            }
        }
    } else if(exists(".Last.lib", mode = "function", where = pos, inherits = FALSE)) {
        .Last.lib <- get(".Last.lib",  mode = "function", pos = pos,
                         inherits = FALSE)
        if(!is.null(libpath)) {
            res <- tryCatch(.Last.lib(libpath), error = identity)
            if (inherits(res, "error")) {
                warning(gettextf("%s failed in %s() for '%s', details:\n  call: %s\n  error: %s",
                                 ".Last.lib", "detach", pkgname,
                                 deparse(conditionCall(res))[1L],
                                 conditionMessage(res)),
                        call. = FALSE, domain = NA)
            }
        }
    }
    .Internal(detach(pos))

    if(isNamespaceLoaded(pkgname)) {
        ## the lazyload DB is flushed when the namespace is unloaded
        if(unload) {
            tryCatch(unloadNamespace(pkgname),
                     error = function(e)
                     warning(gettextf("%s namespace cannot be unloaded:\n  ",
                                      sQuote(pkgname)),
                             conditionMessage(e),
                             call. = FALSE, domain = NA))
        }
    } else {
        if(.isMethodsDispatchOn() && methods:::.hasS4MetaData(env))
            methods::cacheMetaData(env, FALSE)
        .Internal(lazyLoadDBflush(paste0(libpath, "/R/", pkgname, ".rdb")))
    }
    invisible()
}

# bitwise.R

bitwNot <- function(a) .Internal(bitwiseNot(a))

bitwAnd <- function(a, b) .Internal(bitwiseAnd(a, b))

bitwXor <- function(a, b) .Internal(bitwiseXor(a, b))

bitwShiftL <- function(a, n) .Internal(bitwiseShiftL(a, n))

bitwShiftR <- function(a, n) .Internal(bitwiseShiftR(a, n))

# sys.R

sys.call <- function(which = 0L)
    .Internal(sys.call(which))

# dataframe.R

data.frame <-
    function(..., row.names = NULL, check.rows = FALSE, check.names = TRUE,
	     fix.empty.names = TRUE,
             stringsAsFactors = default.stringsAsFactors())
{
    data.row.names <-
	if(check.rows && is.null(row.names)) {
	    function(current, new, i) {
		if(is.character(current)) new <- as.character(new)
		if(is.character(new)) current <- as.character(current)
		if(anyDuplicated(new))
		    return(current)
		if(is.null(current))
		    return(new)
		if(all(current == new) || all(current == ""))
		    return(new)
		stop(gettextf(
		    "mismatch of row names in arguments of 'data.frame\', item %d", i),
		    domain = NA)
	    }
    } else function(current, new, i) {
	    if(is.null(current)) {
		if(anyDuplicated(new)) {
		    warning(gettextf(
                        "some row.names duplicated: %s --> row.names NOT used",
                        paste(which(duplicated(new)), collapse=",")),
                        domain = NA)
		    current
		} else new
	    } else current
	}
    object <- as.list(substitute(list(...)))[-1L]
    mirn <- missing(row.names) # record before possibly changing
    mrn <- is.null(row.names) # missing or NULL
    x <- list(...)
    n <- length(x)
    if(n < 1L) {
        if(!mrn) {
            if(is.object(row.names) || !is.integer(row.names))
                row.names <- as.character(row.names)
            if(anyNA(row.names))
                stop("row names contain missing values")
            if(anyDuplicated(row.names))
                stop(gettextf("duplicate row.names: %s",
                              paste(unique(row.names[duplicated(row.names)]),
                                    collapse = ", ")),
                     domain = NA)
        } else row.names <- integer()
	return(structure(list(), names = character(),
                         row.names = row.names,
			 class = "data.frame"))
    }
    vnames <- names(x)
    if(length(vnames) != n)
	vnames <- character(n)
    no.vn <- !nzchar(vnames)
    vlist <- vnames <- as.list(vnames)
    nrows <- ncols <- integer(n)
    for(i in seq_len(n)) {
        ## do it this way until all as.data.frame methods have been updated
	xi <- if(is.character(x[[i]]) || is.list(x[[i]])) {
		  as.data.frame(x[[i]], optional = TRUE,
				stringsAsFactors = stringsAsFactors)
    } else as.data.frame(x[[i]], optional = TRUE)

        nrows[i] <- .row_names_info(xi) # signed for now
	ncols[i] <- length(xi)
	namesi <- names(xi)
	if(ncols[i] > 1L) {
	    if(length(namesi) == 0L) namesi <- seq_len(ncols[i])
	    vnames[[i]] <- if(no.vn[i]) namesi else paste(vnames[[i]], namesi, sep=".")
	} else if(length(namesi)) {
	    vnames[[i]] <- namesi
	} else if (fix.empty.names && no.vn[[i]]) {
	    tmpname <- deparse(object[[i]], nlines = 1L)[1L]
	    if(substr(tmpname, 1L, 2L) == "I(") { ## from 'I(*)', only keep '*':
		ntmpn <- nchar(tmpname, "c")
		if(substr(tmpname, ntmpn, ntmpn) == ")")
		    tmpname <- substr(tmpname, 3L, ntmpn - 1L)
	    }
	    vnames[[i]] <- tmpname
	} ## else vnames[[i]] are not changed
	if(mirn && nrows[i] > 0L) {
            rowsi <- attr(xi, "row.names")
            ## Avoid all-blank names
            if(any(nzchar(rowsi)))
                row.names <- data.row.names(row.names, rowsi, i)
        }
        nrows[i] <- abs(nrows[i])
	vlist[[i]] <- xi
    }
    nr <- max(nrows)
    for(i in seq_len(n)[nrows < nr]) {
	xi <- vlist[[i]]
	if(nrows[i] > 0L && (nr %% nrows[i] == 0L)) {
            ## make some attempt to recycle column i
            xi <- unclass(xi) # avoid data-frame methods
            fixed <- TRUE
            for(j in seq_along(xi)) {
                xi1 <- xi[[j]]
                if(is.vector(xi1) || is.factor(xi1)) {
                    xi[[j]] <- rep(xi1, length.out = nr)
                } else if(is.character(xi1) && inherits(xi1, "AsIs")) {
                    xi[[j]] <- structure(rep(xi1, length.out = nr),
                                         class = class(xi1))
                } else if(inherits(xi1, "Date") || inherits(xi1, "POSIXct")) {
                    xi[[j]] <- rep(xi1, length.out = nr)
                } else {
                    fixed <- FALSE
                    break
                }
            }
            if (fixed) {
                vlist[[i]] <- xi
                next
            }
        }
        stop(gettextf("arguments imply differing number of rows: %s",
                      paste(unique(nrows), collapse = ", ")),
             domain = NA)
    }
    value <- unlist(vlist, recursive=FALSE, use.names=FALSE)
    ## unlist() drops i-th component if it has 0 columns
    vnames <- unlist(vnames[ncols > 0L])
    if(fix.empty.names && any(noname <- !nzchar(vnames)))
	vnames[noname] <- paste0("Var.", seq_along(vnames))[noname]
    if(check.names) {
	if(fix.empty.names) {
	    vnames <- make.names(vnames, unique=TRUE)
    } else { ## do not fix ""
	    nz <- nzchar(vnames)
	    vnames[nz] <- make.names(vnames[nz], unique=TRUE)
	}
    }
    names(value) <- vnames
    if(!mrn) { # non-null row.names arg was supplied
        if(length(row.names) == 1L && nr != 1L) {  # one of the variables
            if(is.character(row.names))
                row.names <- match(row.names, vnames, 0L)
            if(length(row.names) != 1L ||
               row.names < 1L || row.names > length(vnames))
                stop("'row.names' should specify one of the variables")
            i <- row.names
            row.names <- value[[i]]
            value <- value[ - i]
        } else if ( !is.null(row.names) && length(row.names) != nr )
            stop("row names supplied are of the wrong length")
    } else if( !is.null(row.names) && length(row.names) != nr ) {
        warning("row names were found from a short variable and have been discarded")
        row.names <- NULL
    }
    if(is.null(row.names)) {
        row.names <- .set_row_names(nr) #seq_len(nr)
    }else {
        if(is.object(row.names) || !is.integer(row.names))
            row.names <- as.character(row.names)
        if(anyNA(row.names))
            stop("row names contain missing values")
        if(anyDuplicated(row.names))
            stop(gettextf("duplicate row.names: %s",
                          paste(unique(row.names[duplicated(row.names)]),
                                collapse = ", ")),
                 domain = NA)
    }
    attr(value, "row.names") <- row.names
    attr(value, "class") <- "data.frame"
    value
}

# diff.R
diff <- function(x, ...) UseMethod("diff")

# factor.R
factor <- function(x = character(), levels, labels = levels,
                   exclude = NA, ordered = is.ordered(x), nmax = NA)
{
    if(is.null(x)) x <- character()
    nx <- names(x)
    if (missing(levels)) {
	y <- unique(x, nmax = nmax)
	ind <- sort.list(y) # or possibly order(x) which is more (too ?) tolerant
	levels <- unique(as.character(y)[ind])
    }
    force(ordered) # check if original x is an ordered factor
    if(!is.character(x))
	x <- as.character(x)
    ## levels could be a long vectors, but match will not handle that.
    levels <- levels[is.na(match(levels, exclude))]
    f <- match(x, levels)
    if(!is.null(nx))
	names(f) <- nx
    nl <- length(labels)
    nL <- length(levels)
    if(!any(nl == c(1L, nL)))
	stop(gettextf("invalid 'labels'; length %d should be 1 or %d", nl, nL),
	     domain = NA)
    levels(f) <- ## nl == nL or 1
	if (nl == nL) as.character(labels)	else paste0(labels, seq_along(levels))
    class(f) <- c(if(ordered) "ordered", "factor")
    f
}



# stats/R/models.R
as.formula <- function(object, env = parent.frame())
{
    if(inherits(object, "formula"))
        object
    else {
        rval <- formula(object, env = baseenv())
        if (identical(environment(rval), baseenv()) || !missing(env))
            environment(rval) <- env
        rval
    }
}

# datetime.R
Sys.time <- function() .POSIXct(.Internal(Sys.time()))
