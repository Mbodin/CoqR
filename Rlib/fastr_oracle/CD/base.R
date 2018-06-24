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

# New-Internal.R
.deparseOpts <- function(control) {
    opts <- pmatch(as.character(control),
                   ## the exact order of these is determined by the integer codes in
                   ## ../../../include/Defn.h
                   c("all",
                     "keepInteger", "quoteExpressions", "showAttributes",
                     "useSource", "warnIncomplete", "delayPromises",
                     "keepNA", "S_compatible", "hexNumeric", "digits17"))
    if (anyNA(opts))
        stop(sprintf(ngettext(as.integer(sum(is.na(opts))),
                              "deparse option %s is not recognized",
                              "deparse options %s are not recognized"),
                     paste(sQuote(control[is.na(opts)]), collapse=", ")),
             call. = FALSE, domain = NA)
    if (any(opts == 1L))
        opts <- unique(c(opts[opts != 1L], 2L,3L,4L,5L,6L,8L)) # not (7,9:11)
    if(10L %in% opts && 11L %in% opts)
        stop('"hexNumeric" and "digits17" are mutually exclusive')
    return(sum(2^(opts-2)))
}

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


cat <- function(..., file = "", sep = " ", fill = FALSE,
                labels = NULL, append = FALSE)
{
    if(is.character(file))
        if(file == "") file <- stdout()
        else if(substring(file, 1L, 1L) == "|") {
            file <- pipe(substring(file, 2L), "w")
            on.exit(close(file))
        } else {
            file <- file(file, ifelse(append, "a", "w"))
            on.exit(close(file))
        }
    .Internal(cat(list(...), file, sep, fill, labels, append))
}


cbind <- function(..., deparse.level = 1)
{
    has.dl <- !missing(deparse.level)
    deparse.level <- as.integer(deparse.level)
    if(identical(deparse.level, -1L)) deparse.level <- 0L # our hack
    stopifnot(0 <= deparse.level, deparse.level <= 2)

    argl <- list(...)
    ## remove trailing 'NULL's:
    na <- nargs() - has.dl
    while(na > 0L && is.null(argl[[na]])) { argl <- argl[-na]; na <- na - 1L }
    if(na == 0) return(NULL)
    symarg <- as.list(substitute(list(...)))[-1L] # symbolic argument (names)
    nmsym <- names(symarg)
    ## Give *names* depending on deparse.level {for non-matrix}:
    nm <- c( ## 0:
	function(i) NULL,
	## 1:
	function(i) if(is.symbol(s <- symarg[[i]])) deparse(s) else NULL,
	## 2:
	function(i) deparse(symarg[[i]])[[1L]])[[ 1L + deparse.level ]]
    Nms <- function(i) { if(!is.null(s <- nmsym[i]) && nzchar(s)) s else nm(i) }
    if(na == 1) {
	if(isS4(..1)) {
	    r <- cbind2(..1)
	    if(length(dim(..1)) < 2L && length(dim(r)) == 2L)
		colnames(r) <- Nms(1)
	    return(r)
	}
	else return(.__H__.cbind(..., deparse.level = deparse.level))
    }

    ## else :  na >= 2

    if(na == 2) {
	r <- ..2
	fix.na <- FALSE
    }
    else { ## na >= 3 arguments: -- RECURSION -- with care
	## determine nrow(<result>)  for e.g.,	cbind(diag(2), 1, 2)
	## only when the last two argument have *no* dim attribute:
	nrs <- unname(lapply(argl, nrow)) # of length na
	iV <- vapply(nrs, is.null, NA)# is 'vector'
	fix.na <- identical(nrs[(na-1L):na], list(NULL,NULL))
	if(fix.na) {
	    ## "fix" last argument, using 1-column `matrix' of proper nrow():
	    nr <- max(if(all(iV)) lengths(argl) else unlist(nrs[!iV]))
	    argl[[na]] <- cbind(rep(argl[[na]], length.out = nr),
				deparse.level = 0)
	    ## and since it's a 'matrix' now, cbind() below may not name it
	}
	## need to pass argl, the evaluated arg list to do.call();
	## OTOH, these may have lost their original 'symbols'
	## if(deparse.level) {
	    if(fix.na)
		fix.na <- !is.null(Nna <- Nms(na))
	    if(!is.null(nmi <- names(argl))) iV <- iV & (nmi == "")
	    ## attach `symbols' to argl[-1L] for 'vectors'[iV]
	    ii <- if(fix.na) # need to fix later ([na] is 'matrix')
		2:(na-1) else 2:na
	    if(any(iV[ii])) {
		for(i in ii[iV[ii]])
		    if (!is.null(nmi <- Nms(i))) names(argl)[i] <- nmi
	    }
	## }
	r <- do.call(cbind, c(argl[-1L], list(deparse.level=deparse.level)))
    }

    d2 <- dim(r)
    r <- cbind2(..1, r)
    ## if(deparse.level == 0)
    ##     return(r)
    ism1 <- !is.null(d1 <- dim(..1)) && length(d1) == 2L
    ism2 <- !is.null(d2)	     && length(d2) == 2L && !fix.na
    if(ism1 && ism2) ## two matrices
	return(r)

    ## else -- Setting colnames correctly
    ##	       when one was not a matrix [needs some diligence!]
    Ncol <- function(x) {
	d <- dim(x); if(length(d) == 2L) d[2L] else as.integer(length(x) > 0L) }
    nn1 <- !is.null(N1 <- if(    (l1 <- Ncol(..1)) && !ism1) Nms(1)) # else NULL
    nn2 <- !is.null(N2 <- if(na == 2 && Ncol(..2)  && !ism2) Nms(2))
    if(nn1 || nn2 || fix.na) {
	if(is.null(colnames(r)))
	    colnames(r) <- rep.int("", ncol(r))
	setN <- function(i, nams)
	    colnames(r)[i] <<- if(is.null(nams)) "" else nams
	if(nn1) setN(1,	 N1)
	if(nn2) setN(1+l1, N2)
	if(fix.na) setN(ncol(r), Nna)
    }
    r
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

NROW <- function(x) if(length(d <- dim(x)))      d[1L] else length(x)
NCOL <- function(x) if(length(d <- dim(x)) > 1L) d[2L] else 1L

rownames <- function(x, do.NULL = TRUE, prefix = "row")
{
    dn <- dimnames(x)
    if(!is.null(dn[[1L]])) {
	dn[[1L]]
    } else {
        nr <- NROW(x)
	if(do.NULL) {
        NULL
    } else if(nr > 0L) {
            paste0(prefix, seq_len(nr))
    } else character()
    }
}

`rownames<-` <- function(x, value)
{
    if(is.data.frame(x)) {
        row.names(x) <- value
    } else {
        dn <- dimnames(x)
        if(is.null(dn)) {
            if(is.null(value)) return(x)
            if((nd <- length(dim(x))) < 1L)
                stop("attempt to set 'rownames' on an object with no dimensions")
            dn <- vector("list", nd)
        }
        if(length(dn) < 1L)
            stop("attempt to set 'rownames' on an object with no dimensions")
        if(is.null(value)) dn[1L] <- list(NULL) else dn[[1L]] <- value
        dimnames(x) <- dn
    }
    x
}

colnames <- function(x, do.NULL = TRUE, prefix = "col")
{
    if(is.data.frame(x) && do.NULL)
	return(names(x))
    dn <- dimnames(x)
    if(!is.null(dn[[2L]])) {
	dn[[2L]]
    } else {
        nc <- NCOL(x)
	if(do.NULL) {
        NULL
    } else if(nc > 0L) {
            paste0(prefix, seq_len(nc))
    } else character()
    }
}

`colnames<-` <- function(x, value)
{
    if(is.data.frame(x)) {
        names(x) <- value
    } else {
        dn <- dimnames(x)
        if(is.null(dn)) {
            if(is.null(value)) return(x)
            if((nd <- length(dim(x))) < 2L)
                stop("attempt to set 'colnames' on an object with less than two dimensions")
            dn <- vector("list", nd)
        }
        if(length(dn) < 2L)
            stop("attempt to set 'colnames' on an object with less than two dimensions")
        if(is.null(value)) dn[2L] <- list(NULL) else dn[[2L]] <- value
        dimnames(x) <- dn
    }
    x
}

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
tcrossprod <- function(x, y=NULL) .Internal(tcrossprod(x,y))

t <- function(x) UseMethod("t")
## t.default is <primitive>
t.data.frame <- function(x)
{
    x <- as.matrix(x)
    NextMethod("t")
}

# colSums.R

colSums <- function(x, na.rm = FALSE, dims = 1L)
{
    if(is.data.frame(x)) x <- as.matrix(x)
    if(!is.array(x) || length(dn <- dim(x)) < 2L)
        stop("'x' must be an array of at least two dimensions")
    if(dims < 1L || dims > length(dn) - 1L)
        stop("invalid 'dims'")
    n <- prod(dn[id <- seq_len(dims)])
    dn <- dn[-id]
    z <- if(is.complex(x)) {
        .Internal(colSums(Re(x), n, prod(dn), na.rm)) +
            1i * .Internal(colSums(Im(x), n, prod(dn), na.rm))
    } else .Internal(colSums(x, n, prod(dn), na.rm))
    if(length(dn) > 1L) {
        dim(z) <- dn
        dimnames(z) <- dimnames(x)[-id]
    } else names(z) <- dimnames(x)[[dims+1L]]
    z
}

colMeans <- function(x, na.rm = FALSE, dims = 1L)
{
    if(is.data.frame(x)) x <- as.matrix(x)
    if(!is.array(x) || length(dn <- dim(x)) < 2L)
        stop("'x' must be an array of at least two dimensions")
    if(dims < 1L || dims > length(dn) - 1L)
        stop("invalid 'dims'")
    n <- prod(dn[id <- seq_len(dims)])
    dn <- dn[-id]
    z <- if(is.complex(x)) {
        .Internal(colMeans(Re(x), n, prod(dn), na.rm)) +
            1i * .Internal(colMeans(Im(x), n, prod(dn), na.rm))
    } else .Internal(colMeans(x, n, prod(dn), na.rm))
    if(length(dn) > 1L) {
        dim(z) <- dn
        dimnames(z) <- dimnames(x)[-id]
    } else names(z) <- dimnames(x)[[dims+1L]]
    z
}

rowSums <- function(x, na.rm = FALSE, dims = 1L)
{
    if(is.data.frame(x)) x <- as.matrix(x)
    if(!is.array(x) || length(dn <- dim(x)) < 2L)
        stop("'x' must be an array of at least two dimensions")
    if(dims < 1L || dims > length(dn) - 1L)
        stop("invalid 'dims'")
    p <- prod(dn[-(id <- seq_len(dims))])
    dn <- dn[id]
    z <- if(is.complex(x)) {
        .Internal(rowSums(Re(x), prod(dn), p, na.rm)) +
            1i * .Internal(rowSums(Im(x), prod(dn), p, na.rm))
    } else .Internal(rowSums(x, prod(dn), p, na.rm))
    if(length(dn) > 1L) {
        dim(z) <- dn
        dimnames(z) <- dimnames(x)[id]
    } else names(z) <- dimnames(x)[[1L]]
    z
}

rowMeans <- function(x, na.rm = FALSE, dims = 1L)
{
    if(is.data.frame(x)) x <- as.matrix(x)
    if(!is.array(x) || length(dn <- dim(x)) < 2L)
        stop("'x' must be an array of at least two dimensions")
    if(dims < 1L || dims > length(dn) - 1L)
        stop("invalid 'dims'")
    p <- prod(dn[-(id <- seq_len(dims))])
    dn <- dn[id]
    z <- if(is.complex(x)) {
        .Internal(rowMeans(Re(x), prod(dn), p, na.rm)) +
            1i * .Internal(rowMeans(Im(x), prod(dn), p, na.rm))
    } else .Internal(rowMeans(x, prod(dn), p, na.rm))
    if(length(dn) > 1L) {
        dim(z) <- dn
        dimnames(z) <- dimnames(x)[id]
    } else names(z) <- dimnames(x)[[1L]]
    z
}

# det.R
det <- function(x, ...)
{
    z <- determinant(x, logarithm = TRUE, ...)
    c(z$sign * exp(z$modulus))
}

determinant <- function(x, logarithm = TRUE, ...) UseMethod("determinant")

# duplicated.R

duplicated <- function(x, incomparables = FALSE, ...) UseMethod("duplicated")


# dataframe.R
is.data.frame <- function(x) inherits(x, "data.frame")

# dput.R

dput <-
    function(x, file = "",
             control = c("keepNA", "keepInteger", "showAttributes"))
{
    if(is.character(file))
        if(nzchar(file)) {
            file <- file(file, "wt")
            on.exit(close(file))
        } else file <- stdout()
    opts <- .deparseOpts(control)
    ## FIXME: this should happen in C {deparse2() in ../../../main/deparse.c}
    ##        but we are missing a C-level slotNames()
    ## Fails e.g. if an S3 list-like object has S4 components
    if(isS4(x)) {
	clx <- class(x)
	cat('new("', clx,'"\n', file = file, sep = "")
	for(n in methods::.slotNames(clx)) {
	    cat("    ,", n, "= ", file = file)
	    dput(methods::slot(x, n), file = file, control = control)
	}
	cat(")\n", file = file)
	invisible()
    }
    else .Internal(dput(x, file, opts))
}

# match.R
charmatch <- function(x, table, nomatch = NA_integer_)
    .Internal(charmatch(as.character(x), as.character(table), nomatch))

# diag.R
diag <- function(x = 1, nrow, ncol)
{
    if (is.matrix(x)) {
        if (nargs() > 1L)
            stop("'nrow' or 'ncol' cannot be specified when 'x' is a matrix")

        if((m <- min(dim(x))) == 0L) return(vector(typeof(x), 0L))
        ## NB: need double index to avoid overflows.
        y <- x[1 + 0L:(m - 1L) * (dim(x)[1L] + 1)]
        nms <- dimnames(x)
        if (is.list(nms) && !any(sapply(nms, is.null)) &&
            identical((nm <- nms[[1L]][seq_len(m)]), nms[[2L]][seq_len(m)]))
            names(y) <- nm
        return(y)
    }
    if (is.array(x) && length(dim(x)) != 1L)
        stop("'x' is an array, but not one-dimensional.")

    if (missing(x)) n <- nrow
    else if (length(x) == 1L && nargs() == 1L) {
	n <- as.integer(x)
	x <- 1
    } else n <- length(x)
    if (!missing(nrow)) n <- nrow
    if (missing(ncol)) ncol <- n
    ## some people worry about speed
    .Internal(diag(x, n, ncol))
}

`diag<-` <- function(x, value)
{
    dx <- dim(x)
    if (length(dx) != 2L)
	## no further check, to also work with 'Matrix'
	stop("only matrix diagonals can be replaced")
    len.i <- min(dx)
    len.v <- length(value)
    if (len.v != 1L && len.v != len.i)
	stop("replacement diagonal has wrong length")
    if (len.i) {
	i <- seq_len(len.i)
	x[cbind(i, i)] <- value
    }
    x
}

# deriv.R
deriv <- function(expr, ...) UseMethod("deriv")

# assign.R
assign <-
    function (x, value, pos = -1, envir = as.environment(pos),
              inherits = FALSE, immediate = TRUE)
    .Internal(assign(x, value, envir, inherits))

# delay.R
delayedAssign <-
    function(x, value, eval.env=parent.frame(1), assign.env=parent.frame(1))
    .Internal(delayedAssign(x, substitute(value), eval.env, assign.env))

# connections.R
stdout <- function() .Internal(stdout())

# character.R

chartr <- function(old, new, x)
{
    if(!is.character(x)) x <- as.character(x)
    .Internal(chartr(old, new, x))
}

# chol.R
chol <- function(x, ...) UseMethod("chol")

# as.R
as.vector <- function(x, mode = "any") .Internal(as.vector(x, mode))

as.symbol <- function(x) .Internal(as.vector(x, "symbol"))
