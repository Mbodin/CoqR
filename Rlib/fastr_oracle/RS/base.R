# array.R
array <-
function(data = NA, dim = length(data), dimnames = NULL)
{
    ## allow for as.vector.factor (converts to character)
    if(is.atomic(data) && !is.object(data))
        return(.Internal(array(data, dim, dimnames)))
    data <- as.vector(data)
    ## package rv has an as.vector() method which leave this as a classed list
    if(is.object(data)) {
        dim <- as.integer(dim)
        if (!length(dim)) stop("'dims' cannot be of length 0")
        vl <- prod(dim)
        if(length(data) != vl) {
            ## C code allows long vectors, but rep() does not.
            if(vl > .Machine$integer.max)
                stop("'dim' specifies too large an array")
            data <- rep_len(data, vl)
        }
        if(length(dim)) dim(data) <- dim
        if(is.list(dimnames) && length(dimnames)) dimnames(data) <- dimnames
        data
    } else .Internal(array(data, dim, dimnames))
}

# assign.R
assign <-
    function (x, value, pos = -1, envir = as.environment(pos),
              inherits = FALSE, immediate = TRUE)
    .Internal(assign(x, value, envir, inherits))

# as.R
as.list <- function(x,...) UseMethod("as.list")

as.vector <- function(x, mode = "any") .Internal(as.vector(x, mode))
as.symbol <- function(x) .Internal(as.vector(x, "symbol"))
as.name <- as.symbol

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

typeof <- function(x) .Internal(typeof(x))

inherits <- function(x, what, which = FALSE)
	.Internal(inherits(x, what, which))

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

do.call <- function(what, args, quote = FALSE, envir = parent.frame())
{
    if (!is.list(args))
	stop("second argument must be a list")
    if (quote)
	args <- lapply(args, enquote)
    .Internal(do.call(what, args, envir))
}


rbind <- function(..., deparse.level = 1)
    .Internal(rbind(deparse.level, ...))


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


sprintf <- function(fmt, ...) .Internal(sprintf(fmt, ...))

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

# cat.R
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

# cbind.R
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


# serialize.R

serialize <-
    function(object, connection, ascii = FALSE, xdr = TRUE,
             version = NULL, refhook = NULL)
{
    if (!is.null(connection)) {
        if (!inherits(connection, "connection"))
            stop("'connection' must be a connection")
        if (missing(ascii)) ascii <- summary(connection)$text == "text"
    }
    if (!ascii && inherits(connection, "sockconn")) {
        .Internal(serializeb(object, connection, xdr, version, refhook))
    } else {
	type <- if(is.na(ascii)) 2L else if(ascii) 1L else if(!xdr) 3L else 0L
        .Internal(serialize(object, connection, type, version, refhook))
    }
}

unserialize <- function(connection, refhook = NULL)
{
    if (typeof(connection) != "raw" &&
        !is.character(connection) &&
        !inherits(connection, "connection"))
        stop("'connection' must be a connection")
    .Internal(unserialize(connection, refhook))
}

# options.r

options <- function(...)
    .Internal(options(...))

# RNG.R
set.seed <- function(seed, kind = NULL, normal.kind = NULL)
{
    kinds <- c("Wichmann-Hill", "Marsaglia-Multicarry", "Super-Duper",
               "Mersenne-Twister", "Knuth-TAOCP", "user-supplied",
               "Knuth-TAOCP-2002", "L'Ecuyer-CMRG", "default")
    n.kinds <- c("Buggy Kinderman-Ramage", "Ahrens-Dieter", "Box-Muller",
                 "user-supplied", "Inversion", "Kinderman-Ramage",
		 "default")
    if(length(kind) ) {
	if(!is.character(kind) || length(kind) > 1L)
	    stop("'kind' must be a character string of length 1 (RNG to be used).")
	if(is.na(i.knd <- pmatch(kind, kinds) - 1L))
	    stop(gettextf("'%s' is not a valid abbreviation of an RNG", kind),
                 domain = NA)
        if(i.knd == length(kinds) - 1L) i.knd <- -1L
    } else i.knd <- NULL

    if(!is.null(normal.kind)) {
	if(!is.character(normal.kind) || length(normal.kind) != 1L)
	    stop("'normal.kind' must be a character string of length 1")
        normal.kind <- pmatch(normal.kind, n.kinds) - 1L
        if(is.na(normal.kind))
	    stop(gettextf("'%s' is not a valid choice", normal.kind),
                 domain = NA)
	if (normal.kind == 0L)
            stop("buggy version of Kinderman-Ramage generator is not allowed",
                 domain = NA)
         if(normal.kind == length(n.kinds) - 1L) normal.kind <- -1L
    }
    .Internal(set.seed(seed, i.knd, normal.kind))
}


# sys.R

sys.parent <- function(n = 1L)
    .Internal(sys.parent(n))

sys.call <- function(which = 0L)
    .Internal(sys.call(which))

sys.calls <- function()
    .Internal(sys.calls())

sys.parents <- function()
    .Internal(sys.parents())

sys.nframe <- function()
    .Internal(sys.nframe())

sys.function <- function(which = 0L)
    .Internal(sys.function(which))


# rep.R
rep.int <- function(x, times) .Internal(rep.int(x, times))

rep_len <- function(x, length.out) .Internal(rep_len(x, length.out))

# rank.R
rank <- function(x, na.last = TRUE,
		 ties.method = c("average", "first", "last", "random", "max", "min"))
{
    nas <- is.na(x)
    nm <- names(x)
    ties.method <- match.arg(ties.method)
    ## To preserve past behaviour
    if(is.factor(x)) x <- as.integer(x)
    x <- x[!nas]
    ## we pass length(x) to allow
    y <- switch(ties.method,
		"average" = , "min" = , "max" =
		.Internal(rank(x, length(x), ties.method)),
		"first" = sort.list(sort.list(x)),
		"last"  = ## == rev(sort.list(sort.list(rev(x)))) :
		    sort.list(rev.default(sort.list(x, decreasing=TRUE))),
		"random" = sort.list(order(x, stats::runif(sum(!nas)))))
    ## the internal code has ranks in [1, length(y)]
    if(!is.na(na.last) && any(nas)) {
	yy <- NA
	NAkeep <- (na.last == "keep")
	if(NAkeep || na.last) {
	    yy[!nas] <- y
	    if(!NAkeep) yy[nas] <- (length(y) + 1L) : length(yy)
	} else {
	    len <- sum(nas)
	    yy[!nas] <- y + len
	    yy[nas] <- seq_len(len)
	}
	y <- yy
	names(y) <- nm
    } else names(y) <- nm[!nas]
    y
}


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

# conditions.R
tryCatch <- function(expr, ..., finally) {
    tryCatchList <- function(expr, names, parentenv, handlers) {
	nh <- length(names)
	if (nh > 1L) {
	    tryCatchOne(tryCatchList(expr, names[-nh], parentenv,
                                     handlers[-nh]),
			names[nh], parentenv, handlers[[nh]])
    } else if (nh == 1L) {
	    tryCatchOne(expr, names, parentenv, handlers[[1L]])
    } else expr
    }
    tryCatchOne <- function(expr, name, parentenv, handler) {
	doTryCatch <- function(expr, name, parentenv, handler) {
	    .Internal(.addCondHands(name, list(handler), parentenv,
				    environment(), FALSE))
	    expr
	}
	value <- doTryCatch(return(expr), name, parentenv, handler)
	# The return in the call above will exit withOneRestart unless
	# the handler is invoked; we only get to this point if the handler
	# is invoked.  If we get here then the handler will have been
	# popped off the internal handler stack.
	if (is.null(value[[1L]])) {
	    # a simple error; message is stored internally
	    # and call is in result; this defers all allocs until
	    # after the jump
	    msg <- .Internal(geterrmessage())
	    call <- value[[2L]]
	    cond <- simpleError(msg, call)
	} else cond <- value[[1L]]
	value[[3L]](cond)
    }
    if (! missing(finally))
        on.exit(finally)
    handlers <- list(...)
    classes <- names(handlers)
    parentenv <- parent.frame()
    if (length(classes) != length(handlers))
        stop("bad handler specification")
    tryCatchList(expr, classes, parentenv, handlers)
}

# print.R
print <- function(x, ...) UseMethod("print")

# getenv.R
Sys.getenv <- function(x = NULL, unset = "", names = NA)
{
    if (is.null(x)) {
        ## This presumes that '=' does not appear as part of the name
        ## of an environment variable.  That used to happen on Windows.
	x <- strsplit(.Internal(Sys.getenv(character(), "")), "=", fixed=TRUE)
	v <- n <- character(LEN <- length(x))
	for (i in 1L:LEN) {
	    n[i] <- x[[i]][1L]
	    v[i] <- paste(x[[i]][-1L], collapse = "=")
	}
	if (identical(names, FALSE)) {
	    v[sort.list(n)]
	} else { # with names
	    v <- structure(v, names = n)
	    structure(class = "Dlist", # with nice print method
		      v[sort.list(n)])
	}
    } else {
        v <- .Internal(Sys.getenv(as.character(x), as.character(unset)))
	if (isTRUE(names) || (length(x) > 1L && !identical(names, FALSE))) structure(v, names = x) else v
    }
}

Sys.setenv <- function(...)
{
    x <- list(...)
    nm <- names(x)
    if(is.null(nm) || "" %in% nm)
        stop("all arguments must be named")
    .Internal(Sys.setenv(nm, as.character(unlist(x))))
}

# character.R
substring <- function(text, first, last=1000000L)
{
    if(!is.character(text)) text <- as.character(text)
    n <- max(lt <- length(text), length(first), length(last))
    if(lt && lt < n) text <- rep_len(text, length.out = n)
    .Internal(substr(text, as.integer(first), as.integer(last)))
}

substr <- function(x, start, stop)
{
    if(!is.character(x)) x <- as.character(x)
    .Internal(substr(x, as.integer(start), as.integer(stop)))
}

`substr<-` <- function(x, start, stop, value)
    .Internal(`substr<-`(x, as.integer(start), as.integer(stop), value))

strrep <-
function(x, times)
{
    if(!is.character(x)) x <- as.character(x)
    .Internal(strrep(x, as.integer(times)))
}
startsWith <- function(x, prefix) .Internal(startsWith(x, prefix))

endsWith   <- function(x, suffix) .Internal(endsWith  (x, suffix))

# raw.R
raw <- function(length = 0L) .Internal(vector("raw", length))

rawToBits <- function(x) .Internal(rawToBits(x))

# sets.R
setdiff <- function(x, y)
{
    x <- as.vector(x)
    y <- as.vector(y)
    unique(if(length(x) || length(y)) x[match(x, y, 0L) == 0L] else x)
}

# grep.R
strsplit <-
function(x, split, fixed = FALSE, perl = FALSE, useBytes = FALSE)
    .Internal(strsplit(x, as.character(split), fixed, perl, useBytes))


regexpr <-
function(pattern, text, ignore.case = FALSE, perl = FALSE,
         fixed = FALSE, useBytes = FALSE)
{
    if (!is.character(text)) text <- as.character(text)
    .Internal(regexpr(as.character(pattern), text,
                      ignore.case, perl, fixed, useBytes))
}

# bindenv.R
makeActiveBinding <- function(sym, fun, env) {
    if (is.character(sym)) sym <- as.name(sym)
    .Internal(makeActiveBinding(sym, fun, env))
}

# duplicated.R
unique <- function(x, incomparables = FALSE, ...) UseMethod("unique")


# mode.R
storage.mode <- function(x)
    switch(tx <- typeof(x),
	   closure = , builtin = , special = "function",
	   ## otherwise
	   tx)

# rm.R

rm <-
    function (..., list = character(), pos = -1, envir = as.environment(pos),
              inherits = FALSE)
{
    dots <- match.call(expand.dots=FALSE)$...
    if(length(dots) &&
       !all(vapply(dots, function(x) is.symbol(x) || is.character(x), NA, USE.NAMES=FALSE)))
       stop("... must contain names or character strings")
    names <- vapply(dots, as.character, "")
    if (length(names) == 0L) names <- character()
    list <- .Primitive("c")(list, names)
    .Internal(remove(list, envir, inherits))
}

remove <- rm

# connections.R
stdout <- function() .Internal(stdout())

readChar <- function(con, nchars, useBytes = FALSE)
{
    if(is.character(con)) {
        con <- file(con, "rb")
        on.exit(close(con))
    }
    .Internal(readChar(con, as.integer(nchars), useBytes))
}
rawConnection <- function(object, open = "r") {
    .Internal(rawConnection(deparse(substitute(object)), object, open))
}

# strwrap.R
strtrim <- function(x, width)
{
    if(!is.character(x)) x <- as.character(x)
    .Internal(strtrim(x, width))
}

# sample.R
sample <- function(x, size, replace = FALSE, prob = NULL)
{
    if(length(x) == 1L && is.numeric(x) && is.finite(x) && x >= 1) {
	if(missing(size)) size <- x
	sample.int(x, size, replace, prob)
    } else {
	if(missing(size)) size <- length(x)
	x[sample.int(length(x), size, replace, prob)]
    }
}

# sweep.R
sweep <- function(x, MARGIN, STATS, FUN = "-", check.margin = TRUE, ...)
{
    FUN <- match.fun(FUN)
    dims <- dim(x)
    if (check.margin) {
        dimmargin <- dims[MARGIN]
        dimstats <- dim(STATS)
        lstats <- length(STATS)
        if (lstats > prod(dimmargin)) {
            warning("STATS is longer than the extent of 'dim(x)[MARGIN]'")
        } else if (is.null(dimstats)) { # STATS is a vector
            cumDim <- c(1L, cumprod(dimmargin))
            upper <- min(cumDim[cumDim >= lstats])
            lower <- max(cumDim[cumDim <= lstats])
            if (lstats && (upper %% lstats != 0L || lstats %% lower != 0L))
                warning("STATS does not recycle exactly across MARGIN")
        } else {
            dimmargin <- dimmargin[dimmargin > 1L]
            dimstats <- dimstats[dimstats > 1L]
            if (length(dimstats) != length(dimmargin) ||
                any(dimstats != dimmargin))
                warning("length(STATS) or dim(STATS) do not match dim(x)[MARGIN]")
        }
    }
    perm <- c(MARGIN, seq_along(dims)[ - MARGIN])
    FUN(x, aperm(array(STATS, dims[perm]), order(perm)), ...)
}

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

# split.R
split <- function(x, f, drop = FALSE, ...) UseMethod("split")

# delay.R
delayedAssign <-
    function(x, value, eval.env=parent.frame(1), assign.env=parent.frame(1))
    .Internal(delayedAssign(x, substitute(value), eval.env, assign.env))

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

as.data.frame <- function(x, row.names = NULL, optional = FALSE, ...)
{
    if(is.null(x))			# can't assign class to NULL
	return(as.data.frame(list()))
    UseMethod("as.data.frame")
}

is.data.frame <- function(x) inherits(x, "data.frame")

# seq.R
seq <- function(...) UseMethod("seq")

# match.R
match <- function(x, table, nomatch = NA_integer_, incomparables = NULL)
    .Internal(match(x, table, nomatch, incomparables))

match.call <-
    function(definition=sys.function(sys.parent()),
             call=sys.call(sys.parent()), expand.dots=TRUE,
             envir=parent.frame(2L))
{
    if (!missing(definition) && is.null(definition)) {
        definition <- sys.function(sys.parent())
    }
    .Internal(match.call(definition,call,expand.dots,envir))
}

pmatch <- function(x, table, nomatch = NA_integer_, duplicates.ok = FALSE)
    .Internal(pmatch(as.character(x), as.character(table), nomatch,

# sort.R
sort <- function(x, decreasing = FALSE, ...)
{
    if(!is.logical(decreasing) || length(decreasing) != 1L)
        stop("'decreasing' must be a length-1 logical vector.\nDid you intend to set 'partial'?")
    UseMethod("sort")
}

# stop.R
stop <- function(..., call. = TRUE, domain = NULL)
{
    args <- list(...)
    if (length(args) == 1L && inherits(args[[1L]], "condition")) {
        cond <- args[[1L]]
        if(nargs() > 1L)
            warning("additional arguments ignored in stop()")
        message <- conditionMessage(cond)
        call <- conditionCall(cond)
        .Internal(.signalCondition(cond, message, call))
        .Internal(.dfltStop(message, call))
    } else        .Internal(stop(call., .makeMessage(..., domain = domain)))
}

# locales.R
Sys.setlocale <- function(category = "LC_ALL", locale = "")
{
    category <- match(category, c("LC_ALL", "LC_COLLATE", "LC_CTYPE",
                                  "LC_MONETARY", "LC_NUMERIC", "LC_TIME",
                                  "LC_MESSAGES", "LC_PAPER", "LC_MEASUREMENT"))
    if(is.na(category)) stop("invalid 'category' argument")
    .Internal(Sys.setlocale(category, locale))
}

# summary.R
summary <- function (object, ...) UseMethod("summary")

# sapply.R
simplify2array <- function(x, higher = TRUE)
{
    if(length(common.len <- unique(lengths(x))) > 1L)
        return(x)
    if(common.len == 1L) {
        unlist(x, recursive = FALSE)
    } else if(common.len > 1L) {
        n <- length(x)
        ## make sure that array(*) will not call rep() {e.g. for 'call's}:
	r <- unlist(x, recursive = FALSE, use.names = FALSE)
        if(higher && length(c.dim <- unique(lapply(x, dim))) == 1 &&
           is.numeric(c.dim <- c.dim[[1L]]) &&
           prod(d <- c(c.dim, n)) == length(r)) {

            iN1 <- is.null(n1 <- dimnames(x[[1L]]))
            n2 <- names(x)
            dnam <-
                if(!(iN1 && is.null(n2)))
                    c(if(iN1) rep.int(list(n1), length(c.dim)) else n1,
                      list(n2)) ## else NULL
            array(r, dim = d, dimnames = dnam)

        } else if(prod(d <- c(common.len, n)) == length(r)) {
            array(r, dim = d,
                  dimnames = if(!(is.null(n1 <- names(x[[1L]])) &
                  is.null(n2 <- names(x)))) list(n1,n2))
        } else x
    } else x
}

sapply <- function(X, FUN, ..., simplify = TRUE, USE.NAMES = TRUE)
{
    FUN <- match.fun(FUN)
    answer <- lapply(X = X, FUN = FUN, ...)
    if(USE.NAMES && is.character(X) && is.null(names(answer)))
	names(answer) <- X
    if(!identical(simplify, FALSE) && length(answer)) {
	simplify2array(answer, higher = (simplify == "array"))
    } else answer
}

# rev.R
rev <- function(x) UseMethod("rev")

# outer.R

outer <- function (X, Y, FUN = "*", ...)
{
    if(is.array(X)) {
        dX <- dim(X)
        nx <- dimnames(X)
        no.nx <- is.null(nx)
    } else { # a vector
        dX <- length(X)  # cannot be long, as form a matrix below
        no.nx <- is.null(names(X))
        if(!no.nx) nx <- list(names(X))
    }
    if(is.array(Y)) {
        dY <- dim(Y)
        ny <- dimnames(Y)
        no.ny <- is.null(ny)
    } else { # a vector
        dY <- length(Y)
        no.ny <- is.null(names(Y))
        if(!no.ny) ny <- list(names(Y))
    }
    robj <-
        if (is.character(FUN) && FUN=="*") {
            if(!missing(...)) stop('using ... with FUN = "*" is an error')
            ## this is for numeric vectors, so dropping attributes is OK
            as.vector(X) %*% t(as.vector(Y))
        } else {
            FUN <- match.fun(FUN)
            ## Y may have a class, so don't use rep.int
            Y <- rep(Y, rep.int(length(X), length(Y)))
            ##  length.out is not an argument of the generic rep()
            ##  X <- rep(X, length.out = length(Y))
            if(length(X))
                X <- rep(X, times = ceiling(length(Y)/length(X)))
            FUN(X, Y, ...)
        }
    dim(robj) <- c(dX, dY) # careful not to lose class here
    ## no dimnames if both don't have ..
    if(!(no.nx && no.ny)) {
	if(no.nx) nx <- vector("list", length(dX)) else
	if(no.ny) ny <- vector("list", length(dY))
	dimnames(robj) <- c(nx, ny)
    }
    robj
}

# identical.R
identical <- function(x, y, num.eq = TRUE, single.NA = TRUE,
                      attrib.as.set = TRUE, ignore.bytecode = TRUE,
                      ignore.environment = FALSE, ignore.srcref = TRUE)
    .Internal(identical(x,y, num.eq, single.NA, attrib.as.set,
                        ignore.bytecode, ignore.environment, ignore.srcref))

isTRUE <- function(x) identical(TRUE, x)

# get.R

get <-
    function (x, pos = -1L, envir = as.environment(pos), mode = "any",
              inherits = TRUE)
    .Internal(get(x, envir, mode, inherits))

# is.R
is.vector <- function(x, mode="any") .Internal(is.vector(x,mode))

# stats/R/distn.R
runif <- function(n, min=0, max=1) .Call(C_runif, n, min, max)

rhyper <- function(nn, m, n, k) .Call(C_rhyper, nn, m, n, k)
