#  File src/library/base/R/apply.R
#  Part of the R package, https://www.R-project.org
#
#  Copyright (C) 1995-2013, 2015 The R Core Team
#
#  This program is free software; you can redistribute it and/or modify
#  it under the terms of the GNU General Public License as published by
#  the Free Software Foundation; either version 2 of the License, or
#  (at your option) any later version.
#
#  This program is distributed in the hope that it will be useful,
#  but WITHOUT ANY WARRANTY; without even the implied warranty of
#  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
#  GNU General Public License for more details.
#
#  A copy of the GNU General Public License is available at
#  https://www.R-project.org/Licenses/

match <- function(x, table, nomatch = NA_integer_, incomparables = NULL)
    .Internal(match(x, table, nomatch, incomparables))

`%in%`  <- function(x, table) match(x, table, nomatch = 0L) > 0L

match.arg <- function (arg, choices, several.ok = FALSE)
{
    if (missing(choices)) {
	formal.args <- formals(sys.function(sys.parent()))
	choices <- eval(formal.args[[as.character(substitute(arg))]])
    }
    if (is.null(arg)) return(choices[1L])
    else if(!is.character(arg))
	stop("'arg' must be NULL or a character vector")
    if (!several.ok) { # most important (default) case:
        ## the arg can be the whole of choices as a default argument.
        if(identical(arg, choices)) return(arg[1L])
        if(length(arg) > 1L) stop("'arg' must be of length 1")
    } else if(length(arg) == 0L) stop("'arg' must be of length >= 1")

    ## handle each element of arg separately
    i <- pmatch(arg, choices, nomatch = 0L, duplicates.ok = TRUE)
    if (all(i == 0L))
	stop(gettextf("'arg' should be one of %s",
                      paste(dQuote(choices), collapse = ", ")),
             domain = NA)
    i <- i[i > 0L]
    if (!several.ok && length(i) > 1)
        stop("there is more than one match in 'match.arg'")
    choices[i]
}
