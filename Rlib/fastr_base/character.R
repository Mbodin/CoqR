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


substr <- function(x, start, stop)
{
    if(!is.character(x)) x <- as.character(x)
    .Internal(substr(x, as.integer(start), as.integer(stop)))
}

substring <- function(text, first, last=1000000L)
{
    if(!is.character(text)) text <- as.character(text)
    n <- max(lt <- length(text), length(first), length(last))
    if(lt && lt < n) text <- rep_len(text, length.out = n)
    .Internal(substr(text, as.integer(first), as.integer(last)))
}

`substr<-` <- function(x, start, stop, value)
    .Internal(`substr<-`(x, as.integer(start), as.integer(stop), value))

`substring<-` <- function(text, first, last=1000000L, value)
    .Internal(`substr<-`(text, as.integer(first), as.integer(last), value))


tolower <- function(x)
{
    if(!is.character(x)) x <- as.character(x)
    .Internal(tolower(x))
}
toupper <- function(x)
{
    if(!is.character(x)) x <- as.character(x)
    .Internal(toupper(x))
}
