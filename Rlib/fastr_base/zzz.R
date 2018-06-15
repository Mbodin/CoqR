#  File src/library/base/R/apply.R
#  Part of the R package, https://www.R-project.org
#
#  Copyright (C) 1995-2012 The R Core Team
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


.ArgsEnv <- new.env(hash = TRUE, parent = emptyenv())

assign("attr", function(x, which, exact = FALSE) NULL, envir = .ArgsEnv)
assign("attr<-", function(x, which, value) NULL, envir = .ArgsEnv)
assign("attributes", function(obj) NULL, envir = .ArgsEnv)
assign("attributes<-", function(obj, value) NULL, envir = .ArgsEnv)

assign("class", function(x) NULL, envir = .ArgsEnv)
assign("class<-", function(x, value) NULL, envir = .ArgsEnv)
assign("forceAndCall", function(n, FUN, ...) NULL, envir = .ArgsEnv)

assign("is.atomic", function(x) NULL, envir = .ArgsEnv)
assign("is.character", function(x) NULL, envir = .ArgsEnv)
assign("is.complex", function(x) NULL, envir = .ArgsEnv)
assign("is.double", function(x) NULL, envir = .ArgsEnv)
assign("is.integer", function(x) NULL, envir = .ArgsEnv)
assign("is.list", function(x) NULL, envir = .ArgsEnv)
assign("is.logical", function(x) NULL, envir = .ArgsEnv)
assign("is.null", function(x) NULL, envir = .ArgsEnv)
assign("is.object", function(x) NULL, envir = .ArgsEnv)
assign("is.raw", function(x) NULL, envir = .ArgsEnv)
assign("is.recursive", function(x) NULL, envir = .ArgsEnv)
assign("is.call", function(x) NULL, envir = .ArgsEnv)
assign("is.expression", function(x) NULL, envir = .ArgsEnv)

assign("list", function(...) NULL, envir = .ArgsEnv)

assign("missing", function(x) NULL, envir = .ArgsEnv)
assign("nargs", function() NULL, envir = .ArgsEnv)
assign("nzchar", function(x, keepNA=FALSE) NULL, envir = .ArgsEnv)

assign("seq_len", function(length.out) NULL, envir = .ArgsEnv)

.S3PrimitiveGenerics <-
  c("anyNA", "as.character", "as.complex", "as.double", "as.environment",
    "as.integer", "as.logical", "as.numeric", "as.raw",
    "c", "dim", "dim<-", "dimnames", "dimnames<-",
    "is.array", "is.finite",
    "is.infinite", "is.matrix", "is.na", "is.nan", "is.numeric",
    "length", "length<-", "levels<-", "names", "names<-", "rep",
    "seq.int", "xtfrm")

.GenericArgsEnv <- local({
    env <- new.env(hash = TRUE, parent = emptyenv())
    ## those with different arglists are overridden below
    for(f in .S3PrimitiveGenerics) {
        fx <- function(x) {NULL}
        body(fx) <- substitute(UseMethod(ff), list(ff=f))
        environment(fx) <- .BaseNamespaceEnv
        assign(f, fx, envir = env)
    }
    ## now add the group generics
    ## round, signif, log, trunc are handled below
    fx <- function(x) {NULL}
    for(f in c("abs", "sign", "sqrt", "floor", "ceiling",
               "exp", "expm1", "log1p", "log10", "log2",
               "cos", "sin", "tan", "acos", "asin", "atan", "cosh", "sinh",
               "tanh", "acosh", "asinh", "atanh",
	       "cospi", "sinpi", "tanpi",
               "gamma", "lgamma", "digamma", "trigamma",
               "cumsum", "cumprod", "cummax", "cummin")) {
        body(fx) <- substitute(UseMethod(ff), list(ff=f))
        environment(fx) <- .BaseNamespaceEnv
        assign(f, fx, envir = env)
    }

    ## ! is unary and handled below
    fx <- function(e1, e2) {NULL}
    for(f in c("+", "-", "*", "/", "^", "%%", "%/%", "&", "|",
               "==", "!=", "<", "<=", ">=", ">")) {
        body(fx) <- substitute(UseMethod(ff), list(ff=f))
        environment(fx) <- .BaseNamespaceEnv
        assign(f, fx, envir = env)
    }

    for(f in c("all", "any", "sum", "prod", "max", "min", "range")) {
        fx <- function(..., na.rm = FALSE) {NULL}
        body(fx) <- substitute(UseMethod(ff), list(ff=f))
        environment(fx) <- .BaseNamespaceEnv
        assign(f, fx, envir = env)
    }

    for(f in c("Arg", "Conj", "Im", "Mod", "Re")) {
        fx <- function(z) {NULL}
        body(fx) <- substitute(UseMethod(ff), list(ff=f))
        environment(fx) <- .BaseNamespaceEnv
        assign(f, fx, envir = env)
    }
    fx <- function(x, recursive = FALSE) UseMethod("anyNA")
    environment(fx) <- .BaseNamespaceEnv
    assign("anyNA", fx, envir = env)
    env
})

assign("as.character", function(x, ...) UseMethod("as.character"),
       envir = .GenericArgsEnv)
assign("as.complex", function(x, ...) UseMethod("as.complex"),
       envir = .GenericArgsEnv)
assign("as.double", function(x, ...) UseMethod("as.double"),
       envir = .GenericArgsEnv)
assign("as.integer", function(x, ...) UseMethod("as.integer"),
       envir = .GenericArgsEnv)
assign("as.logical", function(x, ...) UseMethod("as.logical"),
       envir = .GenericArgsEnv)

assign("dim<-", function(x, value) UseMethod("dim<-"), envir = .GenericArgsEnv)
assign("dimnames<-", function(x, value) UseMethod("dimnames<-"),
      envir = .GenericArgsEnv)
assign("length<-", function(x, value) UseMethod("length<-"),
      envir = .GenericArgsEnv)
assign("log", function(x, base=exp(1)) UseMethod("log"),
       envir = .GenericArgsEnv)
assign("rep", function(x, ...) UseMethod("rep"), envir = .GenericArgsEnv)
