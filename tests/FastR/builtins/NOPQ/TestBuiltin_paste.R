argv <- list(list('%%  ~~objects to See Also as', 'code{link{~~fun~~}}, ~~~'), ' ', NULL); .Internal(paste(argv[[1]], argv[[2]], argv[[3]]))
argv <- list(list(c('[', 'cox.zph', NA)), ' ', 'r'); .Internal(paste(argv[[1]], argv[[2]], argv[[3]]))
argv <- list(list(), ' ', NULL); .Internal(paste(argv[[1]], argv[[2]], argv[[3]]))
argv <- list(list('package', structure('pkgA', .Names = 'name')), ':', NULL); .Internal(paste(argv[[1]], argv[[2]], argv[[3]]))
argv <- list(list(c('[', 'as.data.frame', 'plot', 'print', 'summary', 'as.character', 'print', 'print', 'plot', 'update', 'dim', 'dimnames', 'dimnames<-', '[', 't', 'summary', 'print', 'barchart', 'barchart', 'barchart', 'barchart', 'barchart', 'barchart', 'bwplot', 'bwplot', 'densityplot', 'densityplot', 'dotplot', 'dotplot', 'dotplot', 'dotplot', 'dotplot', 'dotplot', 'histogram', 'histogram', 'histogram', 'qqmath', 'qqmath', 'stripplot', 'stripplot', 'qq', 'xyplot', 'xyplot', 'levelplot', 'levelplot', 'levelplot', 'levelplot', 'contourplot', 'contourplot', 'contourplot', 'contourplot', 'cloud', 'cloud', 'cloud', 'wireframe', 'wireframe', 'splom', 'splom', 'splom', 'parallelplot', 'parallelplot', 'parallelplot', 'parallel', 'parallel', 'parallel', 'tmd', 'tmd', 'llines', 'ltext', 'lpoints'), c('shingle', 'shingle', 'shingle', 'shingle', 'shingle', 'shingleLevel', 'shingleLevel', 'trellis', 'trellis', 'trellis', 'trellis', 'trellis', 'trellis', 'trellis', 'trellis', 'trellis', 'summary.trellis', 'formula', 'array', 'default', 'matrix', 'numeric', 'table', 'formula', 'numeric', 'formula', 'numeric', 'formula', 'array', 'default', 'matrix', 'numeric', 'table', 'formula', 'factor', 'numeric', 'formula', 'numeric', 'formula', 'numeric', 'formula', 'formula', 'ts', 'formula', 'table', 'array', 'matrix', 'formula', 'table', 'array', 'matrix', 'formula', 'matrix', 'table', 'formula', 'matrix', 'formula', 'matrix', 'data.frame', 'formula', 'matrix', 'data.frame', 'formula', 'matrix', 'data.frame', 'formula', 'trellis', 'default', 'default', 'default')), '.', NULL); .Internal(paste(argv[[1]], argv[[2]], argv[[3]]))
argv <- list(list(c('dotplot', 'table', NA)), ' ', 'r'); .Internal(paste(argv[[1]], argv[[2]], argv[[3]]))
argv <- list(list(character(0)), ' ', ' '); .Internal(paste(argv[[1]], argv[[2]], argv[[3]]))
argv <- list(list('detaching', '‘package:splines’'), ' ', NULL); .Internal(paste(argv[[1]], argv[[2]], argv[[3]]))
argv <- list(list('GRID', 'text', '6'), '.', NULL); .Internal(paste(argv[[1]], argv[[2]], argv[[3]]))
argv <- list(list('(', structure(c(' 1.124', ' 1.056', ' 1.059', ' 0.932'), .Dim = c(2L, 2L)), ','), '', NULL); .Internal(paste(argv[[1]], argv[[2]], argv[[3]]))
argv <- list(list(character(0)), ' ', ''); .Internal(paste(argv[[1]], argv[[2]], argv[[3]]))
{ paste() }
{ a <- as.raw(200) ; b <- as.raw(255) ; paste(a, b) }
{ paste(character(0),31415) }
{ paste(1:2, 1:3, FALSE, collapse=NULL) }
{ paste(sep="") }
{ paste(1:2, 1:3, FALSE, collapse="-", sep="+") }
{ paste(NULL, list(), sep = "=") }
{ paste(NA) }
{ paste(c(1,NA)) }
{ s<-c('1',NA); paste(s); s; }
{ paste(1:3, sep='.') }
{ paste('a', 1:3, sep='.') }
{ paste(1:3, 'b', sep='.') }
{ paste('a', 1:3, 'b', sep='.') }
{ paste('a', 'a', 1:3, 'b', 'b', sep='.') }
{ as.character.myc <- function(x) '42'; val <- 'hello'; class(val) <- 'myc'; paste(val, 'world') }
{ as.character.myc <- function(x) 42; val <- 3.14; class(val) <- 'myc'; paste(val, 'world') }
{ as.character.myc <- function(x) NULL; val <- 3.14; class(val) <- 'myc'; paste(val, 'world') }
{ as.character.myc <- function(x) '42'; val <- 3.14; class(val) <- 'myc'; paste(val, 'world') }
{ assign('as.character.myc', function(x) '42', envir=.__S3MethodsTable__.); val <- 3.14; class(val) <- 'myc'; res <- paste(val, 'world'); rm('as.character.myc', envir=.__S3MethodsTable__.); res }
