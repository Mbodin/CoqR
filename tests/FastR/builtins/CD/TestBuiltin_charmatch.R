argv <- list(c('x', 'y', 'z'), c('row.names', 'x', 'y', 'z'), 0L); .Internal(charmatch(argv[[1]], argv[[2]], argv[[3]]))
argv <- list(character(0), c('row.names', 'height', 'weight'), 0L); .Internal(charmatch(argv[[1]], argv[[2]], argv[[3]]))
argv <- list('package:methods', c('.GlobalEnv', 'CheckExEnv', 'package:stats', 'package:graphics', 'package:grDevices', 'package:utils', 'package:datasets', 'package:methods', 'Autoloads', 'package:base'), NA_integer_); .Internal(charmatch(argv[[1]], argv[[2]], argv[[3]]))
argv <- list('package:methods', c('.GlobalEnv', 'package:graphics', 'package:stats', 'Autoloads', 'package:base'), NA_integer_); .Internal(charmatch(argv[[1]], argv[[2]], argv[[3]]))
argv <- list(c('0', '1'), c('0', '1'), 0); .Internal(charmatch(argv[[1]], argv[[2]], argv[[3]]))
argv <- list(c('m', 'f'), c('male', 'female'), NA_integer_); .Internal(charmatch(argv[[1]], argv[[2]], argv[[3]]))
argv <- list('me', c('mean', 'median', 'mode'), NA_integer_); .Internal(charmatch(argv[[1]], argv[[2]], argv[[3]]))
argv <- list(character(0), c('semiTransparency', 'transparentBackground', 'rasterImage', 'capture', 'locator', 'events'), 0L); .Internal(charmatch(argv[[1]], argv[[2]], argv[[3]]))
{charmatch("abc", "deeee",c("3","4"))}
{charmatch("abc", "deeee")}
{charmatch("abc", "deeeec",c("3","4"))}
{charmatch("", "")}
{charmatch("m",   c("mean", "median", "mode"))}
{charmatch("med", c("mean", "median", "mode"))}
{charmatch(matrix(c(9,3,1,6),2,2,byrow=T), "hello")}
{charmatch(matrix(c('h',3,'e',6),2,2,byrow=T), "hello")}
{charmatch(c("ole","ab"),c("ole","ab"))}
{charmatch(c("ole","ab"),c("ole","ole"))}
{charmatch(matrix(c('h','l','e',6),2,2,byrow=T), "hello")}
{charmatch('hello', c(''))}
{charmatch(c('', 'hello', '[', 'foo', '{', '(', ''), c('[', '(', '{', ''), nomatch = NA)}
