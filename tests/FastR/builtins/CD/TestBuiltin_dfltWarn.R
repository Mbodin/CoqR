argv <- list('f is deprecated.nUse convertY instead.nSee help(Deprecated)', NULL); .Internal(.dfltWarn(argv[[1]], argv[[2]]))
argv <- list('bessel_y(2,nu=288.12): precision lost in result', quote(besselY(2, nu = nu <- seq(3, 300, len = 51)))); .Internal(.dfltWarn(argv[[1]], argv[[2]]))
argv <- list('glm.fit: algorithm stopped at boundary value', NULL); .Internal(.dfltWarn(argv[[1]], argv[[2]]))
argv <- list('header and col.names are of different lengths', quote(read.table('foo3', header = TRUE, col.names = letters[1:4]))); .Internal(.dfltWarn(argv[[1]], argv[[2]]))
argv <- list('‘graphics’ namespace cannot be unloaded:n  namespace ‘graphics’ is imported by ‘stats’ so cannot be unloaded', NULL); .Internal(.dfltWarn(argv[[1]], argv[[2]]))
argv <- list('NaNs produced', quote(log(ifelse(y == 0, 1, y/mu)))); .Internal(.dfltWarn(argv[[1]], argv[[2]]))
argv <- list('drop argument will be ignored', quote(`[.data.frame`(women, 'height', drop = FALSE))); .Internal(.dfltWarn(argv[[1]], argv[[2]]))
argv <- list('prediction from a rank-deficient fit may be misleading', quote(predict.lm(object, newdata, se.fit, scale = residual.scale, type = ifelse(type == 'link', 'response', type), terms = terms, na.action = na.action))); .Internal(.dfltWarn(argv[[1]], argv[[2]]))
argv <- list('1 y value <= 0 omitted from logarithmic plot', quote(xy.coords(x, NULL, log = log))); .Internal(.dfltWarn(argv[[1]], argv[[2]]))
argv <- list('x is neither a vector nor a matrix: using as.numeric(x)', quote(dotchart(table(infert$education)))); .Internal(.dfltWarn(argv[[1]], argv[[2]]))
argv <- list('Invalid file name(s) for R code in ./myTst/R:n  file55711ba85492n are now renamed to z<name>.R', quote(package.skeleton('myTst', code_files = tmp))); .Internal(.dfltWarn(argv[[1]], argv[[2]]))
argv <- list('incomplete final line found by readTableHeader on foo4', quote(read.table('foo4', header = TRUE))); .Internal(.dfltWarn(argv[[1]], argv[[2]]))
