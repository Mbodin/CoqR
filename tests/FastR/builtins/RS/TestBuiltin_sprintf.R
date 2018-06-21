argv <- list('%s is not TRUE', 'identical(fxy, c(1, 2, 3))'); .Internal(sprintf(argv[[1]], argv[[2]]))
argv <- list('%1.0f', 3.14159265358979); .Internal(sprintf(argv[[1]], argv[[2]]))
argv <- list('min 3-char string '%3s'', c('a', 'ABC', 'and an even longer one')); .Internal(sprintf(argv[[1]], argv[[2]]))
argv <- list('min 10-char string '%10s'', c('a', 'ABC', 'and an even longer one')); .Internal(sprintf(argv[[1]], argv[[2]]))
argv <- list('%o', integer(0)); .Internal(sprintf(argv[[1]], argv[[2]]))
argv <- list('%*s', 1, ''); .Internal(sprintf(argv[[1]], argv[[2]], argv[[3]]))
argv <- list('p,L,S = (%2d,%2d,%2d): ', TRUE, TRUE, FALSE); .Internal(sprintf(argv[[1]], argv[[2]], argv[[3]], argv[[4]]))
argv <- list('p,L,S = (%2d,%2d,%2d): ', TRUE, FALSE, NA); .Internal(sprintf(argv[[1]], argv[[2]], argv[[3]], argv[[4]]))
argv <- list('plot_%02g', 1L); .Internal(sprintf(argv[[1]], argv[[2]]))
argv <- list('tools:::.createExdotR('%s', '%s', silent = TRUE, use_gct = %s, addTiming = %s)', structure('KernSmooth', .Names = 'Package'), '/home/lzhao/hg/r-instrumented/library/KernSmooth', FALSE, FALSE); .Internal(sprintf(argv[[1]], argv[[2]], argv[[3]], argv[[4]], argv[[5]]))
argv <- list('%.0f%% said yes (out of a sample of size %.0f)', 66.666, 3); .Internal(sprintf(argv[[1]], argv[[2]], argv[[3]]))
argv <- list('%1$d %1$x %1$X', 0:15); .Internal(sprintf(argv[[1]], argv[[2]]))
argv <- list('%03o', 1:255); .Internal(sprintf(argv[[1]], argv[[2]]))
argv <- list('%d y value <= 0 omitted from logarithmic plot', 1L); .Internal(sprintf(argv[[1]], argv[[2]]))
argv <- list('%o', 1:255); .Internal(sprintf(argv[[1]], argv[[2]]))
argv <- list('%s-class.Rd', structure('foo', .Names = 'foo')); .Internal(sprintf(argv[[1]], argv[[2]]))
argv <- list('checkRd: (%d) %s', -3, 'evalSource.Rd:157: Unnecessary braces at ‘{'sourceEnvironment'}’'); .Internal(sprintf(argv[[1]], argv[[2]], argv[[3]]))
argv <- list('tools:::check_compiled_code('%s')', '/home/lzhao/hg/r-instrumented/library/foreign'); .Internal(sprintf(argv[[1]], argv[[2]]))
argv <- list('%5g', structure(c(18, 18, 0, 14, 4, 12, 12, 0, 4, 8, 26, 23, 3, 18, 5, 8, 5, 3, 0, 5, 21, 0, 21, 0, 0), .Dim = c(5L, 5L), .Dimnames = list(NULL, c('', '', '', '', '')))); .Internal(sprintf(argv[[1]], argv[[2]]))
argv <- list('%G', 3.14159265358979e-06); .Internal(sprintf(argv[[1]], argv[[2]]))
argv <- structure(list(fmt = '%9.4g', 12345.6789), .Names = c('fmt',     ''));do.call('sprintf', argv)
{ sprintf("0x%x",1L) }
{ sprintf("0x%x",10L) }
{ sprintf("%d%d",1L,2L) }
{ sprintf("0x%x",1) }
{ sprintf("0x%x",10) }
{ sprintf("%d", 10) }
{ sprintf("%7.3f", 10.1) }
{ sprintf("%03d", 1:3) }
{ sprintf("%3d", 1:3) }
{ sprintf("%4X", 26) }
{ sprintf("%04X", 26) }
{ sprintf("Hello %*d", 3, 2) }
{ sprintf("Hello %*2$d", 3, 2) }
{ sprintf("Hello %2$*2$d", 3, 2) }
{ sprintf("%d", as.integer(c(7))) }
{ sprintf("%d", as.integer(c(7,42)), as.integer(c(1,2))) }
{ sprintf("%d %d", as.integer(c(7,42)), as.integer(c(1,2))) }
{ sprintf("%d %d", as.integer(c(7,42)), as.integer(1)) }
{ sprintf("%d %d", as.integer(c(7,42)), integer()) }
{ sprintf("foo") }
{ sprintf(c("foo", "bar")) }
{ sprintf(c("foo %f", "bar %f"), 7) }
{ sprintf(c("foo %f %d", "bar %f %d"), 7, 42L) }
{ sprintf(c("foo %f %d", "bar %f %d"), c(7,1), c(42L, 2L)) }
{ sprintf("%.3g", 1.234) }
{ sprintf('plot_%02g', 3L) }
{ sprintf(c('hello', 'world'), NULL) }
{ sprintf('%s', list('hello world')) }
{ sprintf('%.3d', 4.0) }
{ sprintf('%.3i', 4.0) }
{ asdfgerta <- sprintf('%0.f', 1); }
{ asdfgerta <- sprintf('%0.0f', 1); }
{ asdfgerta <- sprintf('%.0f', 1); }
{ as.character.myclass65231 <- function(x) '42'; y <- 2; class(y) <- 'myclass65231'; sprintf('%s', y); }
{ as.double.myclass65321 <- function(x) 3.14; y <- 3L; class(y) <- 'myclass65321'; sprintf('%g', y); }
{ as.double.myclass65321 <- function(x) 3.14; y <- 'str'; class(y) <- 'myclass65321'; sprintf('%g', y); }
{ sprintf(c('hello %d %s', 'world %d %s'), list(2, 'x')) }
{ sprintf('limited to %d part%s due to %.0f', 3L, 3.3) }
{ sprintf('limited to %d part%s due to %.0f', 3L, 'a', 3L) }
{ sprintf('%s', %0) }", new String[]{"1L", "2", "2.2", "TRUE
{ sprintf('%d', %0) }", new String[]{"1L", "2", "2.2", "TRUE
{ sprintf('%f', %0) }", new String[]{"1L", "2", "2.2", "TRUE
sprintf('%02d', as.integer(NA))
{ sprintf('%s', as.raw(1)) }
