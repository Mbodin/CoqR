
as.integer.myclass <- function(x, extra, ...) list(x=x, extra=extra, varargs=list(...)); as.integer(structure(TRUE, class='myclass'), my=TRUE, extra=42L, args='hello');
as.numeric(diff(structure(c(-154401120, 1503191520), class = c('POSIXct', 'POSIXt'), tzone = 'GMT')), units='secs')
