argv <- structure(list(x = '`', value = TRUE), .Names = c('x',     'value'));do.call('assign', argv)
x <- c(1,2,4); e <- new.env(); assign('foo', x, e); x[[1]] <- 5; x; get('foo', e)
x <- c(1,2,4); e <- new.env(); assign('foo', x, e, inherits=0); x[[1]] <- 5; x; get('foo', e)
