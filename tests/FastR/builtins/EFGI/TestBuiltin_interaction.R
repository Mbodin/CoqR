argv <- list(c('a.b', 'a'), c('c', 'b.c'));do.call('interaction', argv)
{ a <- gl(2, 4, 8) ; b <- gl(2, 2, 8, labels = c("ctrl", "treat")) ; interaction(a, b) }
{ a <- gl(2, 4, 8) ; b <- gl(2, 2, 8, labels = c("ctrl", "treat")) ; s <- gl(2, 1, 8, labels = c("M", "F")) ; interaction(a, b, s, sep = ":") }
