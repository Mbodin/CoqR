argv <- list(3L, 'C'); Sys.setlocale(argv[[1]], argv[[2]])
argv <- structure(list(category = 'LC_TIME', locale = 'C'), .Names = c('category',     'locale'));do.call('Sys.setlocale', argv)
{ Sys.setenv(LC_CTYPE="en_US.UTF-8"); Sys.getlocale("LC_CTYPE"); }
Sys.setlocale(4, c('more', 'elements'))
Sys.setlocale(4, 42)
Sys.setlocale('3L', 'C')
