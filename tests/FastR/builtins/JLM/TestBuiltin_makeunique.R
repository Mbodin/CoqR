argv <- list(c('A', 'B', 'C', 'D', 'E', 'F'), '.'); .Internal(make.unique(argv[[1]], argv[[2]]))
argv <- list(c('b', 'NA', 'NA'), '.'); .Internal(make.unique(argv[[1]], argv[[2]]))
argv <- list(c('1', '2', '3', '6', '7', '7', '7', '8', '8', '10', '11', '12', '12', '12', '15', '15', '16', '17', '19', '20', '21', '21', '23'), '.'); .Internal(make.unique(argv[[1]], argv[[2]]))
argv <- list(character(0), '.'); .Internal(make.unique(argv[[1]], argv[[2]]))
{ make.unique(rep('a', 10)) }
{ make.unique(paste0('a', 1:10)) }
{ make.unique(paste0('a', 1:10)) }
{ make.unique(paste('a', 1:10, sep = '.')) }
{ make.unique(c('a', 'a', 'a.2', 'a'), sep = '.') }
{ make.unique(c('a.1', 'a.2', 'a', 'a'), sep = '.') }
{ make.unique(c('a.2', 'a.2', 'a', 'a', 'a'), sep = '.') }
{ make.unique(c('a.2', 'a.2', 'a.3', 'a.3', 'a', 'a', 'a'), sep = '.') }
{ make.unique("a") }
{ make.unique(character()) }
{ make.unique(c("a", "a")) }
{ make.unique(c("a", "a", "a")) }
{ make.unique(c("a", "a"), "_") }
{ make.unique(1) }
{ make.unique("a", 1) }
{ make.unique("a", character()) }
{ .Internal(make.unique(c(7, 42), ".")) }
{ .Internal(make.unique(NULL, ".")) }
{ .Internal(make.unique(c("7", "42"), 42)) }
{ .Internal(make.unique(c("7", "42"), character())) }
{ .Internal(make.unique(c("7", "42"), c(".", "."))) }
{ .Internal(make.unique(c("7", "42"), NULL)) }
