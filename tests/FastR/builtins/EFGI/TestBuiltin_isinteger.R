argv <- list(2.74035772634541);is.integer(argv[[1]]);
argv <- list(c(NA, 9, 3, 3));is.integer(argv[[1]]);
argv <- list(c(NA, 0L));is.integer(argv[[1]]);
argv <- list(c(NA, -4.19095158576965e-09));is.integer(argv[[1]]);
argv <- list(structure(list(`character(0)` = structure(integer(0), .Label = character(0), class = 'factor')), .Names = 'character(0)', row.names = character(0), class = 'data.frame'));is.integer(argv[[1]]);
argv <- list(c(-0.6, -0.6, -0.6, -0.6, -0.6, -0.6, -0.6, -0.6, -0.3, -0.3, -0.3, -0.3, -0.3, -0.3, -0.3, -0.3, 0.3, 0.3, 0.3, 0.3, 0.3, 0.3, 0.3, 0.3, 0.6, 0.6, 0.6, 0.6, 0.6, 0.6, 0.6, 0.6));is.integer(argv[[1]]);
argv <- list(c(NA, 1L));is.integer(argv[[1]]);
argv <- list(structure(3.14159265358979, class = structure('3.14159265358979', class = 'testit')));is.integer(argv[[1]]);
argv <- list(structure(c(1, 1, 1, 1, 1, 1), .Dim = 1:3));is.integer(argv[[1]]);
argv <- list(c(1L, 0L, NA, 1L));do.call('is.integer', argv)
{ is.integer(seq(1,2)) }
{ is.integer(seq(1L,2L)) }
{ is.integer(as.factor(c(1,2,3))) }
