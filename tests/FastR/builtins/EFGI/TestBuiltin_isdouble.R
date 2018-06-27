argv <- list(list(1, list(3, 'A')));is.double(argv[[1]]);
argv <- list(structure(1:7, .Names = c('a1', 'a2', 'a3', 'a4', 'a5', 'a6', 'a7')));is.double(argv[[1]]);
argv <- list(structure(3.14159265358979, class = structure('3.14159265358979', class = 'testit')));is.double(argv[[1]]);
argv <- list(structure(list(`character(0)` = structure(integer(0), .Label = character(0), class = 'factor')), .Names = 'character(0)', row.names = character(0), class = 'data.frame'));is.double(argv[[1]]);
argv <- list(structure(1:24, .Dim = 2:4));is.double(argv[[1]]);
argv <- list(structure(c(1, 5, 9, 13, 17, 21, 2, 6, 10, 14, 18,     22, 3, 7, 11, 15, 19, 23, 4, 8, 12, 16, 20, 24), .Dim = c(6L,     4L)));do.call('is.double', argv)
