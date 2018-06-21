argv <- list(structure(c(FALSE, TRUE, TRUE, FALSE), .Dim = c(2L, 2L), .Dimnames = list(c('A', 'B'), c('A', 'B'))), TRUE); .Internal(det_ge_real(argv[[1]], argv[[2]]))
argv <- list(structure(c(TRUE, TRUE, TRUE, TRUE), .Dim = c(2L, 2L), .Dimnames = list(c('A', 'B'), c('A', 'B'))), TRUE); .Internal(det_ge_real(argv[[1]], argv[[2]]))
argv <- list(structure(c(2, 1, 1, 2), .Dim = c(2L, 2L), .Dimnames = list(c('A', 'B'), c('A', 'B'))), TRUE); .Internal(det_ge_real(argv[[1]], argv[[2]]))
argv <- structure(list(x = structure(c(0, 0, 0, 0, 0, 0, NA,     0, 0, NA, NA, 0, 0, 0, 0, 1), .Dim = c(4L, 4L))), .Names = 'x');do.call('det', argv)
{ det(matrix(c(1,2,4,5),nrow=2)) }
{ det(matrix(c(1,-3,4,-5),nrow=2)) }
{ det(matrix(c(1,0,4,NA),nrow=2)) }
