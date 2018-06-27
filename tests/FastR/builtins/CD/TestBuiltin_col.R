argv <- list(c(2L, 2L)); .Internal(col(argv[[1]]))
argv <- list(c(1L, 0L)); .Internal(col(argv[[1]]))
{ ma <- matrix(1:12, 3, 4) ; col(ma) }
{ ma <- cbind(x = 1:10, y = (-4:5)^2) ; col(ma) }
{ col(c(1,2,3)) }
col(NULL)
