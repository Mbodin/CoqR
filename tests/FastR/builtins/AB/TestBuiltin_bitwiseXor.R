argv <- list(-1L, 1L); .Internal(bitwiseXor(argv[[1]], argv[[2]]))
{ bitwXor(c(10,11,12,13,14,15), c(1,1,1,1,1,1)) }
{ bitwXor(c(25,57,66), c(10,20,30,40,50,60)) }
{ bitwXor(20,30) }
{ bitwXor(c("r"), c(16,17)) }
