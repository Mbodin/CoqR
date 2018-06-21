argv <- list(-1, 1:31); .Internal(bitwiseShiftL(argv[[1]], argv[[2]]))
{ .Internal(bitwiseShiftL(, 1))}
{ .Internal(bitwiseShiftL(200, ))}
{ bitwShiftL(c(10,11,12,13,14,15), c(1,1,1,1,1,1)) }
{ bitwShiftL(c(100,200,300), 1) }
{ bitwShiftL(c(25,57,66), c(10,20,30,40,50,60)) }
{ bitwShiftL(c(8,4,2), NULL) }
{ bitwShiftL(TRUE, c(TRUE, FALSE)) }
{ bitwShiftL(c(3+3i), c(3,2,4)) }
{ bitwShiftL(c(3,2,4), c(3+3i)) }
{ bitwShiftL(c(1,2,3,4), c("a")) }
