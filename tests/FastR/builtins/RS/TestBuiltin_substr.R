argv <- list('weight', 1L, 2L); .Internal(substr(argv[[1]], argv[[2]], argv[[3]]))
argv <- list(c('        ', '        '), 1L, c(4L, -16L)); .Internal(substr(argv[[1]], argv[[2]], argv[[3]]))
argv <- list(structure(c('as.formula', 'coef', 'makepredictcall', 'na.fail', 'predict'), .Names = c('as.formula', 'coef', 'makepredictcall', 'na.fail', 'predict')), 1L, 6L); .Internal(substr(argv[[1]], argv[[2]], argv[[3]]))
argv <- list(character(0), 7L, 1000000L); .Internal(substr(argv[[1]], argv[[2]], argv[[3]]))
argv <- list(structure('to be supported).', Rd_tag = 'TEXT'), 17L, 17L); .Internal(substr(argv[[1]], argv[[2]], argv[[3]]))
argv <- list(character(0), 1L, 5L); .Internal(substr(argv[[1]], argv[[2]], argv[[3]]))
argv <- list('', 1L, 2L); .Internal(substr(argv[[1]], argv[[2]], argv[[3]]))
argv <- list(structure(c('model.frame', 'predict', 'residuals'), .Names = c('model.frame', 'predict', 'residuals')), 1L, 6L); .Internal(substr(argv[[1]], argv[[2]], argv[[3]]))
{ substr("123456", 2L, 4L) }
{ substr("123456", 2, 4) }
{ substr("123456", 4, 2) }
{ substr("123456", 7, 8) }
{ substr("123456", 4, 8) }
{ substr("123456", -1, 3) }
{ substr("123456", -5, -1) }
{ substr("123456", -20, -100) }
{ substr("123456", 2.8, 4) }
{ substr(c("hello", "bye"), 1, 2) }
{ substr(c("hello", "bye"), c(1,2,3), 4) }
{ substr(c("hello", "bye"), 1, c(1,2,3)) }
{ substr(c("hello", "bye"), c(1,2), c(2,3)) }
{ substr(1234L,2,3) }
{ substr(1234,2,3) }
{ substr("abcdef",c(1,2),c(3L,5L)) }
{ substr(c("abcdef", "aa"), integer(), 2) }
{ substr(c("abcdef", "aa"), 2, integer()) }
{ substr(character(), integer(), integer()) }
{ substr(c("abcdef", "aa"), NA, 4) }
{ substr(c("abcdef", "aa"), 3, NA) }
{ substr(c("abcdef", "aa"), c(NA,8), 4) }
{ substr(c("abcdef", "aa"), c(1,NA), 4) }
{ substr(NA,1,2) }
{ substr("fastr", NA, 2) }
{ substr("fastr", 1, NA) }
{ x<-"abcdef"; substr(x,1,4)<-"0000"; x }
{ x<-"abcdef"; substr(x,1,3)<-"0000"; x }
{ x<-"abcdef"; substr(x,1,3)<-"0"; x }
{ x<-"abcdef"; substr(x,NA,3)<-"0"; x }
{ x<-"abcdef"; substr(x,1,NA)<-"0"; x }
{ x<-character(); substr(x,1,3)<-"0"; x }
{ x<-c("abcdef", "ghijklm"); substr(x, c(1,NA), 4)<-"0"; x }
{ x<-"abcdef"; substr(x,3,1)<-0; x }
{ x<-"abcdef"; substr(x,1,3)<-character(); x }
{ x<-"abcdef"; substr(x,1,3)<-NULL; x }
{ x<-"abcdef"; substr(x,integer(),3)<-NULL; x }
{ x<-character(); substr(x,1,3)<-0; x }
{ x<-character(); substr(x,1,3)<-NULL; x }
{ x<-character(); substr(x,integer(),3)<-NULL; x }
{ x<-c("abcdef"); substr(x[1], 2, 3)<-"0"; x }
