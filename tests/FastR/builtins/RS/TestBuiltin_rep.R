argv <- list(NA, 7); .Internal(rep_len(argv[[1]], argv[[2]]))
argv <- list(NA, 4L); .Internal(rep_len(argv[[1]], argv[[2]]))
argv <- list(-Inf, 1L); .Internal(rep_len(argv[[1]], argv[[2]]))
argv <- list(list(), 0L); .Internal(rep_len(argv[[1]], argv[[2]]))
argv <- list(FALSE, FALSE); .Internal(rep_len(argv[[1]], argv[[2]]))
argv <- list(c(4.60173175921079, 4.46741031725783, 4.30749719409961, 4.12438637683712, 4.51499342053481, 4.24874137138388, 3.92699081698724, 3.6052402625906, 3.92699081698724), 9L); .Internal(rep_len(argv[[1]], argv[[2]]))
argv <- list(c(3L, 6L), 2L); .Internal(rep_len(argv[[1]], argv[[2]]))
argv <- list(list(c('                  ', '                ')), 1L); .Internal(rep_len(argv[[1]], argv[[2]]))
argv <- list(structure(1:4, .Label = c('A', 'B', 'C', 'D'), class = 'factor', .Names = c('a', 'b', 'c', 'd')), 10); .Internal(rep_len(argv[[1]], argv[[2]]))
argv <- list(c(NA, 3L, 4L), 3L); .Internal(rep_len(argv[[1]], argv[[2]]))
argv <- list(c(NA, NA, 30, -30), 4L); .Internal(rep_len(argv[[1]], argv[[2]]))
argv <- list(c(2, 3, 4, 5, 6, 7, 12, 22), 8L); .Internal(rep_len(argv[[1]], argv[[2]]))
argv <- list(c('50-54', '55-59', '60-64', '65-69', '70-74'), 20L); .Internal(rep_len(argv[[1]], argv[[2]]))
argv <- list(987.338461538462, 2L); .Internal(rep_len(argv[[1]], argv[[2]]))
argv <- list(1:5, 15); .Internal(rep_len(argv[[1]], argv[[2]]))
argv <- list(c(NA, 'green', 'black', 'blue'), 4L); .Internal(rep_len(argv[[1]], argv[[2]]))
argv <- list(1, 2L); .Internal(rep_len(argv[[1]], argv[[2]]))
argv <- list(0, 0L); .Internal(rep_len(argv[[1]], argv[[2]]))
argv <- list(FALSE, 1L); .Internal(rep_len(argv[[1]], argv[[2]]))
rep_len(NULL,0)
rep_len(NULL,2)
argv <- structure(list(1:5, each = 2), .Names = c('', 'each'));do.call('rep', argv)
argv <- list(structure(c(1L, 1L, 1L, 2L, 2L, 2L), .Label = c('Batch1',     'Batch2'), class = 'factor'), 2);do.call('rep', argv)
argv <- list(structure(c(11.3164921459501, 9.56444166646261,     23.868524352596, 8.592077957758, 0.187318691429722, -11.3963997363604,     -6.26079624982537, 6.05560822307356, -6.03903226622761, 4.13503361306269),     .Names = c('a', 'b', 'c', 'd', 'e', 'f', 'g', 'h', 'i', 'j')),     15);do.call('rep', argv)

argv <- list(0, 2000);do.call('rep', argv)
argv <- list(0 - (0+2i), 13);do.call('rep', argv)
argv <- list(c(1, 2, 3, 4, 7), c(3, 4, 5, 4, 2));do.call('rep', argv)
argv <- list(1:14, c(3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4));do.call('rep', argv)
argv <- structure(list(c(2, 2, -1, -1, -1, -1, 0, 0), each = 48),     .Names = c('', 'each'));do.call('rep', argv)
argv <- list(c('A', 'B'), c(48L, 44L));do.call('rep', argv)
argv <- structure(list(c('a', 'b', 'c'), each = 3), .Names = c('',     'each'));do.call('rep', argv)
{ rep(1,3) }
{ rep(1:3,2) }
{ rep(c(1,2),0) }
{ rep(as.raw(14), 4) }
{ rep(1:3, length.out=4) }
{ rep("hello", 3) }
{ rep(c(1,2),c(3,3)) }
{ rep(NA,8) }
{ rep(TRUE,8) }
{ rep(1:3, length.out=NA) }
{ x <- as.raw(11) ; names(x) <- c("X") ; rep(x, 3) }
{ x <- as.raw(c(11,12)) ; names(x) <- c("X","Y") ; rep(x, 2) }
{ x <- c(TRUE,NA) ; names(x) <- c("X",NA) ; rep(x, length.out=3) }
{ x <- 1L ; names(x) <- c("X") ; rep(x, times=2) } 
{ x <- 1 ; names(x) <- c("X") ; rep(x, times=0) }
{ x <- 1+1i ; names(x) <- c("X") ; rep(x, times=2) }
{ x <- c(1+1i,1+2i) ; names(x) <- c("X") ; rep(x, times=2) }
{ x <- c("A","B") ; names(x) <- c("X") ; rep(x, length.out=3) }
{ x<-c(1,2); names(x)<-c("X", "Y"); rep(x, c(3,2)) }
{ rep(c(1, 2), each = 2) }
{ rep(c(1, 2), each = 2, length.out = 5) }
{ rep(c(1, 2), each = 2, length.out = 3) }
{ rep(c(1, 2), times = 3) }
{ rep(c(1, 2), times = c(2, 3)) }
{ rep(c(1, 2), times = c(1, 2, 3)) }
{ rep(c(1, 2), times = c(2, 3), each = 2) }
{ x<-factor(c("a", "b", "a")); rep(x, times=3) }
{ x<-factor(c("a", "b", "a")); rep(x, length=5) }
rep(x<-42)
{ rep(function() 42) }
{ rep(7, times=character()) }
{ rep(7, times=NULL) }
{ rep(7, times="7") }
{ rep(7, length.out="7") }
{ rep(7, length.out=integer()) }
{ rep(7, length.out=NA) }
{ rep(7, length.out=NULL) }
{ rep(7, length.out=c(7, 42)) }
{ rep(7, each="7") }
{ rep(7, each=integer()) }
{ rep(7, each=NA) }
{ rep(7, each=NULL) }
{ rep(7, each=c(7, 42)) }
{ rep(7, times=NA) }
{ rep(7, times=-1) }
{ rep(c(7, 42), times=c(2, NA)) }
{ rep(7, times="foo") }
v <- 1; class(v) <- 'asdf'; names(v) <- 'asdf'; rep(v, 1)
v <- 1; class(v) <- 'asdf'; names(v) <- 'asdf'; rep(v, 2)
v <- 1; names(v) <- 'asdf'; rep(v, 1)
v <- 1; names(v) <- 'asdf'; rep(v, 2)
v <- 1; class(v) <- 'asdf'; rep(v, 1)
v <- 1; class(v) <- 'asdf'; rep(v, 2)
{ rep.cls <- function(x) 42; rep(structure(c(1,2), class='cls')); }
{ rep(paste0('hello', 1:10), 10) }
{ rep(paste0('hello', 1:10), 1:10) }
rep(' ', 20L, collapse = ' ')
rep(3, 4,)
rep(numeric(), length.out=2)
rep(character(), length.out=2)
rep(raw(), length.out=2)
rep(complex(), length.out=2)
rep(list(), length.out=2)
rep(numeric(), times=3)
rep(NULL)
