argv <- list(structure(1:12, .Dim = 3:4, comment = c('This is my very important data from experiment #0234', 'Jun 5, 1998')), c('This is my very important data from experiment #0234', 'Jun 5, 1998')); .Internal(`comment<-`(argv[[1]], argv[[2]]))
argv <- list(character(0), NULL); .Internal(`comment<-`(argv[[1]], argv[[2]]))
argv <- list(logical(0), NULL); .Internal(`comment<-`(argv[[1]], argv[[2]]))
{ x <- matrix(1:12, 3, 4); comment(x) <- c('This is my very important data from experiment #0234', 'Jun 5, 1998'); print(x); comment(x) }
