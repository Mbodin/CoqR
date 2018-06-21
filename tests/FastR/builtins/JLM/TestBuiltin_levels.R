argv <- structure(list(x = structure(c(1L, 1L, 1L, 1L, 1L, 1L,     1L, 1L, 1L, 1L, 2L, 2L, 2L, 2L, 2L, 2L, 2L, 2L, 2L, 2L),     .Label = c('1', '2'), class = 'factor')), .Names = 'x');do.call('levels', argv)

{ x <- 1 ; levels(x)<-"a"; levels(x);}
{ x <- 5 ; levels(x)<-"catdog"; levels(x);}
{ x <- 1 ; levels(x)<-NULL; levels(x)}
{ x <- 1 ; levels(x)<-1; levels(x);}
{ x <- 1 ; levels(x)<-4.5; levels(x);}
{ x <- 1 ; levels(x)<-c(1); levels(x);}
{ x <- 5 ; levels(x)<-c(1,2,3); levels(x);}
{ x <- 1 ; levels(x)<-c("cat", "dog"); levels(x)}
{ x <- 1 ; levels(x)<-c(3, "cat"); levels(x);}
{ x <- 1 ; levels(x)<-c(1, "cat", 4.5, "3"); levels(x);}
{ x <- 1 ; levels(x)<-NULL; levels(notx)}
{ x <- NULL; levels(x)<-"dog"; levels(x)}
