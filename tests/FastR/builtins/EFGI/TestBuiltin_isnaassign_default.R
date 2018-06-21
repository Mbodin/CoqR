argv <- structure(list(x = 9L, value = TRUE), .Names = c('x',     'value'));do.call('is.na<-.default', argv)
argv <- structure(list(x = structure(c('A', '3', 'C'), class = 'AsIs'),     value = 2), .Names = c('x', 'value'));do.call('is.na<-.default', argv)
{ x <- c(0:4); is.na(x) <- c(2, 4); x }
{ x<-factor(c("a", "b", "a")); is.na(x)<-1; x }
{ x<-factor(c("a", "b", "a")); is.na(x)<-2; x }
{ x<-factor(c("a", "b", "a")); is.na(x)<-c(1, 3); x }
