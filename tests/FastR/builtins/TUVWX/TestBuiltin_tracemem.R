tracemem(NULL)
retracemem(NULL)
retracemem(c(1,10,100), 1:10)
v <- c(1,10,100); tracemem(v); x <- v; y <- v; x[[1]]<-42; y[[2]] <- 84
v <- c(1,10,100); tracemem(v); x <- v; y <- v; x[[1]]<-42; untracemem(v); y[[2]] <- 84
v <- list(1,10,100); tracemem(v); x <- v; x[[1]]<-42;
v <- c(1,10,100); tracemem(v); x <- v[-1]; retracemem(x, retracemem(v)); u <- x; u[[1]] <- 42;
x<-1:10; retracemem(x, c("first", "second")) 
