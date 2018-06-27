parent.env() <- new.env()
parent.env(NULL) <- new.env()
parent.env(1) <- new.env()
parent.env(c(1,2,3)) <- new.env()
parent.env(emptyenv()) <- new.env()
e <- new.env(); parent.env(e) <- 44
e <- new.env(); parent.env(e) <- NULL
e <- new.env(); parent.env(e) <- emptyenv(); parent.env(e)
e <- new.env(); parent.env(e) <- c(1,2,3)
e <- new.env(); e2 <- new.env(); parent.env(e) <- e2; parent.env(e)
