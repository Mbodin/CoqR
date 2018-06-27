lockEnvironment('foo', TRUE)
e <- new.env(); e$a <- 'foo'; lockEnvironment(e, FALSE); e$b <- 123
e <- new.env(); e$a <- 'foo'; lockEnvironment(e, FALSE); e$a <- 123
e <- new.env(); e$a <- 'foo'; lockEnvironment(e, 'a'); e$b <- 123
e <- new.env(); e$a <- 'foo'; lockEnvironment(e, 'a'); e$a <- 123
e <- new.env(); e$a <- 'foo'; lockEnvironment(e, logical()); e$b <- 123
e <- new.env(); e$a <- 'foo'; lockEnvironment(e, logical()); e$a <- 123
