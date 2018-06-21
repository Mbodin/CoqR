argv <- list(quote(y ~ ((g1) * exp((log(g2/g1)) * (1 - exp(-k * (x - Ta)))/(1 - exp(-k * (Tb - Ta)))))), FALSE, -1L, TRUE); .Internal(all.names(argv[[1]], argv[[2]], argv[[3]], argv[[4]]))
argv <- list(logical(0), logical(0), -1L, TRUE); .Internal(all.names(argv[[1]], argv[[2]], argv[[3]], argv[[4]]))
argv <- list(structure(numeric(0), .Dim = c(0L, 0L)), TRUE, -1L, FALSE); .Internal(all.names(argv[[1]], argv[[2]], argv[[3]], argv[[4]]))
argv <- list(structure(list(c0 = structure(integer(0), .Label = character(0), class = 'factor')), .Names = 'c0', row.names = character(0), class = 'data.frame'), structure(list(c0 = structure(integer(0), .Label = character(0), class = 'factor')), .Names = 'c0', row.names = character(0), class = 'data.frame'), -1L, FALSE); .Internal(all.names(argv[[1]], argv[[2]], argv[[3]], argv[[4]]))
argv <- list(0.1, FALSE, -1L, TRUE); .Internal(all.names(argv[[1]], argv[[2]], argv[[3]], argv[[4]]))
all.names(quote(y ~ ((g1) * exp((log(g2/g1)) * (1 - exp(-k * (x - Ta)))/(1 - exp(-k * (Tb - Ta)))))), FALSE, -1L, TRUE)
all.names(quote(a+y+z+y*y*foo(bar/2)), functions=TRUE, max.names=10, unique=TRUE)
all.names(quote(a+y+z+y*y*foo(bar/2)), functions=TRUE, max.names=10, unique=FALSE)
all.names(quote(a+y+z+y*y*foo(bar/2)), functions=TRUE, max.names=2, unique=TRUE)
all.names(quote(a+y+z+y*y*foo(bar/2)), functions=FALSE, max.names=10, unique=TRUE)
all.names(quote(a+y+z+y*y*function(x=bar/2) baz(1)), functions=TRUE, max.names=10, unique=TRUE)
all.names(quote(a+y+z+y*y*function(x=bar/2) baz(1)), functions=TRUE, max.names=10, unique=FALSE)
all.names(quote(a+y+z+y*y*function(x=bar/2) baz(1)), functions=TRUE, max.names=2, unique=TRUE)
all.names(quote(a+y+z+y*y*function(x=bar/2) baz(1)), functions=FALSE, max.names=10, unique=TRUE)
{ all.names(expression(sin(x+y+x)), functions=F) }
{ all.names(expression(sin(x+y+x)), functions=T) }
{ all.names(expression(sin(x+y+x)), functions=NULL) }
{ all.names(expression(sin(x+y+x)), functions=NA) }
{ all.names(expression(sin(x+y+x)), max.names=NULL) }
{ all.names(expression(sin(x+y+x)), max.names=NA) }
{ all.names(expression(sin(x+y+x)), unique=F) }
{ all.names(expression(sin(x+y+x)), unique=T) }
{ all.names(expression(sin(x+y+x)), unique=NULL) }
{ all.names(expression(sin(x+y+x)), unique=NA) }
{ all.names(quote(switch(x, 'median' =, 'hello' = print('hello case')))) }
{ all.names(as.symbol('a'), max.names=1)}
{ all.names(as.symbol('a'), max.names=0)}
{ all.names(as.symbol('a'), max.names=-1)}
{ all.names(as.symbol('a'), max.names=-2)}
