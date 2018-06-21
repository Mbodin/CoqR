argv <- structure(list(x = 1), .Names = 'x');do.call('as.expression', argv)
{ as.expression("name") }
{ as.expression(NULL) }
{ as.expression(123) }
{ as.expression(as.symbol(123)) }
{ as.expression(c(1,2)) }
{ as.expression(list(1,2)) }
{ as.expression(list("x" = 1, "y" = 2)) }
{ as.expression(sum) }
{ as.expression(function() {}) }
