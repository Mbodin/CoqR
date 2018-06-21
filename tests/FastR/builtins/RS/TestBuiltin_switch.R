argv <- structure(list('forward', forward = 'posS', reverse = 'negS'),     .Names = c('', 'forward', 'reverse'));do.call('switch', argv)
argv <- list(3L);do.call('switch', argv)
argv <- list(2L, TRUE, FALSE, FALSE);do.call('switch', argv)
{ test1 <- function(type) { switch(type, mean = 1, median = 2, trimmed = 3) };test1("median")}
{switch(3,1,2,3)}
{switch(4,1,2,3)}
{switch(4,1,2,z)}
{ test1 <- function(type) { switch(type, mean = mean(c(1,2,3,4)), median = 2, trimmed = 3) };test1("mean")}
{ u <- "uiui" ; switch(u, "iuiu" = "ieps", "uiui" = "miep") }
{ answer<-"no";switch(as.character(answer), yes=, YES=1, no=, NO=2,3) }
{ x <- "<"; v <- switch(x, "<=" =, "<" =, ">" = TRUE, FALSE); v }
{ x <- "<"; switch(x, "<=" =, "<" =, ">" = TRUE, FALSE) }
{ x <- "<"; switch(x, "<=" =, "<" =, ">" =, FALSE) }
{ a <- NULL ; switch(mode(a), NULL="naught") }
{ a <- NULL ; switch(mode(a), NULL=) }
{ x <- "!"; v <- switch(x, v77, "<=" =, "<" =, ">" = 99, v55)}
{ x <- "!"; v <- switch(x, ""=v77, "<=" =, "<" =, ">" = 99, v55)}
switch('q', a=42,)
{ x <- switch(NA, 1, 2, 3); x }
{ switch(quote(a), 1, 2, 3) }
{ x <- switch(expression(quote(1)), 1, 2, 3); x }
{ x <- switch(expression(quote(1), quote(2)), 1, 2, 3); x }
{ x <- switch(list(2), 1, 2, 3); x }
{ x <- switch(list(1,2,3), 1, 2, 3); x }
