argv <- structure(list(x = TRUE), .Names = 'x');do.call('isTRUE', argv)
{ isTRUE(NULL) }
{ isTRUE(TRUE) }
{ isTRUE(FALSE) }
{ isTRUE(NA) }
{ isTRUE(1) }
{ isTRUE(as.vector(TRUE)) }
{ isTRUE(as.vector(FALSE)) }
{ isTRUE(as.vector(1)) }
{ file.path("a", "b", c("d","e","f")) }
{ file.path() }
