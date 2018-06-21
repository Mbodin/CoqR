argv <- structure(list(x = c(0.467590032349108, 0.560407538764412)),     .Names = 'x');do.call('diff', argv)
{ diff(1:10, 2) }
{ diff(1:10, 2, 2) }
{ x <- cumsum(cumsum(1:10)) ; diff(x, lag = 2) }
{ x <- cumsum(cumsum(1:10)) ; diff(x, differences = 2) }
