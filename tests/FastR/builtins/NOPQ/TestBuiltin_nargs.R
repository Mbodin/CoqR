nargs( );
{  f <- function (a, b, c) { nargs() }; f() }
{  f <- function (a, b, c) { nargs() }; f(1, 2) }
{  f <- function (a, b=TRUE, c=FALSE) { nargs() }; f(1) }
{  f <- function (a, b=TRUE, c=FALSE) { nargs() }; f(1, FALSE) }
{  f<-function(x, ..., y=TRUE) { nargs() }; f(1, 2, 3) }
{  f <- function (a, b, c) { nargs() }; f(,,a) }
