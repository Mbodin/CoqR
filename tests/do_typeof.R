# @line
# Tests about typeof.
typeof (1) ; typeof (5i)
typeof (1L)
typeof ("")
typeof (NULL)
typeof (NA) ; typeof (NA_integer_) ; typeof (NA_real_) ; typeof (NA_character_) ; typeof (NA_complex_)
typeof (NaN) ; typeof (Inf)
typeof (typeof) ; typeof (typeof (1))
typeof (.Internal)
runif <- function (...) .Internal (runif (...)) ; typeof (runif (1, 5L, 10L)) ; typeof (runif (1, FALSE, TRUE))
f <- function (...) typeof (...) ; f (1) ; f (list (1, 2)) ; f (NULL)
integer (0) ; typeof (integer (0))
numeric (0) ; typeof (numeric (0))
logical (0) ; typeof (logical (0))
character (0) ; typeof (character (0))
complex (0) ; typeof (complex (0))
raw (0) ; typeof (raw (0))

typeof2 <- function (x) .Internal (typeof (x)) ; typeof == typeof2

