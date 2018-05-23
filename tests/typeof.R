# @line
# Tests about typeof.
# Note: typeof is an internal, and thus should normally not be available in the global state.
#       However, there is a definition in preloaded R files mapping the global variable typeof to this internal.
#       As we do not load these files yet, we have to introduce this definition. (TODO)
typeof <- function (x) .Internal (typeof (x)) ; typeof (1) ; typeof (5i)
typeof <- function (x) .Internal (typeof (x)) ; typeof (1L)
typeof <- function (x) .Internal (typeof (x)) ; typeof ("")
typeof <- function (x) .Internal (typeof (x)) ; typeof (NULL)
typeof <- function (x) .Internal (typeof (x)) ; typeof (NA) ; typeof (NA_integer_) ; typeof (NA_real_) ; typeof (NA_character_) ; typeof (NA_complex_)
typeof <- function (x) .Internal (typeof (x)) ; typeof (NaN) ; typeof (Inf)
typeof <- function (x) .Internal (typeof (x)) ; typeof (typeof) ; typeof (typeof (1))
typeof <- function (x) .Internal (typeof (x)) ; typeof (.Internal)
typeof <- function (x) .Internal (typeof (x)) ; runif <- function (...) .Internal (runif (...)) ; typeof (runif (1, 5L, 10L)) ; typeof (runif (1, FALSE, TRUE))
typeof <- function (x) .Internal (typeof (x)) ; f <- function (...) typeof (...) ; f (1) ; f (list (1, 2)) ; f (NULL)
typeof <- function (x) .Internal (typeof (x)) ; integer (0) ; typeof (integer (0))
typeof <- function (x) .Internal (typeof (x)) ; numeric (0) ; typeof (numeric (0))
typeof <- function (x) .Internal (typeof (x)) ; logical (0) ; typeof (logical (0))
typeof <- function (x) .Internal (typeof (x)) ; character (0) ; typeof (character (0))
typeof <- function (x) .Internal (typeof (x)) ; complex (0) ; typeof (complex (0))
typeof <- function (x) .Internal (typeof (x)) ; raw (0) ; typeof (raw (0))
