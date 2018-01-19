
# This file is meant to be read line-by-line, each line being independent from the other.
# In particular, if the state at the beginning of each line should always be the initial state.
# A test passes if the output of the tested interpreter is the same than R’s.
# In particular, all step should return the same output.

# Tests about aborting primitives.
return
return (1)
return (0/0)
return (NULL)
(return (1)) (2)
break
break (1)
next
next (1)
(function (){ 1 ; return (2) ; 3 }) ()
repeat break
x <- FALSE ; repeat if (x) break else x <- TRUE
x <- FALSE ; repeat if (x) break else { x <- TRUE ; next ; x <- FALSE }
x <- TRUE ; while (x) { x <- FALSE ; next ; x <- TRUE }
while (TRUE) break
repeat break + return (1)
repeat return (1) + break
f <- function () break ; while (TRUE) f ()
f <- function () next ; while (TRUE) f ()
while (TRUE) (function () break) ()
while (TRUE) (function () next) ()
(function () repeat return (1)) ()
(function () while (TRUE) return (1)) ()
(function () while (FALSE) return (1)) () ; (function () if (FALSE) return (1)) ()
x <- 10 ; while (x > 5) x <- x - 1 ; x
x <- 10 ; repeat if (x < 5) break else x <- x - 1 ; x
x <- 10 ; while (x > 5) { repeat break ; x <- x - 1 ; next ; x <- x + 1 } ; x

# Tests about if.
if ("TRUE") 1 else ""
if ("True") "1" else 2
if ("true") 1L else 2
if ("T") 2 else 3L
if ("t") "" else NA
if ("tRUE") "NA" else 2L
if ("FALSE") 1 else TRUE
if ("False") TRUE else 1
if ("false") FALSE else ""
if ("F") "" else FALSE
if ("f") 2L else TRUE
if ("fALSE") FALSE else 2L
if ("") 1 else NULL
if ("0") NULL else ""
if ("1") NULL else NA
if (c (TRUE, FALSE)) NULL else 1L
if (0) 1L else NULL
if (1) NA else NULL
if (0L) "1" else NULL
if (1L) 1L else NULL
if (1:3) NA else NULL
if (function () TRUE) (function () FALSE) else NA
if (.Internal) 1 else ""
if (if (TRUE) FALSE else TRUE) 1 else ""
if (TRUE) a <- 1 else b <- 1 ; a ; b
if (FALSE) a <- 1 else b <- 1 ; b ; a
if (TRUE) 1 else 1 (2)
if (FALSE) 1 (2) else 1
if (FALSE) 1
if (TRUE) 1
if (a <- TRUE) NULL else NULL ; a
1 + if (TRUE) 2
if (NA) NaN else ""
if (NaN) 1L else NaN
if (NULL) NaN else FALSE
if ("NULL") 1 else NaN
if ("NA") NA else Inf
if (" ") NaN else NULL
if ("#") NA else NaN

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

# Tests about lazy evaluation and function application.
(function (x, y = x) { x <- 1 ; y ; x <- 2 ; y }) (3)
x <- 1 ; (function (x, y) { if (x) y }) (FALSE, x <- 2) ; x
x <- 1 ; (function (x, y, z) { z ; if (x) y }) (FALSE, x <- 2, x <- 3) ; x
x <- 1 ; (function (x, y, z) { z ; if (x) y }) (TRUE, x <- 2, x <- 3) ; x
x <- 1 ; (function (x, y) { (function (x, y) if (x) y) (x, y) }) (FALSE, x <- 2) ; x
(function (x, y = x <- 1) { x <- 2 ; y ; x }) (3)
(function (x, y = x <- 1) { x }) (3)
z <- 1 ; (function (x, y = x) NULL) (z <- 2) ; z
z <- 1 ; (function (x, y = x) y) (z <- 2) ; z
apply <- function (f, ...) f (...) ; apply (function () 1) ; apply (function (x) x, 2) ; apply (function (x, y) x, 1) ; apply (function (x, y) y, 1, 2)
a <- b <- c <- d <- e <- 1 ; f <- function (x, y, ..., z) 1 ; f () ; f (a <- 2) ; a; f (a <- 3, b <- 4) ; a ; b ; f (a <- 5, b <- 6, d <- 7, e <- 8) ; a ; b ; c ; d ; e ; f (z = a <- 9, b <- 10, c <- 11, d <- 12, e <- 13) ; a ; b ; c ; d ; e
a <- b <- 1 ; f <- function (x, y) if (missing (y)) x ; f (a <- 2, b <- 3) ; a ; b ; f (a <- 4) ; a ; b ; f ()
missing ; missing (x)
f <- function (x, y, z) x ; g <- function (x, ...) f (..., x) ; g (1) ; g (1, 2) ; g (1, 2, 3)

# Tests about implicit conversions and equality.
TRUE + TRUE ; TRUE + FALSE ; FALSE + FALSE
TRUE - TRUE ; TRUE - FALSE ; FALSE - FALSE
TRUE * TRUE ; TRUE * FALSE ; FALSE * FALSE
TRUE / TRUE ; FALSE / TRUE ; FALSE / FALSE
a <- 1L + 2 ; a ; .Internal (typeof (a))
a <- 1L + TRUE ; a ; .Internal (typeof (a))
a <- 1L + ""
a <- 1L + .Internal
a <- 1 + 2L ; a ; .Internal (typeof (a))
a <- 1 + TRUE ; a ; .Internal (typeof (a))
a <- 1 + ""
a <- 1 + .Internal
a <- "" + 2
a <- "" + 2L
a <- "" + TRUE
a <- "" + .Internal
a <- FALSE + 2 ; a ; .Internal (typeof (a))
a <- FALSE + 2L ; a ; .Internal (typeof (a))
a <- FALSE + ""
a <- FALSE + .Internal
2 == 2L ; -0 == 0 ; -0 == 0L ; 1 == TRUE ; 1L == TRUE ; 0 == FALSE ; 0L == FALSE
"FALSE" == FALSE ; "False" == FALSE ; "false" == FALSE ; "F" == FALSE ; "f" == FALSE ; "fALSE" == FALSE
"TRUE" == TRUE ; "True" == TRUE ; "true" == TRUE ; "T" == TRUE ; "t" == TRUE ; "tRUE" == TRUE
NA == NA ; NaN == NaN ; NA == NaN ; NaN == 0/0 ; NaN == -0/0 ; NaN == 1 + 0/0 ; NaN == 1 + NaN
NA_integer_ == NA ; NA_character_ == NA ; NA_integer_ == NA_character_
NULL == 0 ; NULL == NA ; NULL == NaN ; NULL == FALSE ; NULL == TRUE
0 == -0 ; 0L == -0L ; 1/Inf == 0 ; -1/Inf == 0 ; NaN == Inf - Inf
.Internal == .Internal
c (1, 1L) ; c (1, NULL) ; c (1, TRUE) ; c (1, "a") ; c (1, NA) ; c (1, NaN)
c (1L, 1L) ; c (1L, NULL) ; c (1L, TRUE) ; c (1L, "a") ; c (1L, NA) ; c (1L, NaN)
c (NULL, 1L) ; c (NULL, NULL) ; c (NULL, TRUE) ; c (NULL, "a") ; c (NULL, NA) ; c (NULL, NaN)
c (TRUE, 1L) ; c (TRUE, NULL) ; c (TRUE, TRUE) ; c (TRUE, "a") ; c (TRUE, NA) ; c (TRUE, NaN)
c ("b", 1L) ; c ("b", NULL) ; c ("b", TRUE) ; c ("b", "a") ; c ("b", NA) ; c ("b", NaN)
c (NA, 1L) ; c (NA, NULL) ; c (NA, TRUE) ; c (NA, "a") ; c (NA, NA) ; c (NA, NaN)
c (NaN, 1L) ; c (NaN, NULL) ; c (NaN, TRUE) ; c (NaN, "a") ; c (NaN, NA) ; c (NaN, NaN)
c (1, TRUE, "a") ; c (c (1, TRUE), "a") ; c (1, c (TRUE, "a"))

# Tests about assignments.
x <- y <- 2 ; x ; y
x <- 2 -> y ; x ; y
x <- 2 ; x <- x <- x + 1 ; x
x <- 2 ; x <- x + 1 -> x ; x
x <- 2 ; y <- x <- x + 1 ; y ; x
x <- 2 ; y <- x + 1 -> x ; y ; x
x <- 1 ; y <- x ; x <- 2 ; y
(x <- 1) + (x <- 2)
x <- 1 ; x <- NULL ; x ; x <- NA ; x ; x <- NaN ; x
x <- 1 ; "x" <- 2 ; x
y <- 1 ; x <- "y" ; x <- 2 ; y ; x
x <- 1 ; y <- x ; x <- 2 ; y ; x

# Tests about the modification of primitive operators.
"if" <- function (x, y, z) x + y + z ; if (1) 2 else 3
"if" <- function (x) -x ; if (1) 2 else 3
"(" <- function (x) 2 * x ; (2)
"(" <- function () 1 ; (2)
"{" <- function (x) 2 * x ; {2}
"<-" <- function (x, y) x + y ; 1 <- 2 ; 3 -> 4
"<<-" <- function (x, y) x + y ; 1 <<- 2 ; 3 ->> 4
"function" <- function (x, y, z) y ; function (x) 2
"+" <- function (x, y) x - y ; 1 + 2

# Tests about cat (for outputs).
cat ("") ; cat (")") ; cat ("}") ; cat (">") ; cat ("]") ; cat ("(") ; cat ("{") ; cat ("<") ; cat ("[")
cat ("\n") ; cat (")\n") ; cat ("}\n") ; cat (">\n") ; cat ("]\n") ;cat ("(\n") ; cat ("{\n") ; cat ("<\n") ; cat ("[\n")
cat (1) ; cat (2L) ; cat (.5) ; cat (TRUE) ; cat (NA) ; cat (Inf) ; cat (NaN) ; cat (NULL) ; cat ("TRUE")
cat ("function (x) x") ; cat (function (x) x)
cat (cat) ;
cat (a <- 1) ; a

# Tests about randomness.
runif ()
typeof <- function (x) .Internal (typeof (x)) ; typeof (runif (1))
length (runif (42))

