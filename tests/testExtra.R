# @line
# This file is meant to be read line-by-line, each line being independent from the other.
# The state at the beginning of each line should always be the initial state.
# Furthermore, if an error is thrown, the next line should be unaffected by this error, starting back from the initial state.
# A test passes if the output of the tested interpreter is the same than R’s.
# All step should return the same output.

# Constants
NULL ; TRUE ; FALSE ; 1 ; 1L ; 0 ; -0 ; 0L ; -0L ; 1i ; -1i ; 0i ; -0i ; NaN ; Inf ; -Inf
'' ; "" ; 'TRUE' ; "FALSE" ; '1' ; "1L" ; '0' ; "-0" ; '0L' ; "-0L" ; '1i' ; "0i" ; '-0i' ; "NaN" ; 'Inf' ; "-Inf"
function (x) x ; function () 1 ; function () x
NA_character_ ; NA_complex_ ; NA_real_ ; NA_integer_ ; NA
.Internal ; T ; F
0.5 ; .5 ; .50 ; 0.50 ; 00.50 ; 0000 ; 0000L ; 0000i ; -0000 ; -0000L ; -0000i ; .5L
001 ; 001L ; 001. ; 001.00 ; 001.L
-001 ; -001L ; -001. ; -001.00 ; -001.L ;
0000.L
0000.000L
.000L
.L
1e3 ; 1e3L ; 1.5e3 ; 1.5e3L ; 1.52e1 ; 1.52e1L
1E3 ; 1E3L ; 1.5E3 ; 1.5E3L ; 1.52E1 ; 1.52E1L
0.99999999999999999999 ; 0.99999999999999999999999999999999
1e10000 ; 1e10000L

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
x <- 0 ; (function () return (1) -> x) () ; (function () x <- return (2)) () ; x
(function () while (TRUE) return (1)) ()
(function () while (FALSE) return (1)) () ; (function () if (FALSE) return (1)) ()
x <- 10 ; while (x > 5) x <- x - 1 ; x
x <- 10 ; repeat if (x < 5) break else x <- x - 1 ; x
x <- 10 ; while (x > 5) { repeat break ; x <- x - 1 ; next ; x <- x + 1 } ; x
a <- FALSE ; while (TRUE) if (a) a <- break else a <- TRUE ; a

# Tests about if.
if ("TRUE") 1 else ""
if ('True') "1" else 2
if ("true") 1L else 2
if ("T") 2 else 3L
if ('t') '' else NA
if ("tRUE") 'NA' else 2L
if ("FALSE") 1 else TRUE
if ('False') TRUE else 1
if ("false") FALSE else ''
if ("F") "" else FALSE
if ('f') 2L else TRUE
if ("fALSE") FALSE else 2L
if ("") 1 else NULL
if ("0") NULL else ""
if ('1') NULL else NA
if (c (TRUE, FALSE)) NULL else 1L
if (0) 1L else NULL
if (1) NA else NULL
if (0L) '1' else NULL
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
x <- if (TRUE) 3 ; x
1 + if (FALSE) 2
x <- if (FALSE) 3 ; x
if (NA) NaN else ""
if (NaN) 1L else NaN
if (NULL) NaN else FALSE
if ("NULL") 1 else NaN
if ('NA') NA else Inf
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
typeof <- function (x) .Internal (typeof (x)) ; f <- function (...) typeof (...) ; f (1) ; f (list (1, 2)) ; f (NULL)
typeof <- function (x) .Internal (typeof (x)) ; integer (0) ; typeof (integer (0))
typeof <- function (x) .Internal (typeof (x)) ; numeric (0) ; typeof (numeric (0))
typeof <- function (x) .Internal (typeof (x)) ; logical (0) ; typeof (logical (0))
typeof <- function (x) .Internal (typeof (x)) ; character (0) ; typeof (character (0))
typeof <- function (x) .Internal (typeof (x)) ; complex (0) ; typeof (complex (0))
typeof <- function (x) .Internal (typeof (x)) ; raw (0) ; typeof (raw (0))

# Tests about lazy evaluation and function application.
(function (x, y = x) { x <- 1 ; y ; x <- 2 ; y }) (3)
x <- 1 ; (function (x, y) { if (x) y }) (FALSE, x <- 2) ; x
x <- 1 ; (function (x, y, z) { z ; if (x) y }) (FALSE, x <- 2, x <- 3) ; x
x <- 1 ; (function (x, y, z) { z ; if (x) y }) (TRUE, x <- 2, x <- 3) ; x
x <- 1 ; (function (x, y) { (function (x, y) if (x) y) (x, y) }) (FALSE, x <- 2) ; x
x <- 0 ; (function (x, y = x <- 1) { x <- 2 ; y ; x }) (3) ; x
(function (x, y = x <- 1) { x }) (3)
z <- 1 ; (function (x, y = x) NULL) (z <- 2) ; z
z <- 1 ; (function (x, y = x) y) (z <- 2) ; z
apply <- function (f, ...) f (...) ; apply (function () 1) ; apply (function (x) x, 2) ; apply (function (x, y) x, 1) ; apply (function (x, y) y, 1, 2)
a <- b <- c <- d <- e <- 1 ; f <- function (x, y, ..., z) 1 ; f () ; f (a <- 2) ; a; f (a <- 3, b <- 4) ; a ; b ; f (a <- 5, b <- 6, d <- 7, e <- 8) ; a ; b ; c ; d ; e ; f (z = a <- 9, b <- 10, c <- 11, d <- 12, e <- 13) ; a ; b ; c ; d ; e
a <- b <- 1 ; f <- function (x, y) if (missing (y)) x ; f (a <- 2, b <- 3) ; a ; b ; f (a <- 4) ; a ; b ; f ()
missing ; missing (x)
missing ("x")
missing (1 + 2)
f <- function (x) missing (x) ; f () ; f (1) ; f (x = 1) ; f (1, 2)
f <- function (x) missing ("x") ; f () ; f (1) ; f (x = 1) ; f (1, 2)
f <- function (x) { y <- "x" ; missing (y) } ; f () ; f (1) ; f (x = 1) ; f (1, 2)
f <- function (x = 0) missing (x) ; f () ; f (1) ; f (x = 1) ; f (1, 2)
f <- function (x = NULL) missing (x) ; f () ; f (NULL) ; f (x = NULL) ; f (NULL, NULL)
f <- function (x = 0) { x ; missing (x) } ; f () ; f (1) ; f (x = 1) ; f (1, 2)
f <- function (x) { x ; missing (x) } ; f (1) ; f (x = 1) ; f (1, 2) ; f ()
f <- function (...) missing (...) ; f () ; f (1) ; f (1, 2) ; f (x = 1)
f <- function (x) missing (y) ; g <- function (y) f (y) ; g (x = 1)
f <- function (x) missing (y) ; g <- function (y) f (y) ; g (y = 1)
f <- function (x) missing (y) ; g <- function (y) f (y) ; g (1)
f <- function (x) missing ("y") ; g <- function (y) f (y) ; g (x = 1)
f <- function (x) missing ("y") ; g <- function (y) f (y) ; g (y = 1)
f <- function (x) missing ("y") ; g <- function (y) f (y) ; g (1)
f <- function (...) missing ("x") ; g <- function (x) f (x) ; g (x = 1)
f <- function (...) missing ("x") ; g <- function (x) f (x) ; g (1)
f <- function (x) function (y) missing (x) ; f () ; f ("y") ()
f <- function (m, x) m (x) ; f (missing) ; f (missing, NULL) ; f (missing, f ())
f <- function (x, y, z) x ; g <- function (x, ...) f (..., x) ; g (1) ; g (1, 2) ; g (1, 2, 3)
f <- function (x) x ; g <- function (...) f (...) ; g (1) ; g ()
f <- function (x, y, z) y ; g <- function (...) f (...) ; g (1, 2, 3) ; g (1, 2) ; g (y = 2)
f <- function (...) ... ; f (1)
head <- function (x, ...) x ; head (1, 2, 3) ; head ()
f <- function (x, ...) if (x) TRUE else f (TRUE, x, ...) ; f (FALSE) ; f (FALSE, FALSE)
f <- function (x, ...) if (x) TRUE else f (..., x) ; f (FALSE, FALSE, TRUE)
f <- function (...) ..2 ; f (1, 2, 3) ; f (1, 2) ; f (1)
f <- function (...) ..10 ; f (1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11) ; f (10)
f <- function (...) missing (..2) ; f (1) ; f (1, 2) ; f (1, 2, 3)
f <- function (...) missing (..100) ; f (1)
f <- function (...) missing (..999999999) ; f (1)
f <- function (...) missing (..999999999999999999) ; f () ; f (1) ; f (1, 2)
f <- function (...) ..0 ; f (1) ; f ()
f <- function (...) ..1 ; f (1) ; f ()
f <- function (...) ..01 ; f (1) ; f ()
f <- function (...) ..00 ; f (1) ; f ()
function (..., x, y, z, ...) x
function (x, y, z, x) y
f <- function (x, y) x ; f (x = 1, "x" = 1)
f <- function (x = x) x ; f (1) ; f ()
f <- function (x = 0, ...) x ; f () ; f (1, 2, 3) ; f (1, 2, x = 3)
g <- function (x) x ; f <- function (y = 0, ...) g (...) ; f (1, 2) ; f (1)
g <- function () 1 ; f <- function (...) g (...) ; f ()
g <- function (x) x ; f <- function (...) g (...) ; f (2) ; f ()
g <- function (x) x ; f <- function (...) g (...) ; f (1, 2)
g <- function (x) x ; f <- function (...) g (...) ; g <- function (x, y) x ; f (1) ; f (1, 2) ; f (1, 2, 3)
g <- function (x, y) x * y ; f <- function (...) g (...) ; f (2, 3) ; f (2, 3, 5)
g <- function (x, y) x * y ; f <- function (...) g (...) ; f (list (2, 3))
g <- function (x, y, z) x * y * z ; f <- function (...) g (...) ; f (2, 3, 5) ; f (2, 3, 5, 7)
g <- function (x, y, z) x * y * z ; f <- function (...) g (...) ; f (list (2, 3, 5))
g <- function (x, y, z) x * y * z ; f <- function (...) g (...) ; f (x = 2, y = 3, z = 5) ; f (a = 2, b = 3, c = 5)
f <- function (ab, abc) ab ; f (a = 1, ab = 2)
f <- function (ab, abc) abc ; f (a = 1, ab = 2)
f <- function (..., x) 1 ; f (1, 2, 3, 4, 5) ; f (1) ; f ()
f <- function (..., x) x ; f (1, 2, 3, 4, 5) ; f (1) ; f ()
f <- function (..., x) x ; f (x = 2, 3, 5, 7, 5) ; f (1, 2, x = 3, 4, 5) ; f (1, 2, 3, 4, x = 5) ; f ("x" = 1, 2, 3, 4, 5) ; f (1, 2, "x" = 3, 4, 5) ; f (1, 2, 3, 4, "x" = 5) ; f (x = 1, 2, 3, 4, "x" = 5)
g <- function (x, y, z) x * y * z ; f <- function (..., x) g (...) ; f (2, 3, 5, 7) ; f (x = 2, 3, 5, 7) ; f (2, 3, x = 5, 7) ; f (2, 3, 5, x = 7) ; f ("x" = 2, 3, 5, 7) ; f (2, 3, "x" = 5, 7) ; f (2, 3, 5, "x" = 7) ; f (x = 2, 3, 5, "x" = 7)
f <- function (x, ...) 1 ; f (1, 2, 3, 4, 5) ; f (1) ; f ()
f <- function (x, ...) x ; f (1, 2, 3, 4, 5) ; f (1) ; f ()
f <- function (x, ...) x ; f (x = 2, 3, 5, 7, 5) ; f (1, 2, x = 3, 4, 5) ; f (1, 2, 3, 4, x = 5) ; f ("x" = 1, 2, 3, 4, 5) ; f (1, 2, "x" = 3, 4, 5) ; f (1, 2, 3, 4, "x" = 5) ; f (x = 1, 2, 3, 4, "x" = 5)
g <- function (x, y, z) x * y * z ; f <- function (x, ...) g (...) ; f (2, 3, 5, 7) ; f (x = 2, 3, 5, 7) ; f (2, 3, x = 5, 7) ; f (2, 3, 5, x = 7) ; f ("x" = 2, 3, 5, 7) ; f (2, 3, "x" = 5, 7) ; f (2, 3, 5, "x" = 7) ; f (x = 2, 3, 5, "x" = 7)
g <- function (a, b) a ; f <- function (x, ...) g (...) ; f (1, 2, 3) ; f (1, 2) ; f (1, 2, x = 3) ; f (a = 1, 2, 3) ; f (b = 1, 2, x = 3)
f <- function (..., ab) ab ; f (1, 2, ab = 3, 4, 5) ; f (1, 2, a = 3, 4, 5)
g <- function () 1 ; f <- function (g) g () ; f (2) ; f (function () 3)
g <- function () 1 ; f <- function (g) { g <- 4 ; g () } ; f (2) ; f (function () 3) ; g <- 5 ; g ()
g <- function () 1 ; f <- function (g) (g) () ; f (function () 3) ; f (2)
f <- function (x) 1 ; f (2) ; f () ; f (a) ; f (..1) ; f (TRUE (3)) ; f (1, 2)
1 ()
TRUE ()
FALSE ()
NULL ()
NA ()
NaN ()
"1" ()
"" ()

# Tests about explicit conversions.
is.null (1) ; is.null (NULL) ; is.null ("1") ; is.null (1L) ; is.null (NA) ; is.null (NaN) ; is.null (Inf) ; is.null (x = -1) ; is.null ("x" = -1) ; is.null (y = -1)
is.logical (1) ; is.logical (NULL) ; is.logical ("1") ; is.logical (1L) ; is.logical (NA) ; is.logical (NaN) ; is.logical (Inf) ; is.logical (x = -1) ; is.logical ("x" = -1) ; is.logical (y = -1)
is.integer (1) ; is.integer (NULL) ; is.integer ("1") ; is.integer (1L) ; is.integer (NA) ; is.integer (NaN) ; is.integer (Inf) ; is.integer (x = -1) ; is.integer ("x" = -1) ; is.integer (y = -1)
is.double (1) ; is.double (NULL) ; is.double ("1") ; is.double (1L) ; is.double (NA) ; is.double (NaN) ; is.double (Inf) ; is.double (5i) ; is.double (1 + 3i) ; is.double (x = -1) ; is.double ("x" = -1) ; is.double (y = -1)
is.complex (1) ; is.complex (NULL) ; is.complex ("1") ; is.complex (1L) ; is.complex (NA) ; is.complex (NaN) ; is.complex (Inf) ; is.complex (5i) ; is.complex (1 + 3i) ; is.complex (x = -1) ; is.complex ("x" = -1) ; is.complex (y = -1)
is.character (1) ; is.character (NULL) ; is.character ("1") ; is.character (1L) ; is.character (NA) ; is.character (NaN) ; is.character (Inf) ; is.character (x = -1) ; is.character ("x" = -1) ; is.character (y = -1)
is.numeric (1) ; is.numeric (NULL) ; is.numeric ("1") ; is.numeric (1L) ; is.numeric (NA) ; is.numeric (NaN) ; is.numeric (Inf) ; is.numeric (5i) ; is.numeric (1 + 3i) ; is.numeric (x = -1) ; is.numeric ("x" = -1) ; is.numeric (y = -1)
is.atomic (1) ; is.atomic (NULL) ; is.atomic ("1") ; is.atomic (1L) ; is.atomic (NA) ; is.atomic (NaN) ; is.atomic (Inf) ; is.atomic (5i) ; is.atomic (1 + 3i) ; is.atomic (x = -1) ; is.atomic ("x" = -1) ; is.atomic (y = -1)
is.recursive (1) ; is.recursive (NULL) ; is.recursive ("1") ; is.recursive (1L) ; is.recursive (NA) ; is.recursive (NaN) ; is.recursive (Inf) ; is.recursive (5i) ; is.recursive (1 + 3i) ; is.recursive (x = -1) ; is.recursive ("x" = -1) ; is.recursive (y = -1)
is.array (1) ; is.array (NULL) ; is.array ("1") ; is.array (1L) ; is.array (NA) ; is.array (NaN) ; is.array (Inf) ; is.array (5i) ; is.array (1 + 3i) ; is.array (x = -1) ; is.array ("x" = -1) ; is.array (y = -1)
is.vector <- function (x, mode = "any") .Internal (is.vector (x, mode)) ; is.vector (1) ; is.vector (NULL) ; is.vector ("1") ; is.vector (1L) ; is.vector (NA) ; is.vector (NaN) ; is.vector (Inf) ; is.vector (5i) ; is.vector (1 + 3i) ; is.vector (x = -1) ; is.vector ("x" = -1) ; is.vector (y = -1)
is.single (1) ; is.single (NULL) ; is.single ("1") ; is.single (1L) ; is.single (NA) ; is.single (NaN) ; is.single (Inf) ; is.single (5i) ; is.single (1 + 3i) ; is.single (x = -1) ; is.single ("x" = -1) ; is.single (y = -1)
is.raw (1) ; is.raw (NULL) ; is.raw ("1") ; is.raw (1L) ; is.raw (NA) ; is.raw (NaN) ; is.raw (Inf) ; is.raw (5i) ; is.raw (1 + 3i) ; is.raw (x = -1) ; is.raw ("x" = -1) ; is.raw (y = -1)
is.na (1) ; is.na (NULL) ; is.na ("1") ; is.na (1L) ; is.na (NA) ; is.na (NA_character_) ; is.na (NA_complex_) ; is.na (NA_real_) ; is.na (NA_integer_) ; is.na (NaN) ; is.na (Inf) ; is.na (x = -1) ; is.na ("x" = -1) ; is.na (y = -1)

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
a <- 1 + ''
a <- 1 + .Internal
a <- "" + 2
a <- '' + 2L
a <- "" + TRUE
a <- '' + .Internal
a <- FALSE + 2 ; a ; .Internal (typeof (a))
a <- FALSE + 2L ; a ; .Internal (typeof (a))
a <- FALSE + ""
a <- FALSE + .Internal
1 + 2i ; 1L + 2i ; (1L + 2i) - 2i ; (1L + 2i) - 2i == 1L
NaN + 3i ; NA + 3i ; Inf + 3i ; 3i + 1/0 ; NaN + 0i ; NA + 0i
(1 + 1i) * NaN ; 1i * NaN ; 1 * NaN ; 1i * c (NaN, 0i)[1] ; (1 + 1i) * c (NaN, 0i)[1]
(1 + 1i) * NA ; 1i * NA ; 1 * NA ; 1i * c (NA, 0i)[1] ; (1 + 1i) * c (NA, 0i)[1]
"" == '' ; c ('1', "1")
1. == 1 ; 1.0 == 1 ; 1.00 == 1 ; 1 == 1.000 ; 0.5 == .5 ; 0.5 == 0.50 ; 0.5 == .500
0.99999999999999999999 == 1 ; 0.99999999999999999999999999999999 == 1.
2 == 2L ; -0 == 0 ; -0 == 0L ; 0. == -0L ; 1 == TRUE ; 1L == TRUE ; 0 == FALSE ; 0L == FALSE
"FALSE" == FALSE ; 'False' == FALSE ; "false" == FALSE ; 'F' == FALSE ; "f" == FALSE ; 'fALSE' == FALSE
"TRUE" == TRUE ; "True" == TRUE ; "true" == TRUE ; "T" == TRUE ; "t" == TRUE ; "tRUE" == TRUE
NA == NA ; NaN == NaN ; NA == NaN ; NaN == 0/0 ; NaN == -0/0 ; NaN == 1 + 0/0 ; NaN == 1 + NaN
NA_integer_ == NA ; NA_character_ == NA ; NA_complex_ == NA ; NA_real_ == NA
NA_complex_ == NA_complex_ ; NA_complex_ = NA_integer_ ; NA_complex_ = NA_character_ ; NA_complex_ = NA_real_
NA_integer_ == NA_complex_ ; NA_integer_ = NA_integer_ ; NA_integer_ = NA_character_ ; NA_integer_ = NA_real_
NA_character_ == NA_complex_ ; NA_character_ = NA_integer_ ; NA_character_ = NA_character_ ; NA_character_ = NA_real_
NA_real_ == NA_complex_ ; NA_real_ = NA_integer_ ; NA_real_ = NA_character_ ; NA_real_ = NA_real_
NULL == 0 ; NULL == NA ; NULL == NaN ; NULL == FALSE ; NULL == TRUE
0 == -0 ; 0L == -0L ; 1/Inf == 0 ; -1/Inf == 0 ; NaN == Inf - Inf
.Internal == .Internal
c (1, 1L) ; c (1, NULL) ; c (1, TRUE) ; c (1, "a") ; c (1, NA) ; c (1, NaN) ; c (1, 3i)
c (1L, 1L) ; c (1L, NULL) ; c (1L, TRUE) ; c (1L, 'a') ; c (1L, NA) ; c (1L, NaN) ; c (1L, 3i)
c (NULL, 1L) ; c (NULL, NULL) ; c (NULL, TRUE) ; c (NULL, "a") ; c (NULL, NA) ; c (NULL, NaN) ; c (NULL, 3i)
c (TRUE, 1L) ; c (TRUE, NULL) ; c (TRUE, TRUE) ; c (TRUE, 'a') ; c (TRUE, NA) ; c (TRUE, NaN) ; c (TRUE, 3i)
c ("b", 1L) ; c ('b', NULL) ; c ("b", TRUE) ; c ('b', "a") ; c ("b", NA) ; c ('b', NaN) ; c ("b", 3i)
c (NA, 1L) ; c (NA, NULL) ; c (NA, TRUE) ; c (NA, "a") ; c (NA, NA) ; c (NA, NaN) ; c (NA, 3i)
c (NaN, 1L) ; c (NaN, NULL) ; c (NaN, TRUE) ; c (NaN, "a") ; c (NaN, NA) ; c (NaN, NaN) ; c (NaN, 3i)
c (4i, 1L) ; c (4i, NULL) ; c (4i, TRUE) ; c (4i, "a") ; c (4i, NA) ; c (4i, NaN) ; c (4i, 3i)
c (1, TRUE, 'a') ; c (c (1, TRUE), "a") ; c (1, c (TRUE, 'a'))
c (1) ; c (1L) ; c (1i) ; c (TRUE) ; c ("a") ; c (NA) ; c (NaN) ; c (Inf)
c () ; c (NULL) ; c (NULL, NULL, NULL, NA, NULL, NULL, NULL)
c (NA, 1) ; c (NA_character_, 1) ; c (NA_complex_, 1) ; c (NA_character_, NA_complex_, 1)
c (x = 1) ; c (y = 1)
c (1:10) ; c (c) ; c (function (x) x)
list (c ()) ; list (c (1)) ; list (c (1, 2), c ("1", "2"))
list () ; c (list ()) ; c (list (1)) ; c (list (1, 2), list ("1", "2")) ; c (list (1, TRUE, "a")) ; c (list (1, TRUE, "a"), list (), list (NA), list (FALSE))
list (1, 2) ; list (list (1, 2), list (3, 4)) ; list (NULL) ; list (NA) ; list (NaN) ; list (FALSE) ; list (NULL, NA, NaN, FALSE) ; list (NULL, NA, NaN, FALSE, list (list (list (list ()), 9)), '', list)
c (1, TRUE) ; c (1, TRUE, list ()) ; c (1, TRUE, "a", NULL, list (), NA, list (FALSE), function (x) x)
NULL == list () ; NULL == c () ; list () == list () ; list () == c () ; list () == 1 ; list () == NA ; list () == NaN ; list == list
list (1) == c (1) ; list (1) == 1 ; list (1) == c (1L) ; list (1) == c (1i) ; list (1L) == c (1i) ; list (1) == list (1)
NA == "NA" ; list (NA) == NA ; list (NA) == "NA" ; list ("NA") == "NA" ; list ("NA") == NA
list (1, TRUE) == c ("1", "TRUE") ; list (TRUE, TRUE) == c ("true", "T") ; list (TRUE, TRUE) == c (1) ; list (TRUE, "") == c (1) ; list ("") == c (1) ; list (" ") == c (1) ; list (1, TRUE) == c (TRUE, "")
(list (1, 2, 3)) [[2]] ; (1:3) [[2]] ; list (1) [[2]]
list (a = 3, b = 5) $ a ; list (a = 3, b = 5) $ c ; list (ab = 3, b = 4) $ a ; list (ab = 3, abc = 4) $ a ; list (ab = 3, abc = 4) $ ab
1 == 1i ; 1 == 1 + 0i
-0:0 ; 1:1 ; 1:-1 ; -1:1 ; 1L:-1 ; -1:1L ; 1:"1" ; 1:" "
-10:10 ; -(10:10) ; 1:""
1:NA
1:NaN
1:Inf
TRUE:2 ; 1i:3 ; NULL:1
-0.5:0.5 ; -0.5:10 ; 0.99999999999999999:1.99999999999999999 ; 0.99999999999999999:4
(function () 1):3
.Internal:3
1 > 2 ; 1 < 2 ; 1 <= 2 ; 1 >= 2 ; 1 == 2 ; 1 != 2
1L > 2 ; 1L < 2 ; 1L <= 2 ; 1L >= 2 ; 1L == 2 ; 1L != 2
1 > 2L ; 1 < 2L ; 1 <= 2L ; 1 >= 2L ; 1 == 2L ; 1 != 2L
1L > 2L ; 1L < 2L ; 1L <= 2L ; 1L >= 2L ; 1L == 2L ; 1L != 2L
TRUE > 2 ; TRUE < 2 ; TRUE <= 2 ; TRUE >= 2 ; TRUE == 2 ; TRUE != 2
0 > FALSE ; 0 < FALSE ; 0 <= FALSE ; 0 >= FALSE ; 0 == FALSE ; 0 != FALSE
TRUE > FALSE ; TRUE < FALSE ; TRUE <= FALSE ; TRUE >= FALSE ; TRUE == FALSE ; TRUE != FALSE
"1" > 2 ; '1' < 2 ; "1" <= 2 ; '1' >= 2 ; "1" == 2 ; "1" != 2
1 > '2' ; 1 < "2" ; 1 <= '2' ; 1 >= "2" ; 1 == '2' ; 1 != '2'
'1' > "2" ; "1" < "2" ; "1" <= '2' ; '1' >= '2' ; "1" == "2" ; '1' != "2"
"1" > 'TRUE' ; "1" < "TRUE" ; '1' <= "TRUE" ; '1' >= 'TRUE' ; "1" == "TRUE" ; "1" != 'TRUE'
1 > NA ; 1 < NA ; 1 <= NA ; 1 >= NA ; 1 == NA ; 1 != NA
NA > NA ; NA < NA ; NA <= NA ; NA >= NA ; NA == NA ; NA != NA
1 > NaN ; 1 < NaN ; 1 <= NaN ; 1 >= NaN ; 1 == NaN ; 1 != NaN
NaN > NaN ; NaN < NaN ; NaN <= NaN ; NaN >= NaN ; NaN == NaN ; NaN != NaN
1 > "" ; 1 < '' ; 1 <= "" ; 1 >= '' ; 1 == "" ; 1 != ""
0 == 0i ; 0L == 0i ; 0 == 0L ; FALSE == TRUE - TRUE ; FALSE != TRUE - TRUE
1:5 > 5:1 ; 1:5 < 5:1 ; 1:5 >= 5:1 ; 1:5 <= 5:1 ; 1:5 == 5:1 ; 1:5 != 5:1
1 %% 2 ; 1 %% 1 ; 1 %% 0 ; 1 %% FALSE ; 1 %% TRUE
0 %% 2 ; 0 %% 1 ; 0 %% 0 ; 0 %% FALSE ; 0 %% TRUE
-1 %% 2 ; -1 %% 1 ; -1 %% 3 ; -1 %% 0 ; -1 %% FALSE ; -1 %% TRUE
5.5 %% 4 ; -5.5 %% 4
NA %% 1 ; NA %% 0 ; NaN %% 1 ; NaN %% 0 ; 1 %% NA ; 1 %% NaN ; 0 %% NA ; 0 %% NaN
TRUE %% 2 ; TRUE %% 1 ; TRUE %% 0 ; TRUE %% FALSE ; TRUE %% TRUE
FALSE %% 2 ; FALSE %% 1 ; FALSE %% 0 ; FALSE %% FALSE ; FALSE %% TRUE
0i %% 3
0i %% 0
0i %% 3i
7 %% 2:4 ; -10:10 %% 3 ; -10:10 %% NULL ; NULL %% 2 ; -10:10 %% 2:4 ; -10:10 %% 2:5
0 + 0i ; 0 - 0i ; -0 - 0i ; -0 + 0i
1 / 0 ; 1 / -0 ; 1 / 0i ; 1 / -0i ; 1 / 0 * 1i ; 1 / 0 * i
Inf + Inf ; Inf - Inf ; -Inf + Inf ; -Inf - Inf ; 1 / 0 + Inf ; 1 / 0 - Inf ; 1 / -0 + Inf ; 1 / -0 - Inf ; 1 / 0 + 1 / -0 ; 1 / 0 + 1 / 0

# Tests about assignments.
x <- y <- 2 ; x ; y
x <- 2 -> y ; x ; y
x <- 2 ; x <- x <- x + 1 ; x
x <- 2 ; x <- x + 1 -> x ; x
x <- 2 ; y <- x <- x + 1 ; y ; x
x <- 2 ; y <- x + 1 -> x ; y ; x
x <- 1 ; y <- x ; x <- 2 ; y
(x <- 1) + (x <- 2) ; x
x <- 0 ; (x <- x + 1) + (x <- x + 1) ; x
x <- 1 ; x <- NULL ; x ; x <- NA ; x ; x <- NaN ; x
x <- 1 ; "x" <- 2 ; x ; 'x' <- 3 ; x
y <- 1 ; x <- 'y' ; x <- 2 ; y ; x
x <- 1 ; y <- x ; x <- 2 ; y ; x
c ('a', "b") <- 1 ;
"<-" (x, 1) ; x
T <- 1 ; F <- 2 ; T ; F ; TRUE <- 1
NA <- 1
"NA" <- 1 ; NA
"TRUE" <- 1 ; "FALSE" <- 2 ; TRUE ; FALSE
f <- function (x) x <- 1 ; x <- 2 ; f (3) ; x
x <- 2 ; f <- function (x) x <- 1 ; x ; f (3) ; x
f <- function (x) function (y) x <- 1 ; x <- 2 ; f (3) (4) ; x
x <<- y <<- 2 ; x ; y
x <<- 2 ->> y ; x ; y
x <<- 2 ; x <<- x <<- x + 1 ; x
x <<- 2 ; x <<- x + 1 ->> x ; x
x <<- 2 ; y <<- x <<- x + 1 ; y ; x
x <<- 2 ; y <<- x + 1 ->> x ; y ; x
x <<- 1 ; y <<- x ; x <<- 2 ; y
(x <<- 1) + (x <<- 2) ; x
x <<- 0 ; (x <<- x + 1) + (x <<- x + 1) ; x
x <<- 1 ; x <<- NULL ; x ; x <<- NA ; x ; x <<- NaN ; x
x <<- 1 ; "x" <<- 2 ; x ; 'x' <<- 3 ; x
y <<- 1 ; x <<- 'y' ; x <<- 2 ; y ; x
x <<- 1 ; y <<- x ; x <<- 2 ; y ; x
c ('a', "b") <<- 1 ;
"<<-" (x, 1) ; x
T <<- 1 ; F <<- 2 ; T ; F ; TRUE <<- 1
NA <<- 1
"NA" <<- 1 ; NA
"TRUE" <<- 1 ; "FALSE" <<- 2 ; TRUE ; FALSE
f <<- function (x) x <<- 1 ; x <<- 2 ; f (3) ; x
f <<- function (x) function (y) x <<- 1 ; x <<- 2 ; f (3) (4) ; x
f <- function (x) x <<- 1 ; x <- 2 ; f (3) ; x
f <- function (x) function (y) x <<- 1 ; x <- 2 ; f (3) (4) ; x
x = y = 2 ; x ; y
x = 2 ; x = x = x + 1 ; x
x = 2 ; y = x = x + 1 ; y ; x
x = 0 ; (x = x + 1) + (x = x + 1) ; x
x = 1 ; x = NULL ; x ; x = NA ; x ; x = NaN ; x
x = 1 ; "x" = 2 ; x ; 'x' = 3 ; x
y = 1 ; x = 'y' ; x = 2 ; y ; x
x = 1 ; y = x ; x = 2 ; y ; x
c ('a', "b") = 1 ;
"=" (x, 1) ; x
T = 1 ; F = 2 ; T ; F ; TRUE = 1
NA = 1
"NA" = 1 ; NA
"TRUE" = 1 ; "FALSE" = 2 ; TRUE ; FALSE
f = function (x) x = 1 ; x = 2 ; f (3) ; x
f = function (x) function (y) x = 1 ; x = 2 ; f (3) (4) ; x
a <- b = 2
a = b <- 1 ; a ; b
"<-<-" <- function (a, b, value) c (a, b, value) ; a <- b = 2 ; a ; b
f <- function (x) { g <- function (y) x <- 1 ; g () ; x } ; x <- 2 ; f (3) ; x
f <- function (x) { g <- function (y) x = 1 ; g () ; x } ; x <- 2 ; f (3) ; x
f <- function (x) { g <- function (y) x <<- 1 ; g () ; x } ; x <- 2 ; f (3) ; x
f <- function (x) { g <- function (y) x <- 1 ; g () ; x } ; x <- 2 ; f (x) ; x
f <- function (x) { g <- function (y) x = 1 ; g () ; x } ; x <- 2 ; f (x) ; x
f <- function (x) { g <- function (y) x <<- 1 ; g () ; x } ; x <- 2 ; f (x) ; x
f <- function () { g <- function (y) x <- 1 ; g () ; x } ; x <- 2 ; f () ; x
f <- function () { g <- function (y) x = 1 ; g () ; x } ; x <- 2 ; f () ; x
f <- function () { g <- function (y) x <<- 1 ; g () ; x } ; x <- 2 ; f () ; x
``
a <- 1 ; `a` ; `a` <- 2 ; a ; `a` ; ` ` <- 3 ; ` ` ; `\`` <- 4 ; `\`` ; `'` <- 5 ; `'` ; `\'` ; `"` <- 6 ; `"` ; `\"`
1 -> a ; `a` ; 2 -> `a` ; a ; `a` ; 3 -> ` ` ; ` ` ; 4 -> `\`` ; `\`` ; 5 -> `'` ; `'` ; `\'` ; 6 -> `"` ; `"` ; `\"`
`` <- 1
2 -> ``
a = 1 ; `a` ; `a` = 2 ; a ; `a` ; ` ` = 3 ; ` ` ; `\`` = 4 ; `\`` ; `'` = 5 ; `'` ; `\'` ; `"` = 6 ; `"` ; `\"`
`` = 1
a <<- 1 ; `a` ; `a` <<- 2 ; a ; `a` ; ` ` <<- 3 ; ` ` ; `\`` <<- 4 ; `\`` ; `'` <<- 5 ; `'` ; `\'` ; `"` <<- 6 ; `"` ; `\"`
`` <<- 1
1 ->> a ; `a` ; 2 ->> `a` ; a ; `a` ; 3 ->> ` ` ; ` ` ; 4 ->> `\`` ; `\`` ; 5 ->> `'` ; `'` ; `\'` ; 6 ->> `"` ; `"` ; `\"`
2 ->> ``

# Tests about the modification of primitive operators.
"if" <- function (x, y, z) x + y + z ; if (1) 2 else 3
'if' <- function (x) -x ; if (1) 2 else 3
"(" <- function (x) 2 * x ; (2)
'(' <- function () 1 ; (2)
"{" <- function (x) 2 * x ; {2}
'<-' <- function (x, y) x + y ; 1 <- 2 ; 3 -> 4 ; 5 <- 6 -> 7
"<<-" <- function (x, y) x + y ; 1 <<- 2 ; 3 ->> 4 ; 5 <<- 6 ->> 7
'function' <- function (x, y, z) y ; function (x) 2
"+" <- function (x, y) x - y ; 1 + 2
'1' <- 2 ; "1L" <- 2L ; 1 ; 1L
"1" <- function (x) x ; 1 (2)
"NULL" <- 1 ; NULL ; NULL <- 1

# Tests about attributes and targetted assignments.
attr (1, 1)
attr (1, "") ; attr (a, NA_character_) ; attr (a, NA)
attr (1, NULL)
attr (1, c ("f", "g"))
attr (1, character ())
attr (1, c ())
a <- 1 ; attr (a, 2) <- 3
a <- 1 ; attr (a, "f", TRUE) <- 3
a <- 1 ; attr (a, "f", FALSE) <- 3
a <- 1 ; attr (a, "f", "g") <- 3
a <- 1 ; attr (a, "f") <- 3 ; attr (a, "f") ; attr (a, "f", 4) ; attr (a, "f") ; a
a <<- 1 ; attr (a, 2) <<- 3
a <<- 1 ; attr (a, "f", TRUE) <<- 3
a <<- 1 ; attr (a, "f", FALSE) <<- 3
a <<- 1 ; attr (a, "f", "g") <<- 3
a <<- 1 ; attr (a, "f") <<- 3 ; attr (a, "f") ; attr (a, "f", 4) ; attr (a, "f") ; a
a = 1 ; attr (a, 2) = 3
a = 1 ; attr (a, "f", TRUE) = 3
a = 1 ; attr (a, "f", FALSE) = 3
a = 1 ; attr (a, "f", "g") = 3
a = 1 ; attr (a, "f") = 3 ; attr (a, "f") ; attr (a, "f", 4) ; attr (a, "f") ; a
a <- 1:10 ; b <- 20:25 ; attr (a, "c") <- "a" ; attr (a, "a") <- "a" ; attr (b, "c") <- "b" ; attr (b, "b") <- "b" ; ab <- a + b ; attr (ab, "a") ; attr (ab, "b") ; attr (ab, "c") ; ab
a <- 1:10 ; b <- 20:29 ; attr (a, "c") <- "a" ; attr (a, "a") <- "a" ; attr (b, "c") <- "b" ; attr (b, "b") <- "b" ; ab <- a + b ; attr (ab, "a") ; attr (ab, "b") ; attr (ab, "c") ; ab
a <<- 1:10 ; b <<- 20:25 ; attr (a, "c") <<- "a" ; attr (a, "a") <<- "a" ; attr (b, "c") <<- "b" ; attr (b, "b") <<- "b" ; ab <<- a + b ; attr (ab, "a") ; attr (ab, "b") ; attr (ab, "c") ; ab
a <<- 1:10 ; b <<- 20:29 ; attr (a, "c") <<- "a" ; attr (a, "a") <<- "a" ; attr (b, "c") <<- "b" ; attr (b, "b") <<- "b" ; ab <<- a + b ; attr (ab, "a") ; attr (ab, "b") ; attr (ab, "c") ; ab
a = 1:10 ; b = 20:25 ; attr (a, "c") = "a" ; attr (a, "a") = "a" ; attr (b, "c") = "b" ; attr (b, "b") = "b" ; ab = a + b ; attr (ab, "a") ; attr (ab, "b") ; attr (ab, "c") ; ab
a = 1:10 ; b = 20:29 ; attr (a, "c") = "a" ; attr (a, "a") = "a" ; attr (b, "c") = "b" ; attr (b, "b") = "b" ; ab = a + b ; attr (ab, "a") ; attr (ab, "b") ; attr (ab, "c") ; ab
attr (x, "f")
attr (x, "f") <- 1
attr (x, "f") = 1
attr (x, "f") <<- 1
attr (is.na, "f") <- 1 ; is.na ; is.na (9)
a <- 1 ; attr (a, "f") <- NULL ; a ; attr (a, "f") ; attr (a, "f") <- 1 ; a ; attr (a, "f")
a <- NA_character_ ; attr (a, "f") = -1 ; attr (a, "g") <- -1 ; attr (a, "h") <<- -1
a <- 9 ; attr (a, "f") <- 8 ; a <- 9 ; attr (a, "f") ; f
attr (1, "a") ; attr (1, "a") <- 4 ; attr (1, "a") ; 1
b <- attr (a, "f") <- a <- 2 ; 2 ; a ; b ; attr (a, "f")
b <- attr (a, "f") <- 2 -> a -> c ; a ; b ; c ; attr (a, "f") ; attr (c, "f")
a <- 1 ; attr (a, "f") <- 2 ; a ; attr (a, "f") ; a + 1 ; attr (a + 1, "f") ; 1 + a ; attr (1 + a, "f")
a <- 1:5 ; attr (a, "f") <- 2 ; a ; attr (a, "f") ; a + 1 ; attr (a + 1, "f") ; 1 + a ; attr (1 + a, "f")
a <- 1 ; attr (attr (a, "f"), "g") <- 4
a <- 1 ; attr (a, "f") <- 2 ; attr (attr (a, "f"), "g") <- 3 ; attr (attr (attr (a, "f"), "g"), "h") <- 4 ; attr (a, "f") ; attr (attr (a, "f"), "g") ; attr (attr (attr (a, "f"), "g"), "h") ; a
a <- 1 ; attr (a, "f") <- 2 ; attr (attr (a, "f"), "g") <- 3 ; attr (attr (attr (a, "f"), "g"), "f") <- 4 ; attr (a, "f") ; attr (attr (a, "f"), "g") ; attr (attr (attr (a, "f"), "g"), "f") ; a
a <- 1 ; attr (a, "f") <- 2 ; attr (attr (a, "f"), "g") <- 3 ; b <- attr (attr (a, "f"), "g") ; attr (b, "f") <- 4 ; attr (a, "f") ; attr (attr (a, "f"), "g") ; b ; attr (b, "f") ; a
1 -> a ; 2 -> attr (a, "f") ; 3 -> attr (attr (a, "f"), "g") ; attr (attr (a, "f"), "g") -> b ; 4 -> attr (b, "f") ; attr (a, "f") ; attr (attr (a, "f"), "g") ; b ; attr (b, "f") ; a
f <- "g" ; a <- 1 ; b <- 2 ; attr (a, f) <- 3 ; attr (b, f) <- 4 ; attr (a + b, f) ; attr (a + b, "g") ; attr (a + b, "f")
f <- "g" ; a <- 1 ; b <- 2 ; attr (a, f) <- 3 ; attr (b, f) <- 4 ; attr (a - b, f) ; attr (a * b, f) ; attr (a / b, f) ; attr (a < b, f) ; attr (a > b, f) ; attr (a <= b, f) ; attr (a >= b, f) ; attr (a == b, f) ; attr (a != b, f)
f <- "g" ; a <- 1L ; b <- 2L ; attr (a, f) <- 3L ; attr (b, f) <- 4L ; attr (a - b, f) ; attr (a * b, f) ; attr (a / b, f) ; attr (a < b, f) ; attr (a > b, f) ; attr (a <= b, f) ; attr (a >= b, f) ; attr (a == b, f) ; attr (a != b, f)
a <- 1 ; b <- 2 ; attr (a, "x") <- 3 ; attr (b, "y") <- 4 ; attr (a + b, "x") ; attr (a + b, "y")
a <- function (x) x ; attr (a, "f") <- 2 ; a ; attr (a, "f") ; attr (a, "f") <- function (x) x ; a ; attr (a, "f") ; attr (a, "f") <- NULL ; a ; attr (a, "f") ; attr (a, "f") <- NA ; a ; attr (a, "f")
a <- 1L ; attr (a, "f") <- 2 ; a ; attr (a, "f") ; attr (a, "f") <- function (x) x ; a ; attr (a, "f") ; attr (a, "f") <- NULL ; a ; attr (a, "f") ; attr (a, "f") <- NA ; a ; attr (a, "f")
a <- 2i ; attr (a, "f") <- 2 ; a ; attr (a, "f") ; attr (a, "f") <- function (x) x ; a ; attr (a, "f") ; attr (a, "f") <- NULL ; a ; attr (a, "f") ; attr (a, "f") <- NA ; a ; attr (a, "f")
a <- NaN ; attr (a, "f") <- 2 ; a ; attr (a, "f") ; attr (a, "f") <- function (x) x ; a ; attr (a, "f") ; attr (a, "f") <- NULL ; a ; attr (a, "f") ; attr (a, "f") <- NA ; a ; attr (a, "f")
a <- NA ; attr (a, "f") <- 2 ; a ; attr (a, "f") ; attr (a, "f") <- function (x) x ; a ; attr (a, "f") ; attr (a, "f") <- NULL ; a ; attr (a, "f") ; attr (a, "f") <- NA ; a ; attr (a, "f")
a <- "" ; attr (a, "f") <- 2 ; a ; attr (a, "f") ; attr (a, "f") <- function (x) x ; a ; attr (a, "f") ; attr (a, "f") <- NULL ; a ; attr (a, "f") ; attr (a, "f") <- NA ; a ; attr (a, "f")
a <- "" ; attr (a, "") <- 2 ; a ; attr (a, "") ; attr (a, "") <- function (x) x ; a ; attr (a, "") ; attr (a, "") <- NULL ; a ; attr (a, "") ; attr (a, "") <- NA ; a ; attr (a, "")
a <- NULL ; attr (a, "f") <- 2
a <- -10:10 ; a ; a [3] <- 9 ; a ; a [6:9] ; a > 0 ; a = 0 ; a [a = 0] <- 8 ; a ; a [a < 1] <- 7 ; a ; a [-2] ; a [-4:-7] ; a []
a <- -10:10 ; attr (a, "x") <- 9 ; attr (a, "x") ; attr (a [1], "x") ; attr (a [-1], "x") ; attr (a [1], "y") <- 8 ; a ; attr (a [1], "y") ; attr (a, "y") ; b <- a [1] ; attr (b, "z") <- 7 ; attr (b, "z") ; attr (a [1], "z")
a <- -10:10 ; a [c (TRUE, FALSE, TRUE)] ; a [80:90] ; a [-9:0] ; a [c ("x", "y")] ; a [NA] ; a [NaN] ; a [c (TRUE, FALSE, NA)] ; a ["TRUE"] ; a [0] ; a [a]
a <- 1 ; attr (a, "abc") <- 2 ; attr (a, "a") ; attr (a, "a") <- 3 ; attr (a, "a") ; attr (a, "ab") ; attr (a, "abc") ; attr (a, "ab") <- 4 ; attr (a, "a") ; attr (a, "ab") ; attr (a, "abc")
a <- 1 ; attr (a, "abc") <- 2 ; attr (a, "ab") <- 3 ; attr (a, "a")
a <- 1 ; attr (a, "abc") <- 2 ; attr (a, "ab") <- 3 ; attr (a, "a", TRUE) ; attr (a, "ab", TRUE) ; attr (a, "abc", TRUE) ; attr (a, "a", FALSE) ; attr (a, "ab", FALSE) ; attr (a, "abc", FALSE)
a <- 1 ; attr (a, "abc") <- 2 ; attr (a, "ab") <- 3 ; attr (a, "a", "") ; attr (a, "ab", "") ; attr (a, "abc", "") ; attr (a, "a", 1i) ; attr (a, "ab", 1i) ; attr (a, "abc", 1i)
a <- 1 ; attr (a, "abc") <- 2 ; attr (a, "a") ; attr (a, "a", TRUE) ; attr (a, "a", FALSE) ; attr (a, "a", FALSE) <- 3
a <- 1 ; attr (a, "f", TRUE, FALSE)
"attr<-" <- function (x, y, value) x <- value + 1 ; a <- 1 ; attr (a, "f") <- 2 ; a ; attr (a, "f")
"attr=" <- function (x, y, value) x <- value + 1 ; a <- 1 ; attr (a, "f") <- 2 ; a ; attr (a, "f")
"attr<-" <- function (x, y, value) x <- value + 1 ; a <- 1 ; 2 -> attr (a, "f") ; a ; attr (a, "f")
attr (attr, "f") <- 1 ; attr ; attr (attr, "f")
attr (1, "a") ; attr (1, "a") <<- 4
a <<- 1 ; attr (a, "f") <<- 2 ; a ; attr (a, "f") ; a + 1 ; attr (a + 1, "f") ; 1 + a ; attr (1 + a, "f")
a <<- 1:5 ; attr (a, "f") <<- 2 ; a ; attr (a, "f") ; a + 1 ; attr (a + 1, "f") ; 1 + a ; attr (1 + a, "f")
a <<- 1 ; attr (attr (a, "f"), "g") <<- 4
a <<- 1 ; attr (a, "f") <<- 2 ; attr (attr (a, "f"), "g") <<- 3 ; attr (attr (attr (a, "f"), "g"), "f") <<- 4 ; attr (a, "f") ; attr (attr (a, "f"), "g") ; attr (attr (attr (a, "f"), "g"), "f") ; a
a <<- 1 ; attr (a, "f") <<- 2 ; attr (attr (a, "f"), "g") <<- 3 ; attr (attr (attr (a, "f"), "g"), "f") <<- 4 ; attr (a, "f") ; attr (attr (a, "f"), "g") ; attr (attr (attr (a, "f"), "g"), "f") ; a
a <<- 1 ; attr (a, "f") <<- 2 ; attr (attr (a, "f"), "g") <<- 3 ; b <<- attr (attr (a, "f"), "g") ; attr (b, "f") <<- 4 ; attr (a, "f") ; attr (attr (a, "f"), "g") ; b ; attr (b, "f") ; a
1 ->> a ; 2 ->> attr (a, "f") ; 3 ->> attr (attr (a, "f"), "g") ; attr (attr (a, "f"), "g") ->> b ; 4 ->> attr (b, "f") ; attr (a, "f") ; attr (attr (a, "f"), "g") ; b ; attr (b, "f") ; a
f <<- "g" ; a <<- 1 ; b <<- 2 ; attr (a, f) <<- 2 ; attr (b, f) <<- 3 ; attr (a + b, f) ; attr (a + b, "g") ; attr (a + b, "f")
f <<- "g" ; a <<- 1 ; b <<- 2 ; attr (a, f) <<- 2 ; attr (b, f) <<- 3 ; attr (a - b, f) ; attr (a * b, f) ; attr (a / b, f) ; attr (a < b, f) ; attr (a > b, f) ; attr (a <= b, f) ; attr (a >= b, f) ; attr (a == b, f) ; attr (a != b, f)
a <<- 1 ; b <<- 2 ; attr (a, "x") <<- 3 ; attr (b, "y") <<- 4 ; attr (a + b, "x") ; attr (a + b, "y")
a <<- function (x) x ; attr (a, "f") <<- 2 ; a ; attr (a, "f") ; attr (a, "f") <<- function (x) x ; a ; attr (a, "f") ; attr (a, "f") <<- NULL ; a ; attr (a, "f") ; attr (a, "f") <<- NA ; a ; attr (a, "f")
a <<- 1L ; attr (a, "f") <<- 2 ; a ; attr (a, "f") ; attr (a, "f") <<- function (x) x ; a ; attr (a, "f") ; attr (a, "f") <<- NULL ; a ; attr (a, "f") ; attr (a, "f") <<- NA ; a ; attr (a, "f")
a <<- 2i ; attr (a, "f") <<- 2 ; a ; attr (a, "f") ; attr (a, "f") <<- function (x) x ; a ; attr (a, "f") ; attr (a, "f") <<- NULL ; a ; attr (a, "f") ; attr (a, "f") <<- NA ; a ; attr (a, "f")
a <<- NaN ; attr (a, "f") <<- 2 ; a ; attr (a, "f") ; attr (a, "f") <<- function (x) x ; a ; attr (a, "f") ; attr (a, "f") <<- NULL ; a ; attr (a, "f") ; attr (a, "f") <<- NA ; a ; attr (a, "f")
a <<- NA ; attr (a, "f") <<- 2 ; a ; attr (a, "f") ; attr (a, "f") <<- function (x) x ; a ; attr (a, "f") ; attr (a, "f") <<- NULL ; a ; attr (a, "f") ; attr (a, "f") <<- NA ; a ; attr (a, "f")
a <<- "" ; attr (a, "f") <<- 2 ; a ; attr (a, "f") ; attr (a, "f") <<- function (x) x ; a ; attr (a, "f") ; attr (a, "f") <<- NULL ; a ; attr (a, "f") ; attr (a, "f") <<- NA ; a ; attr (a, "f")
a <<- "" ; attr (a, "") <<- 2 ; a ; attr (a, "") ; attr (a, "") <<- function (x) x ; a ; attr (a, "") ; attr (a, "") <<- NULL ; a ; attr (a, "") ; attr (a, "") <<- NA ; a ; attr (a, "")
a <<- NULL ; attr (a, "f") <<- 2
a <<- -10:10 ; a ; a [3] <<- 9 ; a ; a [6:9] ; a > 0 ; a <<- 0 ; a [a <<- 0] <<- 8 ; a ; a [a < 1] <<- 7 ; a ; a [-2] ; a [-4:-7]
a <<- -10:10 ; attr (a, "x") <<- 9 ; attr (a, "x") ; attr (a [1], "x") ; attr (a [-1], "x") ; attr (a [1], "y") <<- 8 ; a ; attr (a [1], "y") ; attr (a, "y") ; b <<- a [1] ; attr (b, "z") <<- 7 ; attr (b, "z") ; attr (a [1], "z")
a <<- -10:10 ; a [c (TRUE, FALSE, TRUE)] ; a [80:90] ; a [-9:0] ; a [c ("x", "y")] ; a [NA] ; a [NaN] ; a [c (TRUE, FALSE, NA)] ; a ["TRUE"] ; a [0] ; a [a]
a <<- 1 ; attr (a, "abc") <<- 2 ; attr (a, "a") ; attr (a, "a") <<- 3 ; attr (a, "a") ; attr (a, "ab") ; attr (a, "abc") ; attr (a, "ab") <<- 4 ; attr (a, "a") ; attr (a, "ab") ; attr (a, "abc")
a <<- 1 ; attr (a, "abc") <<- 2 ; attr (a, "ab") <<- 3 ; attr (a, "a")
a <<- 1 ; attr (a, "abc") <<- 2 ; attr (a, "ab") <<- 3 ; attr (a, "a", TRUE) ; attr (a, "ab", TRUE) ; attr (a, "abc", TRUE) ; attr (a, "a", FALSE) ; attr (a, "ab", FALSE) ; attr (a, "abc", FALSE)
a <<- 1 ; attr (a, "abc") <<- 2 ; attr (a, "ab") <<- 3 ; attr (a, "a", "") ; attr (a, "ab", "") ; attr (a, "abc", "") ; attr (a, "a", 1i) ; attr (a, "ab", 1i) ; attr (a, "abc", 1i)
a <<- 1 ; attr (a, "abc") <<- 2 ; attr (a, "a") ; attr (a, "a", TRUE) ; attr (a, "a", FALSE) ; attr (a, "a", FALSE) <<- 3
a <<- 1 ; attr (a, "f", TRUE, FALSE)
"attr<<-" <<- function (x, y, value) x <<- value + 1 ; a <<- 1 ; attr (a, "f") <<- 2 ; a ; attr (a, "f")
"attr<-" <<- function (x, y, value) x <<- value + 1 ; a <<- 1 ; attr (a, "f") <<- 2 ; a ; attr (a, "f")
"attr<-" <- function (x, y, value) x <- value + 1 ; a <- 1 ; 2 ->> attr (a, "f") ; a ; attr (a, "f")
"attr=" <<- function (x, y, value) x <<- value + 1 ; a <<- 1 ; attr (a, "f") <<- 2 ; a ; attr (a, "f")
attr (attr, "f") <<- 1 ; attr ; attr (attr, "f")
attr (1, "a") ; attr (1, "a") = 4
a = 1 ; attr (a, "f") = 2 ; a ; attr (a, "f") ; a + 1 ; attr (a + 1, "f") ; 1 + a ; attr (1 + a, "f")
a = 1:5 ; attr (a, "f") = 2 ; a ; attr (a, "f") ; a + 1 ; attr (a + 1, "f") ; 1 + a ; attr (1 + a, "f")
a = 1 ; attr (attr (a, "f"), "g") = 4
a = 1 ; attr (a, "f") = 2 ; attr (attr (a, "f"), "g") = 3 ; attr (attr (attr (a, "f"), "g"), "f") = 4 ; attr (a, "f") ; attr (attr (a, "f"), "g") ; attr (attr (attr (a, "f"), "g"), "f") ; a
a = 1 ; attr (a, "f") = 2 ; attr (attr (a, "f"), "g") = 3 ; attr (attr (attr (a, "f"), "g"), "f") = 4 ; attr (a, "f") ; attr (attr (a, "f"), "g") ; attr (attr (attr (a, "f"), "g"), "f") ; a
a = 1 ; attr (a, "f") = 2 ; attr (attr (a, "f"), "g") = 3 ; b = attr (attr (a, "f"), "g") ; attr (b, "f") = 4 ; attr (a, "f") ; attr (attr (a, "f"), "g") ; b ; attr (b, "f") ; a
f = "g" ; a = 1 ; b = 2 ; attr (a, f) = 2 ; attr (b, f) = 3 ; attr (a + b, f) ; attr (a + b, "g") ; attr (a + b, "f")
f = "g" ; a = 1 ; b = 2 ; attr (a, f) = 2 ; attr (b, f) = 3 ; attr (a - b, f) ; attr (a * b, f) ; attr (a / b, f) ; attr (a < b, f) ; attr (a > b, f) ; attr (a <= b, f) ; attr (a >= b, f) ; attr (a == b, f) ; attr (a != b, f)
a = 1 ; b = 2 ; attr (a, "x") = 3 ; attr (b, "y") = 4 ; attr (a + b, "x") ; attr (a + b, "y")
a = function (x) x ; attr (a, "f") = 2 ; a ; attr (a, "f") ; attr (a, "f") = function (x) x ; a ; attr (a, "f") ; attr (a, "f") = NULL ; a ; attr (a, "f") ; attr (a, "f") = NA ; a ; attr (a, "f")
a = 1L ; attr (a, "f") = 2 ; a ; attr (a, "f") ; attr (a, "f") = function (x) x ; a ; attr (a, "f") ; attr (a, "f") = NULL ; a ; attr (a, "f") ; attr (a, "f") = NA ; a ; attr (a, "f")
a = 2i ; attr (a, "f") = 2 ; a ; attr (a, "f") ; attr (a, "f") = function (x) x ; a ; attr (a, "f") ; attr (a, "f") = NULL ; a ; attr (a, "f") ; attr (a, "f") = NA ; a ; attr (a, "f")
a = NaN ; attr (a, "f") = 2 ; a ; attr (a, "f") ; attr (a, "f") = function (x) x ; a ; attr (a, "f") ; attr (a, "f") = NULL ; a ; attr (a, "f") ; attr (a, "f") = NA ; a ; attr (a, "f")
a = NA ; attr (a, "f") = 2 ; a ; attr (a, "f") ; attr (a, "f") = function (x) x ; a ; attr (a, "f") ; attr (a, "f") = NULL ; a ; attr (a, "f") ; attr (a, "f") = NA ; a ; attr (a, "f")
a = "" ; attr (a, "f") = 2 ; a ; attr (a, "f") ; attr (a, "f") = function (x) x ; a ; attr (a, "f") ; attr (a, "f") = NULL ; a ; attr (a, "f") ; attr (a, "f") = NA ; a ; attr (a, "f")
a = "" ; attr (a, "") = 2 ; a ; attr (a, "") ; attr (a, "") = function (x) x ; a ; attr (a, "") ; attr (a, "") = NULL ; a ; attr (a, "") ; attr (a, "") = NA ; a ; attr (a, "")
a = NULL ; attr (a, "f") = 2
a = -10:10 ; a ; a [3] = 9 ; a ; a [6:9] ; a > 0 ; a = 0 ; a [a = 0] = 8 ; a ; a [a < 1] = 7 ; a ; a [-2] ; a [-4:-7]
a = -10:10 ; attr (a, "x") = 9 ; attr (a, "x") ; attr (a [1], "x") ; attr (a [-1], "x") ; attr (a [1], "y") = 8 ; a ; attr (a [1], "y") ; attr (a, "y") ; b = a [1] ; attr (b, "z") = 7 ; attr (b, "z") ; attr (a [1], "z")
a = -10:10 ; a [c (TRUE, FALSE, TRUE)] ; a [80:90] ; a [-9:0] ; a [c ("x", "y")] ; a [NA] ; a [NaN] ; a [c (TRUE, FALSE, NA)] ; a ["TRUE"] ; a [0] ; a [a]
a = 1 ; attr (a, "abc") = 2 ; attr (a, "a") ; attr (a, "a") = 3 ; attr (a, "a") ; attr (a, "ab") ; attr (a, "abc") ; attr (a, "ab") = 4 ; attr (a, "a") ; attr (a, "ab") ; attr (a, "abc")
a = 1 ; attr (a, "abc") = 2 ; attr (a, "ab") = 3 ; attr (a, "a")
a = 1 ; attr (a, "abc") = 2 ; attr (a, "ab") = 3 ; attr (a, "a", TRUE) ; attr (a, "ab", TRUE) ; attr (a, "abc", TRUE) ; attr (a, "a", FALSE) ; attr (a, "ab", FALSE) ; attr (a, "abc", FALSE)
a = 1 ; attr (a, "abc") = 2 ; attr (a, "ab") = 3 ; attr (a, "a", "") ; attr (a, "ab", "") ; attr (a, "abc", "") ; attr (a, "a", 1i) ; attr (a, "ab", 1i) ; attr (a, "abc", 1i)
a = 1 ; attr (a, "abc") = 2 ; attr (a, "a") ; attr (a, "a", TRUE) ; attr (a, "a", FALSE) ; attr (a, "a", FALSE) = 3
a = 1 ; attr (a, "f", TRUE, FALSE)
"attr=" = function (x, y, value) x = value + 1 ; a = 1 ; attr (a, "f") = 2 ; a ; attr (a, "f")
"attr<-" = function (x, y, value) x = value + 1 ; a = 1 ; attr (a, "f") = 2 ; a ; attr (a, "f")
attr (attr, "f") = 1 ; attr ; attr (attr, "f")
a <- 1 ; f <- function (a) { attr (a, "f") <- 2 ; attr (a, "f") } ; f (3) ; a ; attr (a, "f")
a <- 1 ; f <- function (a) { attr (a, "f") = 2 ; attr (a, "f") } ; f (3) ; a ; attr (a, "f")
a <- 1 ; f <- function (a) { attr (a, "f") <<- 2 ; attr (a, "f") } ; f (3) ; a ; attr (a, "f")
a <- 1 ; f <- function (a) { attr (a, "f") <- 2 ; attr (a, "f") } ; f (a) ; a ; attr (a, "f")
a <- 1 ; f <- function (a) { attr (a, "f") = 2 ; attr (a, "f") } ; f (a) ; a ; attr (a, "f")
a <- 1 ; f <- function (a) { attr (a, "f") <<- 2 ; attr (a, "f") } ; f (a) ; a ; attr (a, "f")
a <- 1 ; attr (a, "f") <- 2 ; x <- "" ; attr (attr (a, x <- paste (x, "f", sep = "")), "g") <- 3 ; x ; a ; attr (a, "f") ; attr (a, "ff") ; attr (attr (a, "ff"), "g")
a <- 1 ; attr (a, "f") <- 2 ; x <- "" ; attr (attr (a, x <- paste (x, "f")), "g") <- 3
f <- function () { x <<- x + 1 ; "f" } ; x <- 0 ; a <- 1 ; attr (a, "f") <- 2 ; attr (attr (a, f ()), "g") <- 3 ; x ; a ; attr (a, "f") ; attr (attr (a, "f"), "g")
a <- 1 ; f <- function () { a <<- 2 ; "f" } ; attr (a, "f") <- 3 ; attr (attr (a, f ()), "g") <- 4 ; a ; attr (a, "f") ; attr (attr (a, "f"), "g")
n <- 0 ; a <- 1 ; f <- function () { n <<- n + 1 ; "f" } ; attr (a, f ()) <- 3 ; n ; attr (attr (a, f ()), "g") <- 4 ; n ; attr (attr (attr (a, f ()), "g"), "h") <- 5 ; n ; a ; attr (a, "f") ; attr (attr (a, "f"), "g") ; attr (attr (attr (a, "f"), "g"), "h")
n <- 0 ; a <- 1 ; f <- function () { n <<- n + 1 ; a } ; attr (f (), "f") <- 2 ; n ; attr (attr (f (), "f"), "g") <- 3 ; n ; attr (attr (attr (f (), "f"), "g"), "f") <- 4 ; n ; attr (f (), "f") ; n ; attr (attr (f (), "f"), "g") ; n ; attr (attr (attr (f (), "f"), "g"), "f") ; n ; a
a <- 1 ; attr (a, c ("f", "g")) <- 1:2 ; attr (a, "f") ;  attr (a, "g") ; a ; attr (a, c ("f", "g"))
a <- 1 ; attr (a, c ("f", "g")) <- 1:2 ; attr (attr (a, c ("f", "g")), "h") <- 3
l <- list (a = 5) ; l$a ; l[["a"]] ; l["a"] ; l[a]
l <- list (ab = 5) ; l$a ; l[["a"]] ; l[["ac"]] ; l["a"] ; l["ac"] ; l[a]
l <- list (ab = 5, abc = 3) ; l$a ; l$ab ; l$abc ; l[["a"]] ; l[["ab"]] ; l[["abc"]] ; l["a"] ; l["ab"] ; l["abc"] ; l[a]

# Tests about special attributes.
a <- 1:10 ; attr (a, "dim") <- 1
a <- 1:10 ; attr (a, "dim") <- NaN
a <- 1:10 ; attr (a, "dim") <- NA
a <- 1:10 ; attr (a, "dim") <- TRUE
a <- 1:10 ; attr (a, "dim") <- "a"
a <- 1:10 ; attr (a, "dim") <- c () ; attr (a, "dim") <- list ()
a <- 1:10 ; attr (a, "dim") <- "10" ; attr (a, "dim") ; a ; a [5] ; a [5, 1]
a <- 1:10 ; attr (a, "dim") <- 10.5 ; attr (a, "dim") ; a ; a [5] ; attr (a, "dim") <- 10 ; a ; a [5] ; attr (a, "dim") <- NULL ; a ; a [] ; a [5]
a <- 1:10 ; attr (a, "dim") <- c (2, -1, 5, -1)
a <- 1:10 ; attr (a, "dim") <- c (2, NA, 5)
a <- 1:10 ; attr (a, "dim") <- c (2, 5) ; attr (a, "dim") ; a ; a [5] ; a [2, 3] ; a [0, 0] ; a [] ; a [-1] ; a [-2] ; a [1,] ; a [-1,] ; a [-1, -2] ; a [1, -3] ; attr (a [1, -3], "dim") ; attr (a [1, -3], "dim") <- c (2, 2) ; attr (a [1, -3], "dim")
a <- 1:27 ; attr (a, "dim") <- c (3, 3, 3) ; a ; a [1] ; a [1, 2, 3] ; a [1, 2]
a <- 1:27 ; attr (a, "dim") <- c (3, 3, 3, 1) ; a ; a [10] ; a [-1] ; a [1, 2, 3, 1] ; a [1, 2, 3, 1] ; a [1, 2, 3, 0] ; attr (a[-1], "dim")
a <- 1:27 ; attr (a, "dim") <- c (3, 3, 3, 1) ; a [1:3, 1, 1:2, 1] ; attr (a [1:3, 1, 1:2, 1], "dim") ; attr (a [1:3, 1, 1:2, 1], "dim") <- 6 ; a [1:3, 1, 1:2, 1]
a <- 1:81 ; attr (a, "dim") <- c (3, 3, 3, 3) ; attr(attr (a, "dim"), "dim") <- c (2, 2) ; attr(attr (a, "dim"), "dim") ; a
a <- 1 ; attr (a, "dim") <- 1 ; c <- a + 1 ; d <- 1 + a ; attr (c, "dim") ; attr (d, "dim") ; c ; d ; a
a <- 1:3 ; attr (a, "dim") <- 2 ; c <- a + 1 ; d <- 1 + a ; attr (c, "dim") ; attr (d, "dim") ; c ; d ; a
a <- 1:10 ; attr (a, "names") <- 1 ; a ; a [10] ; a [1] ; a [3]
a <- 1:10 ; attr (a, "names") <- 10:1 ; a ; a [10] ; a [1] ; a [3]
a <- 1:10 ; attr (a, "names") <- c (TRUE, FALSE) ; a ; a [10] ; a [1] ; a [TRUE] ; a [FALSE] ; a [0] ; a []
a <- 1:10 ; attr (a, "names") <- c ("a", "b", "c") ; a ; a [10] ; a [1] ; a ["a"] ; a ["b"] ; a ["d"] ; a []
a <- 1:10 ; attr (a, "names") <- c (0.5, 1.5, 2, 2.5) ; a ; a [10] ; a [1] ; a [0.5] ; a [1.5] ; a [2] ; a [2.5] ; a [3.5]
a <- 1:4 ; attr (a, "names") <- c (1, 1, 1, 1) ; a ; a [1]
a <- 1:3 ; attr (a, "names") <- c ("a", "a", "a") ; a ; a ["a"] ; attr (a, "names") <- NULL ; a ; a [NULL]
a <- 1:2 ; attr (a, "names") <- c ("abc", "def") ; a ["abc"] ; a ["ab"] ; a [""]
a <- 1 ; attr (a, "names") <- "b" ; c <- a + 1 ; d <- 1 + a ; attr (c, "names") ; attr (d, "names") ; c ; d ; a
a <- 1:3 ; attr (a, "names") <- "b" ; c <- a + 1 ; d <- 1 + a ; attr (c, "names") ; attr (d, "names") ; c ; d ; a
a <- 1 ; attr (a, "class") <- c ("a", "b") ; attr (a, "class") <- 2
a <- 1 ; attr (a, "class") <- NULL ; a ; attr (a, "class") <- NA
a <- NULL ; attr (a, "class") <- c () ; attr (a, "class") <- ""
a <- 1 ; attr (a, "class") <- "factor"
a <- 1 ; attr (a, "class") <- c ("a", "factor", "b")
a <- 1L ; attr (a, "class") <- "factor" ; attr (a, "class") <- c ("a", "factor", "b")

# Tests about cat (for outputs).
.Internal (cat (list ("Hello", "world"), 1, " ", 1000, "", FALSE))
.Internal (cat (list (), 1, "-", 1000, "", FALSE))
cat ("") ; cat (')') ; cat ("}") ; cat ('>') ; cat ("]") ; cat ('(') ; cat ("{") ; cat ('<') ; cat ("[")
cat ('\n') ; cat (")\n") ; cat ('}\n') ; cat (">\n") ; cat (']\n') ;cat ("(\n") ; cat ('{\n') ; cat ("<\n") ; cat ('[\n')
cat (1) ; cat (2L) ; cat (.5) ; cat (TRUE) ; cat (NA) ; cat (Inf) ; cat (NaN) ; cat (NULL) ; cat ("TRUE")
cat (2) ; cat ("3") ; cat ('[4] 5') ; cat ("[1] 6")
cat ("function (x) x") ; cat (function (x) x)
cat (cat)
cat (a <- 1) ; a
cat (cat <- 1) ; cat (cat) ; cat (cat <- function (a) 3)

# Tests about randomness.
runif ()
typeof <- function (x) .Internal (typeof (x)) ; typeof (runif (1))
length (runif (42))

# Tests about subset.
l <- list (a = 1) ; l$a
l <- list (1, a = 2, 3) ; l$a
l <- list (ab = 1, b = 2) ; l$ab ; l$a
l <- list (ab = 1, abc = 2) ; l$ab ; l$abc ; l$a
l <- list () ; l$a
l <- 2 ; l$a
l <- "a" ; l$a

# Tests about some library functions.
length ("") ; length ("a") ; length ("\\")
nchar ("") ; nchar ("a") ; nchar ("\\")
length (c ("", "a", "\\")) ; nchar (c ("", "a", "\\"))
length (NA) ; nchar (NA)

# Miscellaneous.
levels
mode
a$b
a::b
a:::b
a
`a`

# These are tests to test the tester and the parser.
"function" ; 'function' ; 1 # function
"Error" ; 'Error' ; "Error:" ; 'Error:' ; 1 # Error
"Warning" ; 'Warning' ; "Warning:" ; 'Warning:' ; 1 # Warning
"function (x) x" ; 'function (x) x' ; function (x) x ; function (x) function (y) x ; 1 # function (x) x
f <- function ("1") 1
"[1] 1" ; 1
"function" <- 42
"" <- 9
"" ; '' ; "''" ; '""' ; "\"" ; '\'' ; "\'" ; '\"' ; '\\' ; "\\" ; '\\\'' ; "\\\"" ; '#' ; "#" # '"
')' ; "(" ; "\'\"\'" ; '\"\'\"' ; "\\'\\'" ; '\\"\\"'
'\n' ; "\n" ; '\\n' ; "\\n" ; '\\\n' ; "\\\n"
';' ; ";"
# q ("no")

