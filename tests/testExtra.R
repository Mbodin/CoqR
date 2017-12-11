
# This file is meant to be read line-by-line, each line being independent from the other.
# In particular, if the state at the beginning of each line should always be the initial state.

# Tests about aborting primitives.
return
return (1)
return (0/0)
(return (1)) (2)
break
break (1)
next
next (1)

# Tests about if.
if ("TRUE") 1 else ""
if ("True") 1 else ""
if ("true") 1 else ""
if ("T") 1 else ""
if ("t") 1 else ""
if ("tRUE") 1 else ""
if ("FALSE") 1 else ""
if ("False") 1 else ""
if ("false") 1 else ""
if ("F") 1 else ""
if ("f") 1 else ""
if ("fALSE") 1 else ""
if ("") 1 else ""
if ("0") 1 else ""
if ("1") 1 else ""
if (c (TRUE, FALSE)) 1 else ""
if (0) 1 else ""
if (1) 1 else ""
if (0L) 1 else ""
if (1L) 1 else ""
if (1:3) 1 else ""
if (function () TRUE) 1 else ""
if (.Internal) 1 else ""
if (if (TRUE) FALSE else TRUE) 1 else ""
if (TRUE) a <- 1 else b <- 1 ; a ; b
if (FALSE) a <- 1 else b <- 1 ; b ; a

# Tests about typeof.
typeof <- function (x) .Internal (typeof (x)) ; typeof (1)
typeof <- function (x) .Internal (typeof (x)) ; typeof (1L)
typeof <- function (x) .Internal (typeof (x)) ; typeof ("")
typeof <- function (x) .Internal (typeof (x)) ; typeof (typeof)
typeof <- function (x) .Internal (typeof (x)) ; typeof (.Internal)

# Tests about lazy evaluation.
(function (x, y = x) { x <- 1 ; y ; x <- 2 ; y }) (3)
x <- 1 ; (function (x, y) { if (x) y }) (FALSE, x <- 2) ; x
x <- 1 ; (function (x, y, z) { z ; if (x) y }) (FALSE, x <- 2, x <- 3) ; x
x <- 1 ; (function (x, y, z) { z ; if (x) y }) (TRUE, x <- 2, x <- 3) ; x
x <- 1 ; (function (x, y) { (function (x, y) if (x) y) (x, y) }) (FALSE, x <- 2) ; x
(function (x, y = x <- 1) { x <- 2 ; y ; x }) (3)

# Tests about implicit conversions.
TRUE + TRUE ; TRUE + FALSE ; FALSE + FALSE
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
.Internal == .Internal

# Tests about assignments.
"x" <- 1 ; x

# Tests about the modification of primitive operators.
"if" <- function (x, y, z) x + y + z ; if (1) 2 else 3
"if" <- function (x) -x ; if (1) 2 else 3
"(" <- function (x) 2 * x ; (2)
"(" <- function () 1 ; (2)
"{" <- function (x) 2 * x ; {2}
"<-" <- function (x, y) x + y ; 1 <- 2
"<<-" <- function (x, y) x + y ; 1 <<- 2
"function" <- function (x, y, z) y ; function (x) 2

