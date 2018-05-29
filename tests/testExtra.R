# @line
# This file is meant to be read line-by-line, each line being independent from the other.
# The state at the beginning of each line should always be the initial state.
# Furthermore, if an error is thrown, the next line should be unaffected by this error, starting back from the initial state.
# A test passes if the output of the tested interpreter is the same than R’s.
# All step should return the same output.

# Tests about the modification of primitive operators.
"if" <- function (x, y, z) x + y + z ; if (1) 2 else 3
'if' <- function (x) -x ; if (1) 2 else 3
"(" <- function (x) 2 * x ; (2)
'(' <- function () 1 ; (2)
({ "(" <- function (x) 2 * x ; 3 })
'{' <- function (x) 2 * x ; {2}
{ "{" <- function (x) 2 * x ; 3 } ; { 5 ; 7 }
'<-' <- function (x, y) x + y ; 1 <- 2 ; 3 -> 4 ; 5 <- 6 -> 7
"<<-" <- function (x, y) x + y ; 1 <<- 2 ; 3 ->> 4 ; 5 <<- 6 ->> 7
"+" <- function (x, y) x - y ; 1 + 2
'1' <- 2 ; "1L" <- 2L ; 1 ; 1L
"1" <- function (x) x ; 1 (2)
"NULL" <- 1 ; NULL ; NULL <- 1
'function' <- function (x, y, z) y ; function (x) 2 ; function (x) 2 + x
"function" <- function (x, y, z) x ; function (x) 2 + x ; function () 2 + x ; function (x = 1, y) 2 + x ; function (x = 1, y, x) 2 + x
'function' <- function (x, y, z) z ; function (x) 2 + x ; .Internal (typeof (function (x) x + 1)) ; .Internal (typeof (function () NULL))

# Tests about randomness.
runif ()
typeof <- function (x) .Internal (typeof (x)) ; typeof (runif (1))
length (runif (42))

# Tests about some library functions.
length ("") ; length ("a") ; length ("\\")
nchar ("") ; nchar ("a") ; nchar ("\\")
length (c ("", "a", "\\")) ; nchar (c ("", "a", "\\"))
length (list ("", "a", "\\")) ; nchar (list ("", "a", "\\"))
length (NA) ; nchar (NA)
length (NULL) ; nchar (NULL)
length (NaN) ; nchar (NaN)

# Miscellaneous primitive and builtin operator tests.
.Primitive ("invisible") () ; .Primitive ("invisible") (42)
(.Primitive ("invisible") ()) ; (.Primitive ("invisible") (42))
.Primitive ("invisible") (42, 18)
globalenv () ; parent.frame () ; globalenv () == parent.frame ()

# These are tests to test the tester and the parser.
"function" ; 'function' ; 1 # function
"Error" ; 'Error' ; "Error:" ; 'Error:' ; 1 # Error
"Warning" ; 'Warning' ; "Warning:" ; 'Warning:' ; 1 # Warning
"function (x) x" ; 'function (x) x' ; function (x) x ; function (x) function (y) x ; 1 # function (x) x
f <- function ("1") 1
"[1] 1" ; 1
"function" <- 42
"" <- 9
``
levels
mode
a$b
a::b
a:::b
a
`a`
"" ; '' ; "''" ; '""' ; "\"" ; '\'' ; "\'" ; '\"' ; '\\' ; "\\" ; '\\\'' ; "\\\"" ; '#' ; "#" # '"
')' ; "(" ; "\'\"\'" ; '\"\'\"' ; "\\'\\'" ; '\\"\\"'
'\n' ; "\n" ; '\\n' ; "\\n" ; '\\\n' ; "\\\n"
';' ; ";"
# q ("no")

