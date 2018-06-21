# @line
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
f <- function () break ; repeat f ()
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
repeat 4 * break ; repeat (4) * break ; repeat (x <- 1) * break ; x ; repeat x <- 2 * break ; x

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
if ('falsE') "TRUE" else '4L'
if ("F") "" else FALSE
if ('f') 2L else TRUE
if ("fALSE") FALSE else 2L
if ('TR') 2L else TRUE
if ("TRUE ") c (FALSE, TRUE) else 2L
if (' TRUE') 2L else c (FALSE, TRUE)
if ("") 1 else NULL
if ('1') NULL else NA
if ("0") NULL else ""
# if (c (TRUE, FALSE)) NULL else 1L
# if (c (TRUE, TRUE)) "a" else x
# if (c (FALSE, FALSE)) x else 'a'
# if (c (FALSE, TRUE)) (function () x) else 2L
if (logical (0)) 1 else 42
# if (c ('TRUE', "ab")) NULL else NA
# if (c ("T", "T")) "a" else NA
# if (c ('FALSE', '')) x else NA
# if (c ("F", 'TRUE')) (function () x) else NA
if (character (0)) 1 else NA
if (integer (0)) NA else NULL
# if (complex (0)) 0 else NULL
if (0) 1L else NULL
if (1) NA else NULL
if (0L) '1' else NULL
if (1L) 1L else NULL
# if (1+0i) 1i else NA
#if (1+1i) 1i else NULL
#if (0+0i) 1i else 1
if (0i) 1 else 1i
#if (0+1i) 1i else 1L
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
