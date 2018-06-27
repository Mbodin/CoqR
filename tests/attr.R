# @line

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
# a <- -10:10 ; a ; a [3] <- 9 ; a ; a [6:9] ; a > 0 ; a = 0 ; a [a = 0] <- 8 ; a ; a [a < 1] <- 7 ; a ; a [-2] ; a [-4:-7] ; a []
a <- -10:10 ; attr (a, "x") <- 9 ; attr (a, "x") ; attr (a [1], "x") ; attr (a [1], "y") <- 8 ; a ; attr (a [1], "y") ; attr (a, "y") ; b <- a [1] ; attr (b, "z") <- 7 ; attr (b, "z") ; attr (a [1], "z") #; attr (a [-1], "x")
# a <- -10:10 ; a [c (TRUE, FALSE, TRUE)] ; a [80:90] ; a [-9:0] ; a [c ("x", "y")] ; a [NA] ; a [NaN] ; a [c (TRUE, FALSE, NA)] ; a ["TRUE"] ; a [0] ; a [a]
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
a <<- -10:10 ; a ; a [3] <<- 9 ; a ; a [6:9] ; a > 0 ; a <<- 0 ; a [a <<- 0] <<- 8 ; a ; a [a < 1] <<- 7 ; a ; a [-2] # ; a [-4:-7]
# a <<- -10:10 ; attr (a, "x") <<- 9 ; attr (a, "x") ; attr (a [1], "x") ; attr (a [1], "y") <<- 8 ; a ; attr (a [1], "y") ; attr (a, "y") ; b <<- a [1] ; attr (b, "z") <<- 7 ; attr (b, "z") ; attr (a [1], "z") #; attr (a [-1], "x")
#a <<- -10:10 ; a [c (TRUE, FALSE, TRUE)] ; a [80:90] ; a [-9:0] ; a [c ("x", "y")] ; a [NA] ; a [NaN] ; a [c (TRUE, FALSE, NA)] ; a ["TRUE"] ; a [0] ; a [a]
a <<- 1 ; attr (a, "abc") <<- 2 ; attr (a, "a") ; attr (a, "a") <<- 3 ; attr (a, "a") ; attr (a, "ab") ; attr (a, "abc") ; attr (a, "ab") <<- 4 ; attr (a, "a") ; attr (a, "ab") ; attr (a, "abc")
a <<- 1 ; attr (a, "abc") <<- 2 ; attr (a, "ab") <<- 3 ; attr (a, "a")
a <<- 1 ; attr (a, "abc") <<- 2 ; attr (a, "ab") <<- 3 ; attr (a, "a", TRUE) ; attr (a, "ab", TRUE) ; attr (a, "abc", TRUE) ; attr (a, "a", FALSE) ; attr (a, "ab", FALSE) ; attr (a, "abc", FALSE)
a <<- 1 ; attr (a, "abc") <<- 2 ; attr (a, "ab") <<- 3 ; attr (a, "a", "") ; attr (a, "ab", "") ; attr (a, "abc", "") ; attr (a, "a", 1i) ; attr (a, "ab", 1i) ; attr (a, "abc", 1i)
a <<- 1 ; attr (a, "abc") <<- 2 ; attr (a, "a") ; attr (a, "a", TRUE) ; attr (a, "a", FALSE) ; attr (a, "a", FALSE) <<- 3
a <<- 1 ; attr (a, "f", TRUE, FALSE)
"attr<-" <<- function (x, y, value) x <<- value + 1 ; a <<- 1 ; attr (a, "f") <<- 2 ; a ; attr (a, "f")
"attr<-" <- function (x, y, value) x <- value + 1 ; a <- 1 ; 2 ->> attr (a, "f") ; a ; attr (a, "f")
"attr=" <<- function (x, y, value) x <<- value + 1 ; a <<- 1 ; attr (a, "f") <<- 2 ; a ; attr (a, "f")
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
a <- 1 ; attr (a, "f") <- 2 ; x <- "" ; attr (attr (a, x <- paste (x, "f")), "g") <- 3
f <- function () { x <<- x + 1 ; "f" } ; x <- 0 ; a <- 1 ; attr (a, "f") <- 2 ; attr (attr (a, f ()), "g") <- 3 ; x ; a ; attr (a, "f") ; attr (attr (a, "f"), "g")
a <- 1 ; f <- function () { a <<- 2 ; "f" } ; attr (a, "f") <- 3 ; attr (attr (a, f ()), "g") <- 4 ; a ; attr (a, "f") ; attr (attr (a, "f"), "g")
n <- 0 ; a <- 1 ; f <- function () { n <<- n + 1 ; "f" } ; attr (a, f ()) <- 3 ; n ; attr (attr (a, f ()), "g") <- 4 ; n ; attr (attr (attr (a, f ()), "g"), "h") <- 5 ; n ; a ; attr (a, "f") ; attr (attr (a, "f"), "g") ; attr (attr (attr (a, "f"), "g"), "h")
n <- 0 ; a <- 1 ; f <- function () { n <<- n + 1 ; a } ; attr (f (), "f") <- 2 ; n ; attr (attr (f (), "f"), "g") <- 3 ; n ; attr (attr (attr (f (), "f"), "g"), "f") <- 4 ; n ; attr (f (), "f") ; n ; attr (attr (f (), "f"), "g") ; n ; attr (attr (attr (f (), "f"), "g"), "f") ; n ; a
a <- 1 ; attr (a, c ("f", "g")) <- 1:2 ; attr (a, "f") ;  attr (a, "g") ; a ; attr (a, c ("f", "g"))
a <- 1 ; attr (a, c ("f", "g")) <- 1:2 ; attr (attr (a, c ("f", "g")), "h") <- 3

# Tests about special attributes.
a <- 1:10 ; attr (a, "dim") <- 1
a <- 1:10 ; attr (a, "dim") <- NaN
a <- 1:10 ; attr (a, "dim") <- NA
a <- 1:10 ; attr (a, "dim") <- TRUE
# a <- 1:10 ; attr (a, "dim") <- "a"
# a <- 1:10 ; attr (a, "dim") <- c () ; attr (a, "dim") <- list ()
# a <- 1:10 ; attr (a, "dim") <- "10" ; attr (a, "dim") ; a ; a [5] ; a [5, 1]
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
