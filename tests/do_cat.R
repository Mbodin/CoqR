# @line
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

