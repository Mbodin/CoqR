# @line
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
# 1 + 2i ; 1L + 2i ; (1L + 2i) - 2i ; (1L + 2i) - 2i == 1L
# NaN + 3i ; NA + 3i ; Inf + 3i ; 3i + 1/0 ; NaN + 0i ; NA + 0i
# (1 + 1i) * NaN ; 1i * NaN ; 1 * NaN ; 1i * c (NaN, 0i)[1] ; (1 + 1i) * c (NaN, 0i)[1]
# (1 + 1i) * NA ; 1i * NA ; 1 * NA ; 1i * c (NA, 0i)[1] ; (1 + 1i) * c (NA, 0i)[1]
# "" == '' ; c ('1', "1")
1. == 1 ; 1.0 == 1 ; 1.00 == 1 ; 1 == 1.000 ; 0.5 == .5 ; 0.5 == 0.50 ; 0.5 == .500
0.99999999999999999999 == 1 ; 0.99999999999999999999999999999999 == 1.
2 == 2L ; -0 == 0 ; -0 == 0L ; 0. == -0L ; 1 == TRUE ; 1L == TRUE ; 0 == FALSE ; 0L == FALSE
# "FALSE" == FALSE ; 'False' == FALSE ; "false" == FALSE ; 'F' == FALSE ; "f" == FALSE ; 'fALSE' == FALSE
# "TRUE" == TRUE ; "True" == TRUE ; "true" == TRUE ; "T" == TRUE ; "t" == TRUE ; "tRUE" == TRUE
NA == NA ; NaN == NaN ; NA == NaN ; NaN == 0/0 ; NaN == -0/0 ; NaN == 1 + 0/0 ; NaN == 1 + NaN
# NA_integer_ == NA ; NA_character_ == NA ; NA_complex_ == NA ; NA_real_ == NA
# NA_complex_ == NA_complex_ ; NA_complex_ = NA_integer_ ; NA_complex_ = NA_character_ ; NA_complex_ = NA_real_
# NA_integer_ == NA_complex_ ; NA_integer_ = NA_integer_ ; NA_integer_ = NA_character_ ; NA_integer_ = NA_real_
# NA_character_ == NA_complex_ ; NA_character_ = NA_integer_ ; NA_character_ = NA_character_ ; NA_character_ = NA_real_
# NA_real_ == NA_complex_ ; NA_real_ = NA_integer_ ; NA_real_ = NA_character_ ; NA_real_ = NA_real_
NULL == 0 ; NULL == NA ; NULL == NaN ; NULL == FALSE ; NULL == TRUE
0 == -0 ; 0L == -0L ; 1/Inf == 0 ; -1/Inf == 0 ; NaN == Inf - Inf
.Internal == .Internal
# c (1, 1L) ; c (1, NULL) ; c (1, TRUE) ; c (1, "a") ; c (1, NA) ; c (1, NaN) ; c (1, 3i)
# c (1L, 1L) ; c (1L, NULL) ; c (1L, TRUE) ; c (1L, 'a') ; c (1L, NA) ; c (1L, NaN) ; c (1L, 3i)
c (NULL, 1L) ; c (NULL, NULL) ; c (NULL, TRUE) ; c (NULL, "a") ; c (NULL, NA) ; c (NULL, NaN) ; c (NULL, 3i)
c (TRUE, 1L) ; c (TRUE, NULL) ; c (TRUE, TRUE) ; c (TRUE, 'a') ; c (TRUE, NA) ; c (TRUE, NaN) ; c (TRUE, 3i)
# c ("b", 1L) ; c ('b', NULL) ; c ("b", TRUE) ; c ('b', "a") ; c ("b", NA) ; c ('b', NaN) ; c ("b", 3i)
c (NA, 1L) ; c (NA, NULL) ; c (NA, TRUE) ; c (NA, "a") ; c (NA, NA) ; c (NA, NaN) ; c (NA, 3i)
c (NaN, 1L) ; c (NaN, NULL) ; c (NaN, TRUE) ; c (NaN, "a") ; c (NaN, NA) ; c (NaN, NaN) ; c (NaN, 3i)
c (4i, 1L) ; c (4i, NULL) ; c (4i, TRUE) ; c (4i, "a") ; c (4i, NA) ; c (4i, NaN) ; c (4i, 3i)
#c (1, TRUE, 'a') ; c (c (1, TRUE), "a") ; c (1, c (TRUE, 'a'))
c (1) ; c (1L) ; c (1i) ; c (TRUE) ; c ("a") ; c (NA) ; c (NaN) ; c (Inf)
c () ; c (NULL) ; c (NULL, NULL, NULL, NA, NULL, NULL, NULL)
#c (NA, 1) ; c (NA_character_, 1) ; c (NA_complex_, 1) ; c (NA_character_, NA_complex_, 1)
#c (x = 1) ; c (y = 1)
c (1:10) ; c (c) ; c (function (x) x)
list (c ()) ; list (c (1)) ; list (c (1, 2), c ("1", "2"))
list () ; c (list ()) ; c (list (1)) ; c (list (1, 2), list ("1", "2")) ; c (list (1, TRUE, "a")) ; c (list (1, TRUE, "a"), list (), list (NA), list (FALSE))
list (1, 2) ; list (list (1, 2), list (3, 4)) ; list (NULL) ; list (NA) ; list (FALSE) ; list (NULL, NA, NaN, FALSE) ; list (NULL, NA, NaN, FALSE, list (list (list (list ()), 9)), '', list)
c (1, TRUE) ; c (1, TRUE, list ()) ; c (1, TRUE, "a", NULL, list (), NA, list (FALSE), function (x) x)
NULL == list () ; NULL == c () ; list () == list () ; list () == c () ; list () == 1 ; list () == NA ; list () == NaN ; list == list
#list (1) == c (1) ; list (1) == 1 ; list (1) == c (1L) ; list (1) == c (1i) ; list (1L) == c (1i) ; list (1) == list (1)
#NA == "NA" ; list (NA) == NA ; list (NA) == "NA" ; list ("NA") == "NA" ; list ("NA") == NA
#list (1, TRUE) == c ("1", "TRUE") ; list (TRUE, TRUE) == c ("true", "T") ; list (TRUE, TRUE) == c (1) ; list (TRUE, "") == c (1) ; list ("") == c (1) ; list (" ") == c (1) ; list (1, TRUE) == c (TRUE, "")
#(list (1, 2, 3)) [[2]] ; (1:3) [[2]] ; list (1) [[2]]
list (a = 3, b = 5) $ a ; list (a = 3, b = 5) $ c ; list (ab = 3, b = 4) $ a ; list (ab = 3, abc = 4) $ a ; list (ab = 3, abc = 4) $ ab
#1 == 1i ; 1 == 1 + 0i
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
# "1" > 2 ; '1' < 2 ; "1" <= 2 ; '1' >= 2 ; "1" == 2 ; "1" != 2
# 1 > '2' ; 1 < "2" ; 1 <= '2' ; 1 >= "2" ; 1 == '2' ; 1 != '2'
# '1' > "2" ; "1" < "2" ; "1" <= '2' ; '1' >= '2' ; "1" == "2" ; '1' != "2"
#"1" > 'TRUE' ; "1" < "TRUE" ; '1' <= "TRUE" ; '1' >= 'TRUE' ; "1" == "TRUE" ; "1" != 'TRUE'
1 > NA ; 1 < NA ; 1 <= NA ; 1 >= NA ; 1 == NA ; 1 != NA
NA > NA ; NA < NA ; NA <= NA ; NA >= NA ; NA == NA ; NA != NA
1 > NaN ; 1 < NaN ; 1 <= NaN ; 1 >= NaN ; 1 == NaN ; 1 != NaN
NaN > NaN ; NaN < NaN ; NaN <= NaN ; NaN >= NaN ; NaN == NaN ; NaN != NaN
#1 > "" ; 1 < '' ; 1 <= "" ; 1 >= '' ; 1 == "" ; 1 != ""
# 0 == 0i ; 0L == 0i ; 0 == 0L ; FALSE == TRUE - TRUE ; FALSE != TRUE - TRUE
1:5 > 5:1 ; 1:5 < 5:1 ; 1:5 >= 5:1 ; 1:5 <= 5:1 ; 1:5 == 5:1 ; 1:5 != 5:1
# 1 %% 2 ; 1 %% 1 ; 1 %% 0 ; 1 %% FALSE ; 1 %% TRUE
# 0 %% 2 ; 0 %% 1 ; 0 %% 0 ; 0 %% FALSE ; 0 %% TRUE
# -1 %% 2 ; -1 %% 1 ; -1 %% 3 ; -1 %% 0 ; -1 %% FALSE ; -1 %% TRUE
# 5.5 %% 4 ; -5.5 %% 4
# NA %% 1 ; NA %% 0 ; NaN %% 1 ; NaN %% 0 ; 1 %% NA ; 1 %% NaN ; 0 %% NA ; 0 %% NaN
# TRUE %% 2 ; TRUE %% 1 ; TRUE %% 0 ; TRUE %% FALSE ; TRUE %% TRUE
# FALSE %% 2 ; FALSE %% 1 ; FALSE %% 0 ; FALSE %% FALSE ; FALSE %% TRUE
# 0i %% 3
# 0i %% 0
# 0i %% 3i
# 7 %% 2:4 ; -10:10 %% 3 ; -10:10 %% NULL ; NULL %% 2 ; -10:10 %% 2:4 ; -10:10 %% 2:5
# 0 + 0i ; 0 - 0i ; -0 - 0i ; -0 + 0i
# 1 / 0 ; 1 / -0 ; 1 / 0i ; 1 / -0i ; 1 / 0 * 1i ; 1 / 0 * i
Inf + Inf ; Inf - Inf ; -Inf + Inf ; -Inf - Inf ; 1 / 0 + Inf ; 1 / 0 - Inf ; 1 / -0 + Inf ; 1 / -0 - Inf ; 1 / 0 + 1 / -0 ; 1 / 0 + 1 / 0
