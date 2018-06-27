# @line

#### &  ####

TRUE & TRUE
TRUE & FALSE
FALSE & TRUE
FALSE & FALSE

TRUE & NA
NA & TRUE
FALSE & NA
NA & FALSE

1 & 1
1 & 0
0 & 1
0 & 0

1 & NA
NA & 1
0 & NA
NA & 0
NA & NA

"a" & 1
"a" & "b"
1 & "b"
0 & "b"

"T" & 1
"True" & "b"
1 & "TRUE"
0 & "true"
"F" & 1
"False" & "b"
1 & "FALSE"
0 & "false"
"NA" & NA


#### | ####

TRUE | TRUE
TRUE | FALSE
FALSE | TRUE
FALSE | FALSE

TRUE | NA
NA | TRUE
FALSE | NA
NA | FALSE

1 | 1
1 | 0
0 | 1
0 | 0

1 | NA
NA | 1
0 | NA
NA | 0
NA | NA

"a" | 1
"a" | "b"
1 | "b"
0 | "b"

"T" | 1
"True" | "b"
1 | "TRUE"
0 | "true"
"F" | 1
"False" | "b"
1 | "FALSE"
0 | "false"
"NA" | NA


#### ! ####
!TRUE
!"TRUE"
!FALSE
!"FALSE"
!NA
!NaN
!1
!1L
!1:10
!"hello"
!(function () NULL)

!!TRUE
!!FALSE

!(TRUE & TRUE)
!(TRUE & FALSE)
!(FALSE & TRUE)
!(FALSE & FALSE)

!(TRUE & NA)
!(NA & TRUE)
!(FALSE & NA)
!(NA & FALSE)

!(1 & 1)
!(1 & 0)
!(0 & 1)
!(0 & 0)

!(1 & NA)
!(NA & 1)
!(0 & NA)
!(NA & 0)
!(NA & NA)

!("a" & 1)
!("a" & "b")
!(1 & "b")
!(0 & "b")

!("T" & 1)
!("True" & "b")
!(1 & "TRUE")
!(0 & "true")
!("F" & 1)
!("False" & "b")
!(1 & "FALSE")
!(0 & "false")
!("NA" & NA)

!(TRUE | TRUE)
!(TRUE | FALSE)
!(FALSE | TRUE)
!(FALSE | FALSE)

!(TRUE | NA)
!(NA | TRUE)
!(FALSE | NA)
!(NA | FALSE)

!(1 | 1)
!(1 | 0)
!(0 | 1)
!(0 | 0)

!(1 | NA)
!(NA | 1)
!(0 | NA)
!(NA | 0)
!(NA | NA)

!("a" | 1)
!("a" | "b")
!(1 | "b")
!(0 | "b")

!("T" | 1)
!("True" | "b")
!(1 | "TRUE")
!(0 | "true")
!("F" | 1)
!("False" | "b")
!(1 | "FALSE")
!(0 | "false")
!("NA" | NA)


#### Other ####

list(1, 2, 3) & TRUE
1 & function(x) { x }
