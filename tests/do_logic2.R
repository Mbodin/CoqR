# @line

#### &&  ####

TRUE && TRUE
TRUE && FALSE
FALSE && TRUE
FALSE && FALSE

TRUE && NA
NA && TRUE
FALSE && NA
NA && FALSE

1 && 1
1 && 0
0 && 1
0 && 0

1 && NA
NA && 1
0 && NA
NA && 0
NA && NA

"a" && 1
"a" && "b"
1 && "b"
0 && "b"

#### || ####

TRUE || TRUE
TRUE || FALSE
FALSE || TRUE
FALSE || FALSE

TRUE || NA
NA || TRUE
FALSE || NA
NA || FALSE

1 || 1
1 || 0
0 || 1
0 || 0

1 || NA
NA || 1
0 || NA
NA || 0
NA || NA

"a" || 1
"a" || "b"
1 || "b"
0 || "b"


#### Other ####

list(1, 2, 3) && TRUE
1 && function(x) { x }

