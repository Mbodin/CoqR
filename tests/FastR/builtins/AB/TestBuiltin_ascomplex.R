argv <- list(logical(0), logical(0));as.complex(argv[[1]],argv[[2]]);
argv <- list(FALSE, FALSE);as.complex(argv[[1]],argv[[2]]);
argv <- list(' ');as.complex(argv[[1]]);
argv <- list(structure(c(-0.626453810742332, 0.183643324222082, -0.835628612410047, 1.59528080213779, 0.329507771815361, -0.820468384118015, 0.487429052428485, 0.738324705129217, 0.575781351653492, -0.305388387156356, 1.51178116845085, 0.389843236411431, -0.621240580541804, -2.2146998871775, 1.12493091814311, -0.0449336090152309, -0.0161902630989461, 0.943836210685299, 0.821221195098089, 0.593901321217509, 0.918977371608218, 0.782136300731067, 0.0745649833651906, -1.98935169586337, 0.61982574789471), .Dim = c(5L, 5L), .Dimnames = list(c('1', '2', '3', '4', '5'), c('a', 'b', 'c', 'd', 'e'))));as.complex(argv[[1]]);
argv <- list('1.3');as.complex(argv[[1]]);
argv <- list(structure(list(c0 = structure(integer(0), .Label = character(0), class = 'factor')), .Names = 'c0', row.names = character(0), class = 'data.frame'), structure(list(c0 = structure(integer(0), .Label = character(0), class = 'factor')), .Names = 'c0', row.names = character(0), class = 'data.frame'));as.complex(argv[[1]],argv[[2]]);
argv <- list(NA_complex_);as.complex(argv[[1]]);
argv <- list(integer(0));as.complex(argv[[1]]);
argv <- list(1L);as.complex(argv[[1]]);
argv <- list(structure(list(a = 1), .Names = 'a'));as.complex(argv[[1]]);
argv <- list(NULL, NULL);as.complex(argv[[1]],argv[[2]]);
{ as.complex() }
{ as.complex(0) }
{ as.complex(TRUE) }
{ as.complex("1+5i") }
{ as.complex("-1+5i") }
{ as.complex("-1-5i") }
{ as.complex(0/0) }
{ as.complex(c(0/0, 0/0)) }
{ as.complex(c("1","hello")) }
{ as.complex("TRUE") }
{ x<-c(a=1.1, b=2.2); dim(x)<-c(1,2); attr(x, "foo")<-"foo"; y<-as.complex(x); attributes(y) }
{ x<-c(a=1L, b=2L); dim(x)<-c(1,2); attr(x, "foo")<-"foo"; y<-as.complex(x); attributes(y) }
{ as.complex("Inf") }
{ as.complex("NaN") }
{ as.complex("0x42") }
{ as.complex(NULL) }
{ as.complex("1e10+5i") }
{ as.complex("-.1e10+5i") }
{ as.complex("1e-2+3i") }
{ as.complex("+.1e+2-3i") }
{ as.complex(list(42)) }
{ as.complex(list(NULL)) }
{ as.complex(list("foo")) }
{ as.complex.cls <- function(x) 42; as.complex(structure(c(1,2), class='cls')); }
