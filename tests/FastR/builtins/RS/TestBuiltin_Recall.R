{ f<-function(i) { if(i<=1) 1 else i*Recall(i-1) } ; f(10) }
{ f<-function(i) { if(i<=1) 1 else i*Recall(i-1) } ; g <- f ; f <- sum ; g(10) }
{ f<-function(i) { if (i==1) { 1 } else if (i==2) { 1 } else { Recall(i-1) + Recall(i-2) } } ; f(10) }
{ Recall(10) }
{ f <- function(tarDepth,curDepth) { if (tarDepth == curDepth) {curDepth} else {Recall(tarDepth,curDepth+1)}}; f(3,0) }
