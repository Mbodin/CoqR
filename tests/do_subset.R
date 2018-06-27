# @line


# x<-1:3; x[0-2]
# x<-1:3; x[FALSE]
# x<-1:3; x[TRUE]
# x<-c(TRUE,TRUE,FALSE); x[0-2]
# x<-c(1,2);x[0-3]
#
# x<-10; x[0-1]
# x<-10; x[NA]

x <- c(TRUE, FALSE, NA) ; x[0]
#x <- list(1L, 2L, 3L) ; x[10]


x<-1:5 ; x[3:4]
x<-1:5 ; x[4:3]
x<-c(1,2,3,4,5) ; x[4:3]
(1:5)[3:4]
x<-(1:5)[2:4] ; x[2:1]
#x<-1:5;x[c(0-2,0-3)]
#x<-1:5;x[c(0-2,0-3,0,0,0)]
x<-1:5;x[c(2,5,4,3,3,3,0)]
#x<-1:5;x[c(2L,5L,4L,3L,3L,3L,0L)]
#f<-function(x, i) { x[i] } ; f(1:3,3:1) ; f(1:5,c(0,0,0,0-2))
#f<-function(x, i) { x[i] } ; f(1:3,0-3) ; f(1:5,c(0,0,0,0-2))
#f<-function(x, i) { x[i] } ; f(1:3,0L-3L) ; f(1:5,c(0,0,0,0-2))
#x<-1:5 ; x[c(TRUE,FALSE)]
# x<-1:5 ; x[c(TRUE,TRUE,TRUE,NA)]
# x<-1:5 ; x[c(TRUE,TRUE,TRUE,FALSE,FALSE,FALSE,FALSE,TRUE,NA)]
# f<-function(i) { x<-1:5 ; x[i] } ; f(1) ; f(1L) ; f(TRUE)
# f<-function(i) { x<-1:5 ; x[i] } ; f(1) ; f(TRUE) ; f(1L)
# f<-function(i) { x<-1:5 ; x[i] } ; f(1) ; f(TRUE) ; f(c(3,2))
f<-function(i) { x<-1:5 ; x[i] } ; f(1)  ; f(3:4)
#f<-function(i) { x<-1:5 ; x[i] } ; f(c(TRUE,FALSE))  ; f(3:4)
