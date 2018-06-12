# @line
# do_for tests

for(1 in 1:10) 1
for("x" in  1:10) 1

f<-function() { x<-1 ; for(i in 1:10) { x<-x+1 } ; x } ; f(); f()
f<-function(r) { x<-0 ; for(i in r) { x<-x+i } ; x } ; f(c(1,2,3,4,5)) ; f(1:10)
f<-function(r) { x<-0 ; for(i in r) { x<-x+i } ; x } ; f(1:10) ; f(c(1,2,3,4,5))
f<-function(i) { if (i<=1) {1} else {r<-i; for(j in 2:(i-1)) {r=r*j}; r} }; f(10)
x<-1 ; for(i in 1:10) { x<-x+1 } ; x
