x <- matrix(c(1,1,1,1,2,3), 3, 2); dimnames(x) <- list(c(1,2,3),c('','x')); coeff <- c(0,1); names(coeff) <- c('a', 'b'); x %*% coeff; 
m1 <- matrix(1:6,3,2,dimnames=list(c('a','b','c'),c('c1','c2')));m2 <- matrix(c(3,4),2,1,dimnames=list(c('a2','b2'),c('col'))); m1 %*% m2; 
vec <- c(1,2); names(vec) <- c('a','b'); mat <- matrix(c(8,3),1,2,dimnames=list('row',c('c1','c2'))); vec %*% mat; 
