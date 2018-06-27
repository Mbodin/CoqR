argv <- list(0.7800058115849);do.call('log', argv)
{ log(1) } 
{ log(0) }
{ log(c(0,1)) }
{ round( log(10,), digits = 5 ) }
{ round( log(10,2), digits = 5 ) }
{ round( log(10,10), digits = 5 ) }
{ log(c(2,3), NA) } 
{ log(c(2,3), 0/0) } 
{ log(NaN) }
{ log(NA) }
{ log(1, NaN) }
{ log(1, NA) }
{ log(NaN, NaN) }
{ log(NA, NA) }
{ log(T) }
{ log(c(T)) }
{ log(c(T, F)) }
{ log(c(T, F), T) }
{ log(T, T) }
{ log(T, F) }
{ log(F, F) }
{ log(F, T) }
{ log(c(T, T), NA) }
{ log(c(T, T), NaN) }
{ log(1L) }
{ log(-1L) }
{ log(0L) }
{ log(NA_integer_) }
{ log(0L, NA_integer_) }
{ log(c(0L, NA_integer_)) }
{ log(1L, 1L) }
{ log(10L, 1L) }
{ log(10L, -1L) }
{ log(10L, 10L) }
{ log(c(1L, 1L, 0L, 10L), 10L) }
{ log(c(1L, 0L, 10L), 1L) }
{ log(c(1L, 2L), NA) }
{ log(c(1L, 2L), NaN) }
{ log(c(1L, 2L, NA)) }
{ log(1.1) }
{ log(-1.1) }
{ log(0.0) }
{ log(NA_real_) }
{ log(10, NA_real_) }
{ log(c(10, NA_real_)) }
{ log(1.0, 1.0) }
{ log(10.0, 1.0) }
{ log(10.0, -1.0) }
{ log(10.0, 10.0) }
{ log(c(1.0, 0.0, 10.0), 10.0) }
{ log(c(1.0, 0.0, 10.0), 1.0) }
{ log(c(1.0, 2.0), NA) }
{ log(c(1.0, 2.0), NaN) }
{ log(c(1.0, 2.0, NA)) }
{ log(0+0i) }
{ log(0+0i, 0) }
{ log(0L, 0+0i) }
{ log(0.0, 0+0i) }
{ log(F, 0+0i) }
{ log(0+0i, 0+0i) }
{ log(0+0i, 1) }
{ log(1+1i) }
{ log(complex(real=NA, imaginary=1i)) }
{ log(complex(real=1, imaginary=NA)) }
{ log(complex(real=NA, imaginary=NA)) }
{ log(NA_complex_) }
{ log(1+1i, NA_complex_) }
{ log(c(1+1i, NA_complex_)) }
{ log(1+1i, 0) }
{ log(1+1i, 1) }
{ log(10+1i, 10) }
{ log(10-1i, 10) }
{ log(-10-1i, 10) }
{ log(10+1i, -10) }
{ log(10+10i, 10) }
{ log(c(1+1i)) }
{ log(c(1+1i), 0) }
{ log(c(1+1i, 2+2i), NA) }
{ log(c(1+1i, 2+2i), NaN) }
{ log(c(1+1i, 2+2i), complex(real=1, imaginary=NaN)) }
{ log(c(1+1i, 2+2i), complex(real=NaN, imaginary=1)) }
{ log(c(1+1i, 2+2i), complex(real=NaN, imaginary=NaN)) }
{ log(c(1+1i, 2+2i), complex(real=1, imaginary=NA)) }
{ log(c(1+1i, 2+2i), complex(real=NA, imaginary=1)) }
{ log(c(1+1i, 2+2i, complex(real=NA, imaginary=NA))) }
{ log(c(10+1i, 10), 10) }
{ log(c(10+10i, 10), 10) }
{ log(c(1+1i, 2+1i)) }
{ log(c(10, 10+10i), 10) }
{ log(c(10.0, 10+10i), 10) }
{ log(c(T, 10+10i), 10) }
{ log(1, 1+1i) }
{ log(10, 10+10i) }
{ log(1.0, 1+1i) }
{ log(10.0, 1+1i) }
{ log(T, 1+1i) }
{ log(1+1i, 1+1i) }
{ log(1+1i, 1-1i) }
{ log(1+1i, -1-1i) }
{ log(10+10i, 10+10i) }
{ log(1+1i, 10+10i) }
{ log(c(10, 10), 10+10i) }
{ log(c(10.0, 10.0), 10+10i) }
{ log(c(T, F), 1+1i) }
{ log(c(10+10i, 10+10i), 10+10i) }
{ log(complex(real=sqrt(.5), imaginary=sqrt(.5)), 1) }
{ log(c(F, F), F) }
{ log(c(1L, 1L), 1L) }
{ log(c(1.0, 1.0), 1.0) }
{ log(c(0+0i, 0+0i), 0) }
{ log(c(F, F), 0+0i) }
{ log(c(0L, 0L), 0+0i) }
{ log(c(0.0, 0.0), 0+0i) }
{ log(c(0+0i, 0+0i), 0+0i) }
{ x <- array(1:3, 1); dimnames(x) <- list('a'); r <- log(x); names(r)[[1]] <- 'new'; list(x=x, r=r); }
{ x <- array(1:3, 3, list(x=c('x1','x2','x3'))); r <- log(x); r; }
{ y <- array(1:6, c(2,3), list(y=c('y1','y2'), x=c('x1','x2','x3'))); r <- log(y); r; }
