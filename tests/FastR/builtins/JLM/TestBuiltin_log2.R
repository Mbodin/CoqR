argv <- list(48L);log2(argv[[1]]);
argv <- list(FALSE);log2(argv[[1]]);
argv <- list(2.2250738585072e-308);log2(argv[[1]]);
argv <- list(2.2250738585072e-308);do.call('log2', argv)
{ log2(1) } 
{ log2(0) }
{ log2(c(0,1)) }
{ log2(2) } 
{ log2(4) } 
{ as.integer(log2(6)*1000000) } 
{ log2(c(1+1i, -1-1i)) }
{ log2(NaN) }
{ log2(NA) }
