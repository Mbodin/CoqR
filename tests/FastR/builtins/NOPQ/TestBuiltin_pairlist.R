argv <- list();do.call('pairlist', argv)
{ x<-7; y<-c(foo=42); z<-pairlist(x, y); list(z, typeof(z)) }
