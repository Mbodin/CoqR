argv <- list(0L, 0L, FALSE, NULL); .Internal(sample(argv[[1]], argv[[2]], argv[[3]], argv[[4]]))
argv <- list(1L, 1L, FALSE, NULL); .Internal(sample(argv[[1]], argv[[2]], argv[[3]], argv[[4]]))
argv <- list(2L, 499, TRUE, c(0, 0.525)); .Internal(sample(argv[[1]], argv[[2]], argv[[3]], argv[[4]]))
argv <- structure(list(x = c(0, 0)), .Names = 'x');do.call('sample', argv)
{  set.seed(4357, "default"); x <- 5 ; sample(x, 5, TRUE, NULL) ;}
{  set.seed(4357, "default"); x <- 5 ; sample(x, 5, FALSE, NULL) ;}
{ set.seed(4357, "default");  x <- c(5, "cat"); sample(x, 2, TRUE, NULL) ;}
{ set.seed(4357, "default"); x <- c(5, "cat"); sample(x, 2, FALSE, NULL) ;}
{ set.seed(4357, "default"); x <- c(5, "cat"); sample(x, 3, TRUE, NULL) ;}
{ set.seed(9567, "Marsaglia-Multicarry"); x <- 5; sample(x, 5, TRUE, NULL) ;}
{ set.seed(9567, "Marsaglia-Multicarry"); x <- 5; sample(x, 5, FALSE, NULL) ;}
{ set.seed(9567, "Marsaglia-Multicarry"); x <- c(5, "cat") ; sample(x, 2, TRUE, NULL) ;}
{ set.seed(9567, "Marsaglia-Multicarry"); x <- c(5, "cat") ; sample(x, 2, FALSE, NULL) ;}
{ set.seed(9567, "Marsaglia-Multicarry"); x <- c(5, "cat") ; sample(x, 3, TRUE, NULL) ;}
{ set.seed(9567, "Marsaglia-Multicarry"); x <- 5 ; prob <- c(.1, .2, .3, .2, .1) ; sample(x, 10, TRUE, prob) ; }
{ set.seed(9567, "Marsaglia-Multicarry"); x <- 5 ; prob <- c(.5, .5, .5, .5, .5) ; sample(x, 5, FALSE, prob) ; }
{ set.seed(9567, "Marsaglia-Multicarry"); x <- 5 ; prob <- c(.2, .2, .2, .2, .2 ) ; sample(x, 5, FALSE, prob) ; }
{ set.seed(4357, "default"); x <- c("Heads", "Tails"); prob <- c(.3, .7) ; sample(x, 10, TRUE, prob) ; }
{ set.seed(4357, "default"); x <- 5 ; prob <- c(.1, .2, .3, .2, .1); sample(x, 10, TRUE, prob) ; }
{ set.seed(4357, "default"); x <- 5 ; prob <- c(.5, .5, .5, .5, .5); sample(x, 5, FALSE, prob) ; }
{ set.seed(4357, "default"); x <- 5 ; prob <- c(.2, .2, .2, .2, .2 ); sample(x, 5, FALSE, prob) ; }
{ set.seed(9567, "Marsaglia-Multicarry");x <- c("Heads", "Tails") ; prob <- c(.3, .7) ; sample(x, 10, TRUE, prob) ; }
{ set.seed(9567, "Marsaglia-Multicarry");x <- c(5) ; prob <- c(1, 2, 3, 4, 5) ; sample(x, 5, TRUE, prob) ; }
{ set.seed(9567, "Marsaglia-Multicarry");x <- c(5) ; prob <- c(1, 2, 3, 4, 5) ; sample(x, 5, FALSE, prob) ; }
{ set.seed(4357, "default"); x <- c(5) ; prob <- c(1, 2, 3, 4, 5) ; sample(x, 5, TRUE, prob) ; }
{ set.seed(4357, "default"); x <- c(5) ; prob <- c(1, 2, 3, 4, 5) ; sample(x, 5, FALSE, prob) ; }
{ set.seed(4357, "default"); x <- 5 ; sample(x, 6, FALSE, NULL) ;}
{ set.seed(9567, "Marsaglia-Multicarry"); x <- 5 ; sample(x, 6, FALSE, NULL) ;}
set.seed(42); sample(-1)
set.seed(42); .Internal(sample(4.5e20, 4.5e20, FALSE, NULL))
set.seed(42); .Internal(sample(NA, NA, FALSE, NULL))
set.seed(42); .Internal(sample(NaN, NaN, FALSE, NULL))
set.seed(42); .Internal(sample(NULL, NULL, F, NULL))
set.seed(42); .Internal(sample(NULL, NULL, F, seq(1.2,3)))
set.seed(42); .Internal(sample(5,6,T,))
set.seed(42); .Internal(sample(5,6,T,NULL))
set.seed(42); .Internal(sample(5,6,T,seq(1.2,3)))
set.seed(42); .Internal(sample(1/0, 1, FALSE, NULL))
set.seed(42); sample(3, '2')
set.seed(42); sample(3, 2.0)
set.seed(42); sample(3, c(2,3))
set.seed(42); sample(3, TRUE)
set.seed(42); sample(3, -3)
set.seed(42); sample(3, NA)
set.seed(42); sample(2, 0)
set.seed(42); sample(0, 0)
set.seed(42); sample(4, replace=c(T,F))
set.seed(42); sample(4, replace=1)
set.seed(42); sample(4, replace=1.2)
set.seed(42); sample(4, replace='s')
set.seed(42); sample(4, prob=c(1,2))
set.seed(42); sample(4, prob=c(-1,1,1,2))
