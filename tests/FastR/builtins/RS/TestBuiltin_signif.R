argv <- list(structure(c(0, NaN, 0, 4.94065645841247e-324), class = 'integer64'));do.call('signif', argv)
{ signif(8.175, 3) }
{ signif(8.125, 3) }
{ signif(0.555, 2) }
{ signif(0.5549, 2) }
{ signif(0.5551, 2) }
{ signif(0.555, 0) }
{ signif(0.555, -1) }
{ signif(0.0005551, 2) }
{ signif(42.1234, "2") }
{ signif(42.1234, as.raw(2)) }
{ signif(42.1234, 42+7i) }
{ signif(42.1234, character()) }
{ signif("42.1234", 2) }
{ signif(c(42.1234, 7.1234), 1:2) }
{ signif(42.1234, 1:2) }
{ signif(c(42.1234, 7.1234), 1) }
{ signif(c(42.1234, 7.1234, 42.1234), c(1,2)) }
{ x<-42.1234; attr(x, "foo")<-"foo"; signif(x, 2) }
{ x<-FALSE; attr(x, "foo")<-"foo"; signif(x, 2) }
{ signif(42.1234, matrix(1:2, nrow=1)) }
