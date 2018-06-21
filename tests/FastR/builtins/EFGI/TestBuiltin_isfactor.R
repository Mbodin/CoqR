argv <- structure(list(x = c(TRUE, TRUE, TRUE, TRUE, FALSE, FALSE,     FALSE, FALSE, FALSE, FALSE, TRUE, TRUE, TRUE, TRUE, FALSE,     FALSE, FALSE, FALSE, FALSE, FALSE)), .Names = 'x');do.call('is.factor', argv)

{x<-1;class(x)<-"foo";is.factor(x)}
{is.factor(1)}
{is.factor(c)}
{x<-1;class(x)<-"factor";is.factor(x)}
