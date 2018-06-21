{y<-function(){y<-2;get("y",mode="integer")};y();}
{y<-function(){y<-2;get("y",mode="closure")};y();}
{y<-function(){y<-2;get("y",mode="integer",inherits=FALSE);get("y",mode="integer",inherits=FALSE)};y();}
{y<-function(){y<-2;get("y",mode="double")};y();}
{y<-function(){y<-2;get("y",mode="double",inherits=FALSE)};y();}
{ get("dummy") }
{ x <- 33 ; f <- function() { if (FALSE) { x <- 22  } ; get("x", inherits = FALSE) } ; f() }
{ x <- 33 ; f <- function() { get("x", inherits = FALSE) } ; f() }
{ get(".Platform", globalenv())$endian }
{ get(".Platform")$endian }
{y<-function(){y<-2;get("y",mode="closure",inherits=FALSE);};y();}
setClass('foo', representation(x='numeric')); f <- new('foo'); e <- new.env(); e$x <- 1; attr(f, '.xData') <- e; get('x', envir=f)
setClass('foo', representation(x='numeric')); f <- new('foo'); e <- new.env(); e$x <- 1; attr(f, '.Data') <- e; get('x', envir=f)
{x <- 1L; get('x', mode='numeric'); }
{x <- 1L; get('x', mode='double'); }
