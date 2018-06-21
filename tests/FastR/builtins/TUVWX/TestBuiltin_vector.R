argv <- list('integer', 0L); .Internal(vector(argv[[1]], argv[[2]]))
argv <- list('double', 17.1); .Internal(vector(argv[[1]], argv[[2]]))
argv <- list('list', 1L); .Internal(vector(argv[[1]], argv[[2]]))
argv <- list('logical', 15L); .Internal(vector(argv[[1]], argv[[2]]))
argv <- list('double', 2); .Internal(vector(argv[[1]], argv[[2]]))
argv <- list('raw', 0L); .Internal(vector(argv[[1]], argv[[2]]))
argv <- list('list', structure(1L, .Names = 'c')); .Internal(vector(argv[[1]], argv[[2]]))
argv <- structure(list(mode = 'complex', length = 7), .Names = c('mode',     'length'));do.call('vector', argv)
{ vector() }
{ vector("integer") }
{ vector("numeric") }
{ vector("numeric", length=4) }
{ vector(length=3) }
{ x<-as.vector(3); y<-vector(length=x) }
{ vector(character()) }
{ vector(c("numeric", "numeric")) }
{  vector("numeric", integer()) }
{  vector("numeric", c(7, 42)) }
vector('pairlist', 0)
vector('pairlist', 3)
v <- as.integer(c(1, 2)); v[1]<-NA_integer_; v
v <- c(1, 2); v[1]<-NA_real_; v
v <- c('a', 'b'); v[1]<-NA_character_; v
v <- c(1, 2); v[1]<-NA_integer_; v
v <- as.integer(c(1, 2, 3, 4)); dim(v)<-c(2,2); v[1, 1]<-NA_integer_; v
v <- c(1, 2, 3, 4); dim(v)<-c(2,2); v[1, 1]<-NA_real_; v
v <- c('a', 'b', 'c', 'd'); dim(v)<-c(2,2); v[1, 1]<-NA_character_; v
v <- c(1, 2, 3, 4); dim(v)<-c(2,2); v[1, 1]<-NA_integer_; v
