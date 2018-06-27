argv <- list('head', TRUE); .Internal(make.names(argv[[1]], argv[[2]]))
argv <- list('FALSE', TRUE); .Internal(make.names(argv[[1]], argv[[2]]))
argv <- list(c('.Call', '.Call numParameters', '.Fortran', '.Fortran numParameters'), TRUE); .Internal(make.names(argv[[1]], argv[[2]]))
argv <- list('..adfl.row.names', TRUE); .Internal(make.names(argv[[1]], argv[[2]]))
argv <- list(c('name', 'title', 'other.author'), TRUE); .Internal(make.names(argv[[1]], argv[[2]]))
argv <- list('.2a', TRUE); .Internal(make.names(argv[[1]], argv[[2]]))
argv <- list('', TRUE); .Internal(make.names(argv[[1]], argv[[2]]))
argv <- list(NA_character_, TRUE); .Internal(make.names(argv[[1]], argv[[2]]))
argv <- list(c('Subject', 'predict.fixed', 'predict.Subject'), TRUE); .Internal(make.names(argv[[1]], argv[[2]]))
argv <- list(c('', '', 'bady'), TRUE); .Internal(make.names(argv[[1]], argv[[2]]))
argv <- list(character(0), TRUE); .Internal(make.names(argv[[1]], argv[[2]]))
{ make.names(7) }
{ make.names("a_a") }
{ make.names("a a") }
{ make.names("a_a", allow_=FALSE) }
{ make.names("a_a", allow_=7) }
{ make.names("a_a", allow_=c(7,42)) }
{ make.names("...7") }
{ make.names("..7") }
{ make.names(".7") }
{ make.names("7") }
{ make.names("$") }
{ make.names("$_", allow_=FALSE) }
{ make.names("else")}
{ make.names("NA_integer_", allow_=FALSE) }
{ make.names("a_a", allow_="a") }
{ make.names("a_a", allow_=logical()) }
{ make.names("a_a", allow_=NULL) }
{ .Internal(make.names(42, F)) }
