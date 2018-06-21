argv <- list('./myTst2/man/DocLink-class.Rd');nzchar(argv[[1]]);
argv <- list(FALSE);nzchar(argv[[1]]);
argv <- list(c('a', 'b', 'c'));nzchar(argv[[1]]);
argv <- list(structure('MASS', .Names = ''));nzchar(argv[[1]]);
argv <- list(NULL);nzchar(argv[[1]]);
argv <- list(c('Fr', 'Temp', 'Soft', 'M.user', 'Brand'));nzchar(argv[[1]]);
argv <- list(structure('survival', .Names = ''));nzchar(argv[[1]]);
argv <- list(structure(3.14159265358979, class = structure('3.14159265358979', class = 'testit')));nzchar(argv[[1]]);
argv <- list(c('  036 The other major change was an error for asymmetric loss matrices,', '    prompted by a user query.  With L=loss asymmetric, the altered', '    priors were computed incorrectly - they were using L' instead of L.', '    Upshot - the tree would not not necessarily choose optimal splits', '    for the given loss matrix.  Once chosen, splits were evaluated', '    correctly.  The printed “improvement” values are of course the', '    wrong ones as well.  It is interesting that for my little test', '    case, with L quite asymmetric, the early splits in the tree are', '    unchanged - a good split still looks good.'));nzchar(argv[[1]]);
argv <- list(logical(0));nzchar(argv[[1]]);
argv <- list('');do.call('nzchar', argv)
nzchar(c('asdasd', NA), keepNA=TRUE)
nzchar(c('asdasd', NA), keepNA=FALSE)
nzchar(c('aasd', NA), keepNA=NA)
nzchar(list('x', 42, list('a'), list()))
nzchar(NULL)
nzchar(NA)
nzchar(keepNA=F)
nzchar(keepNA=NA)
nchar(wrongArgName="a")
nchar(wrongArgName='a')
