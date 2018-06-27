argv <- list('.', 'myTst_.*tar.gz$', FALSE, FALSE, FALSE, FALSE, FALSE, FALSE); .Internal(list.files(argv[[1]], argv[[2]], argv[[3]], argv[[4]], argv[[5]], argv[[6]], argv[[7]], argv[[8]]))
argv <- list('./myTst/data', NULL, FALSE, FALSE, FALSE, FALSE, FALSE, FALSE); .Internal(list.files(argv[[1]], argv[[2]], argv[[3]], argv[[4]], argv[[5]], argv[[6]], argv[[7]], argv[[8]]))
print('Work dir: ', getwd()); argv <- list('.', '^CITATION.*', FALSE, FALSE, TRUE, FALSE, FALSE, FALSE); sort(.Internal(list.files(argv[[1]], argv[[2]], argv[[3]], argv[[4]], argv[[5]], argv[[6]], argv[[7]], argv[[8]])))
argv <- list('mgcv', NULL, FALSE, FALSE, FALSE, FALSE, FALSE, FALSE); .Internal(list.files(argv[[1]], argv[[2]], argv[[3]], argv[[4]], argv[[5]], argv[[6]], argv[[7]], argv[[8]]))
{ list.files("test/r/simple/data/tree1") }
{ list.files("test/r/simple/data/tree1", recursive=TRUE) }
{ list.files("test/r/simple/data/tree1", recursive=TRUE, pattern=".*dummy.*") }
{ list.files("test/r/simple/data/tree1", recursive=TRUE, pattern="dummy") }
{ list.files("test/r/simple/data/tree1", pattern=".*.tx") }
