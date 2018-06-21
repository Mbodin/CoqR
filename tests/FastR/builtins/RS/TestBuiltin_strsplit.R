argv <- list('exNSS4', '_', TRUE, FALSE, FALSE); .Internal(strsplit(argv[[1]], argv[[2]], argv[[3]], argv[[4]], argv[[5]]))
argv <- list(structure('x, row.names = NULL, ', Rd_tag = 'RCODE'), '', FALSE, FALSE, FALSE); .Internal(strsplit(argv[[1]], argv[[2]], argv[[3]], argv[[4]], argv[[5]]))
argv <- list('  036  isSeekable() now returns FALSE on connections       which have non-default encoding.  Although documented to       record if ‘in principle’ the connection supports seeking,       it seems safer to report FALSE when it may not work.', '[ tn]', FALSE, TRUE, FALSE); .Internal(strsplit(argv[[1]], argv[[2]], argv[[3]], argv[[4]], argv[[5]]))
argv <- list('Keywords:  device ', '[ tn]', FALSE, TRUE, TRUE); .Internal(strsplit(argv[[1]], argv[[2]], argv[[3]], argv[[4]], argv[[5]]))
argv <- list('R CMD check now gives an error if the R code in a vignette fails tonrun, unless this is caused by a missing package.nn036R CMD check now unpacks tarballs in the same way as R CMD INSTALL,nincluding making use of the environment variable R_INSTALL_TAR tonoverride the default behaviour.nn036R CMD check performs additional code analysis of package startupnfunctions, and notifies about incorrect argument lists andn(incorrect) calls to functions which modify the search path orninappropriately generate messages.nn036R CMD check now also checks compiled code for symbols correspondingnto functions which might terminate R or write to stdout/stderrninstead of the console.nn036R CMD check now uses a pdf() device when checking examples (rathernthan postscript()).nn036R CMD check now checks line-endings of makefiles and C/C++/Fortrannsources in subdirectories of src as well as in src itself.nn036R CMD check now reports as a NOTE what look like methods documentednwith their full names even if there is a namespace and they arenexported.  In almost all cases they are intended to be used only asnmethods and should use the method markup.  In the other rare casesnthe recommended form is to use a function such as coefHclust whichnwould not get confused with a method, document that and register itnin the NAMESPACE file by s3method(coef, hclust, coefHclust).nn036The default for the environment variable _R_CHECK_COMPACT_DATA2_ isnnow true: thus if using the newer forms of compression introducednin R 2.10.0 would be beneficial is now checked (by default).nn036Reference output for a vignette can be supplied when checking anpackage by R CMD check: see ‘Writing R Extensions’.nn036R CMD Rd2dvi allows the use of LaTeX package inputenx rather thanninputenc: the value of the environment variable RD2DVI_INPUTENC isnused.  (LaTeX package inputenx is an optional install whichnprovides greater coverage of the UTF-8 encoding.)nn036Rscript on a Unix-alike now accepts file names containing spacesn(provided these are escaped or quoted in the shell).nn036R CMD build on a Unix-alike (only) now tries to preserve dates onnfiles it copies from its input directory.  (This was thenundocumented behaviour prior to R 2.13.0.)', 'n036', TRUE, FALSE, FALSE); .Internal(strsplit(argv[[1]], argv[[2]], argv[[3]], argv[[4]], argv[[5]]))
argv <- list(structure('Formal Methods and Classes', .Names = 'Title'), 'nn', TRUE, FALSE, TRUE); .Internal(strsplit(argv[[1]], argv[[2]], argv[[3]], argv[[4]], argv[[5]]))
argv <- list('', '', FALSE, FALSE, FALSE); .Internal(strsplit(argv[[1]], argv[[2]], argv[[3]], argv[[4]], argv[[5]]))
argv <- list('The usage entries for S3 methods should use the method markup and not their full name.n', 'n', FALSE, FALSE, TRUE); .Internal(strsplit(argv[[1]], argv[[2]], argv[[3]], argv[[4]], argv[[5]]))
argv <- list('M.user:Temp', ':', FALSE, FALSE, FALSE); .Internal(strsplit(argv[[1]], argv[[2]], argv[[3]], argv[[4]], argv[[5]]))
argv <- list('A shell of class documentation has been written to the file './myTst2/man/DocLink-class.Rd'.n', '[ tn]', FALSE, TRUE, TRUE); .Internal(strsplit(argv[[1]], argv[[2]], argv[[3]], argv[[4]], argv[[5]]))
argv <- list(structure('pkgB', .Names = 'name'), '_', TRUE, FALSE, FALSE); .Internal(strsplit(argv[[1]], argv[[2]], argv[[3]], argv[[4]], argv[[5]]))
argv <- list('Keywords:  utilities ', 'n[ tn]*n', FALSE, TRUE, TRUE); .Internal(strsplit(argv[[1]], argv[[2]], argv[[3]], argv[[4]], argv[[5]]))
argv <- list('x', '', FALSE, FALSE, FALSE); .Internal(strsplit(argv[[1]], argv[[2]], argv[[3]], argv[[4]], argv[[5]]))
argv <- list(c('* Edit the help file skeletons in 'man', possibly combining help files for multiple functions.', '* Edit the exports in 'NAMESPACE', and add necessary imports.', '* Put any C/C++/Fortran code in 'src'.', '* If you have compiled code, add a useDynLib() directive to 'NAMESPACE'.', '* Run R CMD build to build the package tarball.', '* Run R CMD check to check the package tarball.', '', 'Read 'Writing R Extensions' for more information.'), 'n[ tn]*n', FALSE, TRUE, TRUE); .Internal(strsplit(argv[[1]], argv[[2]], argv[[3]], argv[[4]], argv[[5]]))
argv <- list('  036  Complex arithmetic sometimes warned incorrectly about       producing NAs when there were NaNs in the input.', '[ tn]', FALSE, TRUE, TRUE); .Internal(strsplit(argv[[1]], argv[[2]], argv[[3]], argv[[4]], argv[[5]]))
argv <- list(structure(c('1', '2', '3', '4', '5', '1', '2', '3', '4', '5'), .Dim = 10L), '.', TRUE, FALSE, FALSE); .Internal(strsplit(argv[[1]], argv[[2]], argv[[3]], argv[[4]], argv[[5]]))
{ strsplit("helloh", "h", fixed=TRUE) }
{ strsplit( c("helloh", "hi"), c("h",""), fixed=TRUE) }
{ strsplit("helloh", "", fixed=TRUE) }
{ strsplit("helloh", "h") }
{ strsplit( c("helloh", "hi"), c("h","")) }
{ strsplit("ahoj", split="") [[c(1,2)]] }
{ strsplit("a,h,o,j", split=",") }
{ strsplit("abc", ".", fixed = TRUE, perl=FALSE) }
{ strsplit("abc", ".", fixed = TRUE, perl=TRUE) }
{ strsplit("abc", ".", fixed = FALSE, perl=FALSE) }
{ strsplit("abc", ".", fixed = FALSE, perl=TRUE) }
{ .Internal(strsplit(7, "42", F, F, F)) }
{ .Internal(strsplit("7", 42, F, F, F)) }
strsplit('foo bar baz', '[f z]', perl=TRUE)
strsplit('oo bar baz', '[f z]', perl=TRUE)
strsplit('foo u1010ÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄbar baz ', '[f z]', perl=TRUE)
strsplit('Ä Ä', '[ ]', perl=TRUE)
strsplit('1', '1', fixed=TRUE)
strsplit('11', '11', fixed=TRUE)
strsplit(c('1', '11'), c('1', '11'), fixed=TRUE)
strsplit('Ä', 'Ä', fixed=TRUE)
strsplit('ÄÄ', 'Ä', fixed=TRUE)
strsplit('1', '1', fixed=FALSE)
strsplit('11', '11', fixed=FALSE)
strsplit(c('1', '11'), c('1', '11'), fixed=FALSE)
strsplit('Ä', 'Ä', fixed=FALSE)
strsplit('ÄÄ', 'Ä', fixed=FALSE)
strsplit(c('111', '1'), c('111', '1'), fixed=TRUE)
strsplit(c('1', ''), c('1', ''), fixed=TRUE)
strsplit(c('1', 'b'), c('1', 'b'), fixed=TRUE)
strsplit(c('a1a', 'a1b'), c('1', '1'), fixed=TRUE)
strsplit(c('a1a', 'a1b'), '1', fixed=TRUE)
strsplit(c('111', '1'), c('111', '1'), fixed=FALSE)
strsplit(c('1', ''), c('1', ''), fixed=FALSE)
strsplit(c('1', 'b'), c('1', 'b'), fixed=FALSE)
strsplit(c('a1a', 'a1b'), c('1', '1'), fixed=FALSE)
strsplit(c('a1a', 'a1b'), '1', fixed=FALSE)
strsplit(c('','a , b'), '[[:space:]]*,[[:space:]]*')
