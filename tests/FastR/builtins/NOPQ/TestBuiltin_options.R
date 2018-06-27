argv <- list('survfit.print.n'); .Internal(options(argv[[1]]))
argv <- list('contrasts'); .Internal(options(argv[[1]]))
argv <- list('str'); .Internal(options(argv[[1]]))
argv <- list('ts.eps'); .Internal(options(argv[[1]]))
options(list(NULL));
options(NA);
options(NULL);
argv <- list(NULL); .Internal(options(argv[[1]]))
{ getOption(NULL) }
{ getOption(character()) }
{ options("timeout", "width") }
{ options(options(digits = 5)) }
{ options(list(aaa = 42, bbb = 'hello')); x <- options('aaa', 'bbb'); options(aaa=NULL, bbb=NULL); x }
{ options(lll = list(aaa = 42, bbb = 'hello')); x <- options('lll', 'aaa', 'bbb'); options(aaa=NULL, bbb=NULL, lll=NULL); x }
{ f<-function(){}; options(editor=f); identical(getOption("editor"), f) }
{ options(editor="vi"); identical(getOption("editor"), "vi") }
{ options(editor=NULL); identical(getOption("editor"), NULL) }
{ options(editor="") }
{ options(prompt=NULL) }
{ options(prompt="abc"); identical(getOption("prompt"), "abc") }
{ options(continue=NULL) }
{ options(continue="abc"); identical(getOption("continue"), "abc") }
