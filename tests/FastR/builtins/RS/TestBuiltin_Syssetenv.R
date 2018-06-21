argv <- list('_R_NS_LOAD_', 'Matrix'); .Internal(Sys.setenv(argv[[1]], argv[[2]]))
argv <- list('_R_NS_LOAD_', 'methods'); .Internal(Sys.setenv(argv[[1]], argv[[2]]))
argv <- list(c('BIBINPUTS', 'add'), c('.:.:/home/lzhao/hg/r-instrumented/share/texmf/bibtex/bib::/home/lzhao/hg/r-instrumented/share/texmf/bibtex/bib:', 'TRUE')); .Internal(Sys.setenv(argv[[1]], argv[[2]]))
argv <- structure(list(TZ = 'EST5EDT'), .Names = 'TZ');do.call('Sys.setenv', argv)
