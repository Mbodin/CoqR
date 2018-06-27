argv <- list('EDITOR', ''); .Internal(Sys.getenv(argv[[1]], argv[[2]]))
argv <- list('SWEAVE_OPTIONS', NA_character_); .Internal(Sys.getenv(argv[[1]], argv[[2]]))
{ Sys.setenv("a") } 
{ Sys.setenv(FASTR_A="a"); Sys.getenv("FASTR_A"); } 
{ Sys.setenv(FASTR_A="a", FASTR_B="b"); Sys.getenv(c("FASTR_A", "FASTR_B"));  } 
{ Sys.getenv("FASTR_A") } 
{ Sys.getenv("FASTR_A", unset="UNSET") } 
