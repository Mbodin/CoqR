argv <- structure(list(test = c(TRUE, TRUE, FALSE, TRUE, FALSE),     yes = 'True', no = 'False'), .Names = c('test', 'yes', 'no'));do.call('ifelse', argv)
{ ifelse(TRUE,1,0) }
{ ifelse(FALSE,1,0) }
{ ifelse(NA,1,0) }
