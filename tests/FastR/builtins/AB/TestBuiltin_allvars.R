argv <- structure(list(expr = expression(quote(temp[1, ] ~ 3))),     .Names = 'expr');do.call('all.vars', argv)
{ fml <- as.formula('v ~ a + b'); fml[[2]] <- NULL; all.vars(fml) }
